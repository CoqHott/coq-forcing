open Names
open Term
open Environ
open Globnames
open Pp

type translator = global_reference Refmap.t
exception MissingGlobal of global_reference

let rel_name = function
| Anonymous -> Anonymous
| Name id ->
  let id = Id.to_string id in
  let id_ = Id.of_string (id ^ "ᴿ") in
  Name id_

(** Yoneda embedding *)

type category = {
  cat_obj : Constr.t;
  (** Objects. Must be of type [Type]. *)
  cat_hom : Constr.t;
  (** Morphisms. Must be of type [cat_obj -> cat_obj -> Type]. *)
}

let obj_name = Name (Id.of_string "R")
let knt_name = Name (Id.of_string "k")

let hom cat a b =
  let lft = mkApp (cat.cat_hom, [| Vars.lift 1 b; mkRel 1 |]) in
  let rgt = mkApp (cat.cat_hom, [| Vars.lift 2 a; mkRel 2 |]) in
  let arr = mkArrow lft rgt in
  mkProd (obj_name, cat.cat_obj, arr)

let hom_type cat =
  mkLambda (obj_name, cat.cat_obj,
    mkLambda (obj_name, cat.cat_obj, hom cat (mkRel 2) (mkRel 1)))

let refl cat a =
  let hom = mkApp (cat.cat_hom, [| Vars.lift 1 a; mkRel 1 |]) in
  let lam = mkLambda (knt_name, hom, mkRel 1) in
  mkLambda (obj_name, cat.cat_obj, lam)

let trns cat a b c f g =
  let hom = mkApp (cat.cat_hom, [| Vars.lift 1 c; mkRel 1 |]) in
  let app = mkApp (Vars.lift 2 g, [| mkRel 2; mkRel 1 |]) in
  let app' = mkApp (Vars.lift 2 f, [| mkRel 2; app |]) in
  let lam = mkLambda (knt_name, hom, app') in
  mkLambda (obj_name, cat.cat_obj, lam)

(** Translation of types *)

let forcing_module =
  let dp = List.map Id.of_string ["Forcing"; "Forcing"] in
  ModPath.MPfile (DirPath.make dp)

let cType = (MutInd.make2 forcing_module (Label.make "Typeᶠ"), 0)
let ctype = (cType, 1)
let cmono = (cType, 2)
let ptype = Projection.make (Constant.make2 forcing_module (Label.make "type")) false
let pmono = Projection.make (Constant.make2 forcing_module (Label.make "mono")) false
let fcast = Constant.make3 forcing_module DirPath.empty (Label.make "cast")
let frealizes = Constant.make3 forcing_module DirPath.empty (Label.make "realizes")
let ftypemon = Constant.make3 forcing_module DirPath.empty (Label.make "Typeᶿ")

(** Optimization of cuts *)

let mkOptApp (t, args) =
  let len = Array.length args in
  try
    let (_, t) = Term.decompose_lam_n len t in
    Vars.substl (CArray.rev_to_list args) t
  with _ ->
    mkApp (t, args)

let mkOptProj c = match kind_of_term c with
| App (i, args) ->
  if Array.length args = 5 && Term.isConstruct i then args.(3)
  else mkProj (ptype, c)
| _ ->
  mkProj (ptype, c)

let mkOptMono c = match kind_of_term c with
| App (i, args) ->
  if Array.length args = 5 && Term.isConstruct i then args.(4)
  else mkProj (pmono, c)
| _ ->
  mkProj (pmono, c)

(** Forcing translation *)

type forcing_condition =
| Variable
| Lift

type forcing_context = {
  context : forcing_condition list;
  (** Forcing contexts are flagging variables of the rel_context in the same
    order. We statically know that variables coming from the introduction of
    a forcing condition come by pairs: the first one is a level, the second one
    a morphism. There is therefore only [Lift] condition for such pairs. *)
  category : category;
  (** Underlying category *)
  translator : translator;
  (** A map associating to all source constant a forced constant *)
}

(** We assume that there is a hidden topmost variable [p : Obj] in the context *)

let pos_name = Name (Id.of_string "p")
let hom_name = Name (Id.of_string "α")

let dummy = mkProp

let last_condition fctx =
  let rec last fctx = match fctx with
  | [] -> 1
  | Variable :: fctx -> 2 + last fctx
  | Lift :: fctx -> 2
  in
  last fctx.context

let gather_morphisms n fctx =
  let rec gather i n fctx =
    if n = 0 then []
    else match fctx with
    | [] -> []
    | Variable :: fctx -> gather (i + 2) (n - 1) fctx
    | Lift :: fctx -> i :: gather (i + 2) n fctx
  in
  gather 1 n fctx.context

let morphism_var n fctx =
  let morphs = gather_morphisms n fctx in
  let last = mkRel (last_condition fctx) in
  let fold accu i =
    trns fctx.category dummy dummy last (mkRel i) accu
  in
  List.fold_left fold (refl fctx.category last) morphs

let get_var_shift n fctx =
  let rec get n fctx =
    if n = 0 then 0
    else match fctx with
    | [] -> n
    | Variable :: fctx -> 2 + get (n - 1) fctx
    | Lift :: fctx -> 2 + get n fctx
  in
  get n fctx.context

let extend fctx =
  let cat = fctx.category in
  let last = last_condition fctx in
  let ext = [(hom_name, None, hom cat (mkRel (1 + last)) (mkRel 1)); (pos_name, None, cat.cat_obj)] in
  (ext, { fctx with context = Lift :: fctx.context })

let add_variable fctx =
  { fctx with context = Variable :: fctx.context }

(** Monadic style *)

type 'a t = Environ.env -> forcing_context -> Evd.evar_map -> Evd.evar_map * 'a

let return (x : 'a) : 'a t = fun _ _ sigma -> (sigma, x)

let (>>=) (m : 'a t) (f : 'a -> 'b t) : 'b t = (); fun env fctx sigma ->
  let (sigma, x) = m env fctx sigma in
  f x env fctx sigma

let rec mmap (f : 'a -> 'b t) (l : 'a list) : 'b list t = match l with
| [] -> return []
| x :: l -> f x >>= fun x -> mmap f l >>= fun l -> return (x :: l)

type rec_f = {
  otranslate : constr -> constr t;
  rtranslate : constr -> constr t;
}

let in_extend f = fun env fctx sigma ->
  let (ext, fctx) = extend fctx in
  let env = Environ.push_rel_context ext env in
  f ext env fctx sigma

let get_category = (); fun env fctx sigma -> (sigma, fctx.category)

let fresh_inductive ind = (); fun env fctx sigma ->
  Evd.fresh_inductive_instance env sigma ind

let fresh_constant c = (); fun env fctx sigma ->
  Evd.fresh_constant_instance env sigma c

let fresh_universe = (); fun env fctx sigma ->
  let (sigma, s) = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  (sigma, mkSort s)

(** Macros *)

let liftn_named_decl n k (na, b, t) = (na, Option.map (fun c -> Vars.liftn n k c) b, Vars.liftn n k t)
let liftn_named_context n k ctx =
  let len = List.length ctx in
  List.mapi (fun i d -> liftn_named_decl n (k + len - i) d) ctx

(** Given an inhabitant of CType build a Type *)
let projfType c env fctx sigma =
  let c = mkOptProj c in
  let last = mkRel (last_condition fctx) in
  (sigma, mkOptApp (c, [| last; refl fctx.category last |]))

(** Inverse *)
let mkfType lam mon env fctx sigma =
  let (sigma, pc) = Evd.fresh_constructor_instance env sigma ctype in
  let (ext0, fctx0) = extend fctx in
  let self = it_mkProd_or_LetIn (mkOptApp (Vars.lift 2 lam, [| mkRel 2; mkRel 1 |])) ext0 in
  let mon = mkLambda (Anonymous, self, mon) in
  let tpe = mkApp (mkConstructU pc, [| fctx.category.cat_obj; fctx.category.cat_hom; mkRel (last_condition fctx); lam; mon |]) in
  (sigma, tpe)

let box t =
  in_extend begin fun ext ->
    t >>= fun t_ ->
    return (it_mkLambda_or_LetIn t_ ext)
  end

let box_type t =
  in_extend begin fun ext ->
    t >>= fun t_ ->
    projfType t_ >>= fun t_ ->
    return (it_mkProd_or_LetIn t_ ext)
  end

let rel_type t =
  t >>= fun t_ -> return (mkOptMono t_)

let translate_var n = fun env fctx sigma ->
  let p = mkRel (last_condition fctx) in
  let f = morphism_var n fctx in
  let m = get_var_shift n fctx in
  (sigma, mkApp (mkRel m, [| p; f |]))

let translate_pvar n = fun env fctx sigma ->
  let p = mkRel (last_condition fctx) in
  let f = morphism_var n fctx in
  let m = get_var_shift n fctx - 1 in
  (sigma, mkApp (mkRel m, [| p; f |]))

let mkHole = fun env fctx sigma ->
  let (sigma, (typ, _)) = Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
  let (sigma, c) = Evarutil.new_evar env sigma typ in
  (sigma, c)

(** Given a type A, builds Rel 1 ||- [[A]] *)
let mkParamType self t =
  get_category >>= fun cat ->
  fresh_constant frealizes >>= fun frealizes ->
  box (self.otranslate t) >>= fun t_ ->
  box (self.rtranslate t) >>= fun tr_ ->
  (fun env fctx sigma -> (sigma, last_condition fctx)) >>= fun last ->
  let ans = mkApp (mkConstU frealizes, [| cat.cat_obj; cat.cat_hom; mkRel last; t_; tr_ |]) in
  let ans = Vars.lift 1 ans in
  return (mkApp (ans, [| mkRel 1 |]))

let in_var self na t f =
  box_type (self.otranslate t) >>= fun t_ ->
  mkParamType self t >>= fun tr_ env fctx sigma ->
  let fctx = add_variable fctx in
  let ctx = [(rel_name na, None, tr_); (na, None, t_)] in
  let env = Environ.push_rel_context ctx env in
  f ctx env fctx sigma

(** Parametricity conditions. Rel1 is bound to a boxed term of the right type *)

let type_mon =
  get_category >>= fun cat ->
  fresh_constant ftypemon >>= fun ftypemon ->
  (fun env fctx sigma -> (sigma, last_condition fctx)) >>= fun last ->
  let ans = mkApp (mkConstU ftypemon, [| cat.cat_obj; cat.cat_hom; mkRel last |]) in
  return (mkApp (Vars.lift 1 ans, [| mkRel 1 |]))

let prod_mon self na t u =
  let in_dummy_var f = fun env fctx sigma ->
    let fctx = add_variable fctx in
    f env fctx sigma
  in
  in_dummy_var begin in_var self na t begin fun var ->
    mkParamType self u >>= fun u_ ->
    in_extend begin fun ext ->
      translate_var 2 >>= fun f ->
      box (translate_var 1) >>= fun x ->
      box (translate_pvar 1) >>= fun px ->
      let arg = mkApp (f, [| x; px |]) in
      return (it_mkLambda_or_LetIn arg ext)
    end >>= fun arg ->
    let u_ = Vars.subst1 arg u_ in
    return (it_mkProd_or_LetIn u_ var)
  end end >>= fun ans ->
  return (Vars.subst1 dummy ans)

let dummy_mon = mkProp

(** Forcing translation core *)

let rec otranslate c =
let self = { otranslate = otranslate; rtranslate = rtranslate } in
match kind_of_term c with
| Rel n ->
  translate_var n

| Sort s ->
  in_extend begin fun ext0 ->
    get_category >>= fun cat ->
    fresh_inductive cType >>= fun pi ->
    let tpe = mkApp (mkIndU pi, [| cat.cat_obj; cat.cat_hom; mkRel 2 |]) in
    return (it_mkLambda_or_LetIn tpe ext0)
  end >>= fun lam ->
  type_mon >>= fun mon ->
  mkfType lam mon

| Cast (c, k, t) ->
  otranslate c >>= fun c_ ->
  otranslate_type t >>= fun t_ ->
  let ans = mkCast (c_, k, t_) in
  return ans

| Prod (na, t, u) ->
  in_extend begin fun ext0 ->
    in_var self na t begin fun var ->
      otranslate u >>= fun u_ ->
      projfType u_ >>= fun u_ ->
      return (it_mkProd_or_LetIn u_ var)
    end >>= fun ans ->
    return (it_mkLambda_or_LetIn ans ext0)
  end >>= fun lam ->
  prod_mon self na t u >>= fun mon ->
  mkfType lam mon

| Lambda (na, t, u) ->
  in_var self na t begin fun var ->
    otranslate u >>= fun u_ ->
    return (it_mkLambda_or_LetIn u_ var)
  end

| App (t, args) ->
  otranslate t >>= fun t_ ->
  let map u =
    otranslate_boxed u >>= fun u_ ->
    rtranslate u >>= fun ur_ ->
    return [u_; ur_]
  in
  mmap map (Array.to_list args) >>= fun args_ ->
  let app = applist (t_, List.concat args_) in
  return app

| LetIn (na, c, t, u) -> assert false
| Var id -> assert false
| Const (p, u) -> assert false
| Ind (i, u) -> assert false
| Construct (c, u) -> assert false
| Case (ci, r, c, p) -> assert false
| Fix f -> assert false
| CoFix f -> assert false
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

and otranslate_type t env fctx sigma =
  let (sigma, t_) = otranslate t env fctx sigma in
  projfType t_ env fctx sigma

and otranslate_boxed t env fctx sigma =
  let (ext, ufctx) = extend fctx in
  let (sigma, t_) = otranslate t env ufctx sigma in
  let t_ = it_mkLambda_or_LetIn t_ ext in
  (sigma, t_)

and otranslate_boxed_type t env fctx sigma =
  let (ext, ufctx) = extend fctx in
  let (sigma, t_) = otranslate_type t env ufctx sigma in
  let t_ = it_mkProd_or_LetIn t_ ext in
  (sigma, t_)

and rtranslate t =
let self = { otranslate = otranslate; rtranslate = rtranslate } in
match kind_of_term t with
| Rel n ->
  fun env fctx sigma ->
    let f = morphism_var n fctx in
    let n = get_var_shift n fctx - 1 in
    let last = last_condition fctx in
    (sigma, mkApp (mkRel n, [| mkRel last; f; mkRel last; refl fctx.category (mkRel last) |]))

| Sort s ->
  in_extend begin fun ext ->
    fresh_universe >>= fun u ->
    otranslate_type (mkSort s) >>= fun uT ->
    let refl = Coqlib.gen_constant "" ["Init"; "Logic"] "eq_refl" in
    let refl = mkApp (refl, [| u; uT |]) in
    return (it_mkLambda_or_LetIn refl ext)
  end

| Cast (c, k, t) ->
  mkHole

| Prod (na, t, u) ->
  in_extend begin fun ext ->
    fresh_universe >>= fun u ->
    otranslate_type (mkProd (na, t, u)) >>= fun uT ->
    let refl = Coqlib.gen_constant "" ["Init"; "Logic"] "eq_refl" in
    let refl = mkApp (refl, [| u; uT |]) in
    return (it_mkLambda_or_LetIn refl ext)
  end

| Lambda (na, t, u) ->
  mkHole

| App (t, args) ->
  mkHole

| LetIn (na, c, t, u) -> assert false
| Var id -> assert false
| Const (p, u) -> assert false
| Ind (i, u) -> assert false
| Construct (c, u) -> assert false
| Case (ci, r, c, p) -> assert false
| Fix f -> assert false
| CoFix f -> assert false
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

let empty translator cat lift env =
  let ctx = rel_context env in
  let empty = { context = []; category = cat; translator; } in
  let empty = List.fold_right (fun _ fctx -> add_variable fctx) ctx empty in
  let rec flift fctx n =
    if n = 0 then fctx
    else flift (snd (extend fctx)) (pred n)
  in
  flift empty (match lift with None -> 0 | Some n -> n)

(** The toplevel option allows to close over the topmost forcing condition *)

let translate ?(toplevel = true) ?lift translator cat env sigma c =
  let empty = empty translator cat lift env in
  let env = Environ.push_rel (obj_name, None, cat.cat_obj) env in
  let (sigma, c) = otranslate c env empty sigma in
  let ans = if toplevel then mkLambda (pos_name, cat.cat_obj, c) else c in
  (sigma, ans)

let translate_type ?(toplevel = true) ?lift translator cat env sigma c =
  let empty = empty translator cat lift env in
  let env = Environ.push_rel (obj_name, None, cat.cat_obj) env in
  let (sigma, c) = otranslate_type c env empty sigma in
  let ans = if toplevel then mkProd (pos_name, cat.cat_obj, c) else c in
  (sigma, ans)

let translate_context ?(toplevel = true) ?lift translator cat env sigma ctx =
  let empty = empty translator cat lift env in
  let fold (na, body, t) (sigma, fctx, ctx_) =
    let (sigma, body_) = match body with
    | None -> (sigma, None)
    | Some _ -> assert false
    in
    let (ext, tfctx) = extend fctx in
    let (sigma, t_) = otranslate_type t env tfctx sigma in
    let t_ = it_mkProd_or_LetIn t_ ext in
    let decl_ = (na, body_, t_) in
    let fctx = add_variable fctx in
    (sigma, fctx, decl_ :: ctx_)
  in
  let init = if toplevel then [pos_name, None, cat.cat_obj] else [] in
  let (sigma, _, ctx_) = List.fold_right fold ctx (sigma, empty, init) in
  (sigma, ctx_)
