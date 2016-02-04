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
let ptype = Projection.make (Constant.make2 forcing_module (Label.make "type")) false
let pmono = Projection.make (Constant.make2 forcing_module (Label.make "mono")) false
let fcast = Constant.make3 forcing_module DirPath.empty (Label.make "cast")
let frealizes = Constant.make3 forcing_module DirPath.empty (Label.make "realizes")
let ftypemon = Constant.make3 forcing_module DirPath.empty (Label.make "Typeᶿ")
let fprodmon = Constant.make3 forcing_module DirPath.empty (Label.make "Prodᶿ")

let fBox = Constant.make3 forcing_module DirPath.empty (Label.make "Box")
let pbox = Projection.make (Constant.make2 forcing_module (Label.make "box")) false
let fmkBox = Constant.make3 forcing_module DirPath.empty (Label.make "mkBox")

let fTYPE = Constant.make3 forcing_module DirPath.empty (Label.make "TYPEᶠ")
let fBTYPE = Constant.make3 forcing_module DirPath.empty (Label.make "BTYPEᶠ")
let fARROW = Constant.make3 forcing_module DirPath.empty (Label.make "Arrowᶠ")
let fBARROW = Constant.make3 forcing_module DirPath.empty (Label.make "BArrowᶠ")
let fPROD = Constant.make3 forcing_module DirPath.empty (Label.make "Prodᶠ")
let fBPROD = Constant.make3 forcing_module DirPath.empty (Label.make "BProdᶠ")
let flift = Constant.make3 forcing_module DirPath.empty (Label.make "lift")

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
  | Variable :: fctx -> 1 + last fctx
  | Lift :: fctx -> 2
  in
  last fctx.context

let gather_morphisms n fctx =
  let rec gather i n fctx =
    if n = 0 then []
    else match fctx with
    | [] -> []
    | Variable :: fctx -> gather (i + 1) (n - 1) fctx
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
    | Variable :: fctx -> 1 + get (n - 1) fctx
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

let fresh_constructor c = (); fun env fctx sigma ->
  Evd.fresh_constructor_instance env sigma c

let fresh_universe = (); fun env fctx sigma ->
  let (sigma, s) = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  (sigma, mkSort s)

let with_cat c = fun env fctx sigma ->
  let cat = fctx.category in
  (sigma, mkApp (c, [| cat.cat_obj; cat.cat_hom |]))

let with_lcat c = fun env fctx sigma ->
  let cat = fctx.category in
  let n = last_condition fctx in
  (sigma, mkApp (c, [| cat.cat_obj; cat.cat_hom; mkRel n |]))

(** Macros *)

let liftn_named_decl n k (na, b, t) = (na, Option.map (fun c -> Vars.liftn n k c) b, Vars.liftn n k t)
let liftn_named_context n k ctx =
  let len = List.length ctx in
  List.mapi (fun i d -> liftn_named_decl n (k + len - i) d) ctx

(** Given an inhabitant of Typeᶠ builds a Type *)
let projfType c env fctx sigma =
  let c = mkOptProj c in
  let last = mkRel (last_condition fctx) in
  (sigma, mkOptApp (c, [| last; refl fctx.category last |]))

(** Inverse *)
let mkfType lam mon env fctx sigma =
  let (sigma, pc) = Evd.fresh_constructor_instance env sigma ctype in
  let tpe = mkApp (mkConstructU pc, [| fctx.category.cat_obj; fctx.category.cat_hom; mkRel (last_condition fctx); lam; mon |]) in
  (sigma, tpe)

let mkHole = fun env fctx sigma ->
  let (sigma, (typ, _)) = Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
  let (sigma, c) = Evarutil.new_evar env sigma typ in
  (sigma, c)

let in_var na t_ f =
  fresh_constant fBox >>= fun pc ->
  with_lcat (mkConstU pc) >>= fun fBox ->
  fun env fctx sigma ->
  let t_ = mkApp (fBox, [| t_ |]) in
  let fctx = add_variable fctx in
  let ctx = [(na, None, t_)] in
  let env = Environ.push_rel_context ctx env in
  f ctx env fctx sigma

(** Parametricity conditions. Rel1 is bound to a boxed term of the right type *)

let dummy_mon = mkProp

(** Forcing translation core *)

let debox_with c last =
  get_category >>= fun cat ->
  let ans = mkProj (pbox, c) in
  let ans = mkApp (ans, [| last; refl cat last |]) in
  return ans

let debox c =
  (fun env fctx sigma -> (sigma, last_condition fctx)) >>= fun n ->
  debox_with c (mkRel n)

let box_abs na t_ (ext, var, u_) =
  fresh_constant fmkBox >>= fun fmkBox ->
  with_lcat (mkConstU fmkBox) >>= fun fmkBox ->
  fresh_constant fBARROW >>= fun fBARROW ->
  with_lcat (mkConstU fBARROW) >>= fun fBARROW ->
  fresh_constant fBTYPE >>= fun fBTYPE ->
  with_lcat (mkConstU fBTYPE) >>= fun fBTYPE ->
  let typ = mkApp (fBARROW, [| t_; fBTYPE |]) in
  debox_with u_ (mkRel 3) >>= fun term ->
  let term = it_mkLambda_or_LetIn term (var @ ext) in
  let real = it_mkLambda_or_LetIn u_ (var @ ext) in
  let ans = mkApp (fmkBox, [| typ; term; real |]) in
  return ans

let rec rtranslate t = match kind_of_term t with
| Rel n ->
  fun env fctx sigma ->
  let morph = gather_morphisms n fctx in
  let m = get_var_shift n fctx in
  (** Short path: do not lift if not necessary *)
  let (sigma, ans) = match morph with
  | [] -> (sigma, mkRel m)
  | _ ->
    let (sigma, pc) = Evd.fresh_constant_instance env sigma flift in
    let (sigma, flift) = with_lcat (mkConstU pc) env fctx sigma in
    (sigma, mkApp (flift, [| mkRel m |])) (** FIXME *)
  in
  (sigma, ans)

| Sort s ->
  fresh_constant fBTYPE >>= fun fBTYPE ->
  with_lcat (mkConstU fBTYPE)

| Cast (c, k, t) ->
  mkHole

| Prod (na, t, u) when Vars.noccurn 1 u ->
  fresh_constant fBARROW >>= fun c_ ->
  with_lcat (mkConstU c_) >>= fun ans ->
  rtranslate t >>= fun t_ ->
  rtranslate (Vars.subst1 dummy u) >>= fun u_ ->
  return (mkApp (ans, [| t_; u_ |]))

| Prod (na, t, u) ->
  fresh_constant fBPROD >>= fun c_ ->
  with_lcat (mkConstU c_) >>= fun ans ->
  rtranslate t >>= fun t_ ->
  in_extend begin fun ext ->
  in_var na (Vars.lift 2 t_) begin fun var ->
    rtranslate u >>= fun u_ ->
    return (ext, var, u_)
  end end >>= fun (ext, var, u_) ->
  box_abs na t_ (ext, var, u_) >>= fun u_ ->
  return (mkApp (ans, [| t_; u_ |]))

| Lambda (na, t, u) ->
  fresh_constant fmkBox >>= fun box_ ->
  with_lcat (mkConstU box_) >>= fun box_ ->
  rtranslate t >>= fun t_ ->
  in_var na t_ begin fun var ->
    rtranslate u >>= fun u_ ->
    return (var, u_)
  end >>= fun (var, u_) ->
  in_extend begin fun ext ->
    debox (Vars.lift 2 u_) >>= fun u_ ->
    return (it_mkLambda_or_LetIn u_ ext)
  end >>= fun f_ ->
  mkHole >>= fun hole ->
  return (mkApp (box_, [| hole; f_ ; u_ |]))

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

let otranslate c =
  rtranslate c >>= fun c_ ->
  debox c_

let otranslate_type t env fctx sigma =
  let (sigma, t_) = otranslate t env fctx sigma in
  projfType t_ env fctx sigma

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
