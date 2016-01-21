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

let in_extend f = (); fun env fctx sigma ->
  let (ext, fctx) = extend fctx in
  f ext env fctx sigma

let in_var f = (); fun env fctx sigma ->
  let fctx = add_variable fctx in
  f env fctx sigma

let get_category = (); fun env fctx sigma -> (sigma, fctx.category)

let get_inductive ind = (); fun env fctx sigma ->
  Evd.fresh_inductive_instance env sigma ind

(** Macros *)

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
  let tpe = mkApp (mkConstructU pc, [| fctx.category.cat_obj; hom_type fctx.category; mkRel (last_condition fctx); lam; mon |]) in
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

let translate_var fctx n =
  let p = mkRel (last_condition fctx) in
  let f = morphism_var n fctx in
  let m = get_var_shift n fctx in
  mkApp (mkRel m, [| p; f |])

(** Parametricity conditions. Rel1 is bound to a boxed term of the right type *)

let type_mon env fctx sigma =
  let cat = fctx.category in
  let dummy = mkProp in
  let fctx = add_variable fctx in
  let eq = Coqlib.gen_constant "" ["Init"; "Logic"] "eq" in
  let (sigma, s) = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
  let (ext, fctx) = extend fctx in
  let (ext0, fctx) = extend fctx in
  (** (A q f).type r g *)
  let lhs = mkApp (mkOptProj (mkApp (mkRel 5, [| mkRel 4; mkRel 3 |])), [| mkRel 2; mkRel 1 |]) in
  (** (A r (f o g)).type r id *)
  let rhs = mkApp (mkOptProj (mkApp (mkRel 5, [| mkRel 2; trns cat dummy dummy (mkRel 2) (mkRel 3) (mkRel 1) |])), [| mkRel 2; refl cat (mkRel 2) |]) in
  let mon = mkApp (eq, [| mkSort s; lhs; rhs |]) in
  let mon = it_mkProd_or_LetIn mon (ext0 @ ext) in
  let mon = Vars.substnl [mkProp] 2 mon in
  (sigma, mon)

let prod_mon na t u =
(*   box_type t >>= fun t_ -> *)
(*   rel_type t >>= fun rel_ -> *)
(*   in_var (box (fun env fctx sigma -> (sigma, translate_var fctx 1))) >>= fun x -> *)
  (** There is hidden variable up there *)
(*   let t_ = Vars.lift 1 t_ in *)
(*   let rel_ = Vars.lift 2 rel_ in *)
(*   let relarg = mkOptApp (rel_, [| Vars.liftn 1 2 x |]) in *)
(*   return (mkProd (na, t_, (*mkArrow relarg*) mkProp)) *)
  return mkProp

let dummy_mon = mkProp

(** Handling of globals *) 

let rec untranslate_rel n c = match Constr.kind c with
| App (t, args) when isRel t && Array.length args >= 2 ->
  c
| _ -> Constr.map_with_binders succ untranslate_rel n c

let fix_return_clause env fctx sigma r_ =
  (** The return clause must be mangled for the last variable *)
(*   msg_info (Termops.print_constr r_); *)
  let (args, r_) = decompose_lam_assum r_ in
  let ((na, _, self), args) = match args with h :: t -> (h, t) | _ -> assert false in
  (** Remove the forall boxing *)
  let self_ = match decompose_prod_n 2 self with
  | ([_; _], c) -> c
  | exception _ -> assert false
  in
  let last = last_condition fctx + List.length args in
  let (ext, _) = extend fctx in
  let r_ = untranslate_rel 1 r_ in
  let r_ = mkApp (r_, [| mkRel (last + 1); refl fctx.category (mkRel (last + 1)) |]) in
  let self_ = Vars.substl [refl fctx.category (mkRel last); (mkRel last)] self_ in
  let r_ = it_mkLambda_or_LetIn r_ ((na, None, self_) :: args) in
  (sigma, r_)

let apply_global env sigma gr u fctx =
  (** FIXME *)
  let p' =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env sigma p' in
  let last = last_condition fctx in
  match gr with
  | IndRef _ ->
    let (_, oib) = Inductive.lookup_mind_specif env (fst (destInd c)) in
    (** First parameter is the toplevel forcing condition *)
    let _, paramtyp = CList.sep_last oib.mind_arity_ctxt in
    let nparams = List.length paramtyp in
    let fctx = List.fold_left (fun accu _ -> add_variable accu) fctx paramtyp in
    let (ext, fctx0) = extend fctx in
    let mk_var n =
      let n = nparams - n in
      let (ext0, fctx) = extend fctx0 in
      let ans = translate_var fctx n in
      it_mkLambda_or_LetIn ans ext0
    in
    let params = CList.init nparams mk_var in
    let app = applist (c, mkRel (last_condition fctx0) :: params) in
    let (sigma, tpe) = mkfType (it_mkLambda_or_LetIn app ext) dummy_mon env fctx sigma in
    let map_p i c = Vars.substnl_decl [mkRel last] (nparams - i - 1) c in
    let paramtyp = List.mapi map_p paramtyp in
    let ans = it_mkLambda_or_LetIn tpe paramtyp in
    (sigma, ans)
  | _ -> (sigma, mkApp (c, [| mkRel last |]))

(** Forcing translation core *)

let rec otranslate c = match kind_of_term c with
| Rel n ->
  fun env fctx sigma ->
  let ans = translate_var fctx n in
  (sigma, ans)

| Sort s ->
  in_extend begin fun ext0 ->
    get_category >>= fun cat ->
    get_inductive cType >>= fun pi ->
    let tpe = mkApp (mkIndU pi, [| cat.cat_obj; hom_type cat; mkRel 2 |]) in
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
    otranslate_boxed_type t >>= fun t_ ->
    in_var begin
      otranslate u >>= fun u_ ->
      projfType u_
    end >>= fun u_ ->
    let unit = Coqlib.gen_constant "" ["Init"; "Datatypes"] "unit" in
    let ans = mkProd (na, t_, mkProd (rel_name na, unit, u_)) in
    return (it_mkLambda_or_LetIn ans ext0)
  end >>= fun lam ->
  prod_mon na (otranslate t) (otranslate u) >>= fun mon ->
  mkfType lam mon

| Lambda (na, t, u) ->
  otranslate_boxed_type t >>= fun t_ ->
  let unit = Coqlib.gen_constant "" ["Init"; "Datatypes"] "unit" in
  in_var begin
    otranslate u
  end >>= fun u_ ->
  return (mkLambda (na, t_, (mkLambda (rel_name na, unit, u_))))

| LetIn (na, c, t, u) ->
  otranslate_boxed c >>= fun c_ ->
  otranslate_boxed_type t >>= fun t_ ->
  in_var begin
    otranslate u
  end >>= fun u_ ->
  return (mkLetIn (na, c_, t_, u_))

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

and rtranslate t env fctx sigma =
  let tt = Coqlib.gen_constant "" ["Init"; "Datatypes"] "tt" in
  (sigma, tt)

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
  let (sigma, c) = otranslate c env empty sigma in
  let ans = if toplevel then mkLambda (pos_name, cat.cat_obj, c) else c in
  (sigma, ans)

let translate_type ?(toplevel = true) ?lift translator cat env sigma c =
  let empty = empty translator cat lift env in
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
