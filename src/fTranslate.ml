open Names
open Term
open Constr
open Declarations
open Environ
open Globnames

module RelDecl = Context.Rel.Declaration

type translator = GlobRef.t Refmap.t
exception MissingGlobal of GlobRef.t

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
  let arr = Term.mkArrow lft rgt in
  mkProd (obj_name, cat.cat_obj, arr)

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

(** Optimization of cuts *)

let mkOptApp (t, args) =
  let len = Array.length args in
  try
    let (_, t) = Term.decompose_lam_n len t in
    Vars.substl (CArray.rev_to_list args) t
  with _ ->
    mkApp (t, args)

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
  let open RelDecl in
  let cat = fctx.category in
  let last = last_condition fctx in
  let ext = [LocalAssum (hom_name, hom cat (mkRel (1 + last)) (mkRel 1));
             LocalAssum (pos_name, cat.cat_obj)] in
  (ext, { fctx with context = Lift :: fctx.context })

let add_variable fctx =
  { fctx with context = Variable :: fctx.context }

(** Handling of globals *) 

let translate_var fctx n =
  let p = mkRel (last_condition fctx) in
  let f = morphism_var n fctx in
  let m = get_var_shift n fctx in
  mkApp (mkRel m, [| p; f |])

let rec untranslate_rel n c = match Constr.kind c with
| App (t, args) when isRel t && Array.length args >= 2 ->
  c
| _ -> Constr.map_with_binders succ untranslate_rel n c

let get_inductive fctx ind =
  let gr = IndRef ind in
  let gr_ =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  match gr_ with
  | IndRef ind_ -> ind_
  | _ -> assert false

let apply_global env sigma gr u fctx =
  (** FIXME *)
  let p' =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env sigma p' in
  let c = EConstr.to_constr sigma c in
  let last = last_condition fctx in
  match gr with
  | IndRef _ -> assert false
  | _ -> (sigma, mkApp (c, [| mkRel last |]))

(** Forcing translation core *)

let rec otranslate env fctx sigma c = match kind c with
| Rel n ->
  let ans = translate_var fctx n in
  (sigma, ans)
| Sort s ->
  let (ext0, fctx) = extend fctx in
  let (ext, fctx) = extend fctx in
  let (sigma, s') =
    if Sorts.is_prop s then (sigma, Sorts.prop)
    else Evd.new_sort_variable Evd.univ_flexible sigma
  in
  let sigma = Evd.set_leq_sort env sigma s s' in
  let tpe = it_mkProd_or_LetIn (mkSort s') ext in
  let lam = it_mkLambda_or_LetIn tpe ext0 in
  (sigma, lam)
| Cast (c, k, t) ->
  let (sigma, c_) = otranslate env fctx sigma c in
  let (sigma, t_) = otranslate_type env fctx sigma t in
  let ans = mkCast (c_, k, t_) in
  (sigma, ans)
| Prod (na, t, u) ->
  let (ext0, fctx) = extend fctx in
  (** Translation of t *)
  let (sigma, t_) = otranslate_boxed_type env fctx sigma t in
  (** Translation of u *)
  let ufctx = add_variable fctx in
  let (sigma, u_) = otranslate_type env ufctx sigma u in
  (** Result *)
  let ans = mkProd (na, t_, u_) in
  let lam = it_mkLambda_or_LetIn ans ext0 in
  (sigma, lam)
| Lambda (na, t, u) ->
  (** Translation of t *)
  let (sigma, t_) = otranslate_boxed_type env fctx sigma t in
  (** Translation of u *)
  let ufctx = add_variable fctx in
  let (sigma, u_) = otranslate env ufctx sigma u in
  let ans = mkLambda (na, t_, u_) in
  (sigma, ans)
| LetIn (na, c, t, u) ->
  let (sigma, c_) = otranslate_boxed env fctx sigma c in
  let (sigma, t_) = otranslate_boxed_type env fctx sigma t in
  let ufctx = add_variable fctx in
  let (sigma, u_) = otranslate env ufctx sigma u in
  (sigma, mkLetIn (na, c_, t_, u_))
| App (t, args) when isInd t ->
  let (ind, u) = destInd t in
  otranslate_ind env fctx sigma ind u args
| App (t, args) ->
  let (sigma, t_) = otranslate env fctx sigma t in
  let fold sigma u = otranslate_boxed env fctx sigma u in
  let (sigma, args_) = CArray.fold_left_map fold sigma args in
  let app = mkApp (t_, args_) in
  (sigma, app)
| Var id ->
  apply_global env sigma (VarRef id) Univ.Instance.empty fctx
| Const (p, u) ->
  apply_global env sigma (ConstRef p) u fctx
| Ind (ind, u) ->
  otranslate_ind env fctx sigma ind u [||]
| Construct (c, u) ->
  apply_global env sigma (ConstructRef c) u fctx
| Case (ci, r, c, p) ->
   let ind_ = get_inductive fctx ci.ci_ind in
   let ci_ = Inductiveops.make_case_info env ind_ ci.ci_pp_info.style in
   let (sigma, c_) = otranslate env fctx sigma c in
   let fix_return_clause env fctx sigma r =
     (** The return clause structure is fun indexes self => Q
         All indices must be boxed, but self only needs to be translated *)
     let (args, r_) = decompose_lam_assum r in
     let (na, self, args) = match args with
       | RelDecl.LocalAssum (na, ty) :: t -> (na, ty, t)
       | _ -> assert false in
     let fold (sigma, fctx) decl =
       let (na, o, u) = RelDecl.to_tuple decl in
      (** For every translated index, the corresponding variable is added
          to the forcing context *)
       let (sigma, u_) = otranslate_boxed_type env fctx sigma u in
       let (sigma, o_) = match o with
         | None -> (sigma, None)
         | Some o -> let (sigma, o) = otranslate_boxed env fctx sigma o in (sigma, Some o) in
       let fctx = add_variable fctx in
       let decl = match o_ with None -> RelDecl.LocalAssum (na, u_) | Some o_ -> RelDecl.LocalDef (na, o_, u_) in
       (sigma, fctx), decl
     in
     let (sigma, fctx), args = CList.fold_left_map fold (sigma, fctx) args in
     let (sigma, self_) = otranslate_type env fctx sigma self in
     let fctx_ = add_variable fctx in
     let (sigma, r_) = otranslate_type env fctx_ sigma r_ in
     let (ext, ufctx) = extend fctx in
     let selfid = Id.of_string "self" in
     let flags = let open CClosure in
       RedFlags.red_add betaiota RedFlags.fDELTA
     in
     let r_ = FAux.clos_norm_flags flags env r_ in
     let r_ = Vars.substnl [it_mkLambda_or_LetIn (mkVar selfid) ext] 1 (Vars.lift 1 r_) in
     let r_ = FAux.clos_norm_flags CClosure.beta env r_ in
     let r_ = Vars.subst_var selfid r_ in
     let r_ = it_mkLambda_or_LetIn r_ (RelDecl.LocalAssum (na, self_) :: args) in
     (sigma, r_)       
   in
   let (sigma, r_) = fix_return_clause env fctx sigma r in
   let fold sigma u = otranslate env fctx sigma u in
   let (sigma, p_) = CArray.fold_left_map fold sigma p in
   (sigma, mkCase (ci_, r_, c_, p_))
| Fix f -> assert false
| CoFix f -> assert false
| Proj (p, c) -> assert false
| Meta _ -> assert false
| Evar _ -> assert false

and otranslate_ind env fctx sigma ind u args =
  let ind_ = get_inductive fctx ind in
  let (_, oib) = Inductive.lookup_mind_specif env ind_ in
  let fold sigma u = otranslate_boxed env fctx sigma u in
  let (sigma, args_) = CArray.fold_left_map fold sigma args in
  (** First parameter is the toplevel forcing condition *)
  let _, paramtyp = CList.sep_last oib.mind_arity_ctxt in
  let nparams = List.length paramtyp in
  let last = last_condition fctx in
  let fctx = List.fold_left (fun accu _ -> add_variable accu) fctx paramtyp in
  let (ext, fctx) = extend fctx in
  let mk_var n =
    let n = nparams - n in
    let (ext0, fctx) = extend fctx in
    let ans = translate_var fctx n in
    it_mkLambda_or_LetIn ans ext0
  in
  let (sigma, pi) = Evd.fresh_inductive_instance env sigma ind_ in
  let params = CList.init nparams mk_var in
  let app = applist (mkIndU pi, mkRel (last_condition fctx) :: params) in
  let map_p i c = Vars.substnl_decl [mkRel last] (nparams - i - 1) c in
  let paramtyp = List.mapi map_p paramtyp in
  let ans = it_mkLambda_or_LetIn app (ext @ paramtyp) in
  (sigma, mkOptApp (ans, args_))

and otranslate_type env fctx sigma t =
  let (sigma, t_) = otranslate env fctx sigma t in
  let last = mkRel (last_condition fctx) in
  let t_ = mkOptApp (t_, [| last; refl fctx.category last |]) in
  (sigma, t_)

and otranslate_boxed env fctx sigma t =
  let (ext, ufctx) = extend fctx in
  let (sigma, t_) = otranslate env ufctx sigma t in
  let t_ = it_mkLambda_or_LetIn t_ ext in
  (sigma, t_)

and otranslate_boxed_type env fctx sigma t =
  let (ext, ufctx) = extend fctx in
  let (sigma, t_) = otranslate_type env ufctx sigma t in
  let t_ = it_mkProd_or_LetIn t_ ext in
  (sigma, t_)

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
  let (sigma, c) = otranslate env empty sigma c in
  let ans = if toplevel then mkLambda (pos_name, cat.cat_obj, c) else c in
  (sigma, ans)

let translate_type ?(toplevel = true) ?lift translator cat env sigma c =
  let empty = empty translator cat lift env in
  let (sigma, c) = otranslate_type env empty sigma c in
  let ans = if toplevel then mkProd (pos_name, cat.cat_obj, c) else c in
  (sigma, ans)

let translate_context ?(toplevel = true) ?lift translator cat env sigma ctx =
  let empty = empty translator cat lift env in
  let fold decl (sigma, fctx, ctx_) =
    let (na, body, t) = RelDecl.to_tuple decl in
    let (ext, tfctx) = extend fctx in
    let (sigma, t_) = otranslate_type env tfctx sigma t in
    let t_ = it_mkProd_or_LetIn t_ ext in
    let (sigma, decl_) = match body with
    | None -> (sigma, RelDecl.LocalAssum (na, t_))
    | Some _ -> assert false
    in
    let fctx = add_variable fctx in
    (sigma, fctx, decl_ :: ctx_)
  in
  let init = if toplevel then [RelDecl.LocalAssum (pos_name, cat.cat_obj)] else [] in
  let (sigma, _, ctx_) = List.fold_right fold ctx (sigma, empty, init) in
  (sigma, ctx_)
