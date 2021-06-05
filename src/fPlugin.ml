open CErrors
open Pp
open Util
open Names
open Decls
open Term
open Constr
open Libobject
open Proofview.Notations

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᶠ")

(** Record of translation between globals *)

let translator : FTranslate.translator ref =
  Summary.ref ~name:"Forcing Global Table" GlobRef.Map.empty

type translator_obj = (GlobRef.t * GlobRef.t) list

let add_translator translator l =
  List.fold_left (fun accu (src, dst) -> GlobRef.Map.add src dst accu) translator l
							    
let cache_translator (_, l) =
  translator := add_translator !translator l

let load_translator _ l = cache_translator l
let open_translator _ _ l = cache_translator l

let in_translator : translator_obj -> obj =
  declare_object { (default_object "FORCING TRANSLATOR") with
    cache_function = cache_translator;
    load_function = load_translator;
    open_function = open_translator;
    discharge_function = (fun (_, o) -> Some o);
    classify_function = (fun o -> Substitute o);
  }

(** Tactic *)

let force_tac cat c =
  Proofview.Goal.enter (begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let cat =
      let (obj, hom) = cat in {
          FTranslate.cat_obj = EConstr.to_constr sigma obj;
          FTranslate.cat_hom = EConstr.to_constr sigma hom;
        } in
    let c = EConstr.to_constr sigma c in
    let (sigma, ans) = FTranslate.translate !translator cat env sigma c in
    let sigma, _ = Typing.type_of env sigma (EConstr.of_constr ans) in
    Proofview.Unsafe.tclEVARS sigma <*>
    Tactics.letin_tac None Names.Name.Anonymous (EConstr.of_constr ans) None Locusops.allHyps
  end)

(*
let force_solve cat c =
  Proofview.Goal.enter (begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, ans) = FTranslate.translate !translator cat env sigma c in
    (*     msg_info (Termops.print_constr ans); *)
    let sigma, _ = Typing.type_of env sigma (EConstr.of_constr ans) in
    Proofview.Unsafe.tclEVARS sigma <*>
    FAux.refine_casted ~typecheck:false (fun sigma -> (sigma,EConstr.of_constr ans))
  end)
*)

let force_translate_constant cat cst ids =
  let id = match ids with
  | None -> translate_name (Nametab.basename_of_global (GlobRef.ConstRef cst))
  | Some [id] -> id
  | Some _ -> user_err (Pp.str "Not the right number of provided names")
  in
  (* Translate the type *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let typ, _uctx = Typeops.type_of_global_in_context env (GlobRef.ConstRef cst) in
  let (sigma, typ) = FTranslate.translate_type !translator cat env sigma typ in
  let sigma, _ = Typing.type_of env sigma (EConstr.of_constr typ) in
  (* Define the term by tactic *)
  let body, _, _ = Option.get (Global.body_of_constant Library.indirect_accessor cst) in
  let (sigma, body) = FTranslate.translate !translator cat env sigma body in
(*  Pp.pp_with Format.err_formatter (Printer.pr_constr_env env sigma body);*)
  let sigma = Typing.check env sigma (EConstr.of_constr body) (EConstr.of_constr typ) in
  let uctx = Evd.univ_entry ~poly:false sigma in
  let ce = Declare.definition_entry ~types:typ ~univs:uctx body in
  let cd = Declare.DefinitionEntry ce in
  let kind = IsProof Lemma in
  let cst_ = Declare.declare_constant ~name:id ~kind cd in
  [GlobRef.ConstRef cst, GlobRef.ConstRef cst_]

let eta_reduce c =
  let rec aux c =
    match kind c with
    | Lambda (n, t, b) ->
       let rec eta b =
	 match kind b with
	 | App (f, args) ->
	    if isRelN 1 (Array.last args) then
	      let args', _ = Array.chop (Array.length args - 1) args in
	      if Array.for_all (Vars.noccurn 1) args' then Vars.subst1 mkProp (mkApp (f, args'))
	      else let b' = aux b in if Constr.equal b b' then c else eta b'
	    else let b' = aux b in if Constr.equal b b' then c else eta b'
	 | _ -> let b' = aux b in
	    if Constr.equal b' b then c else eta b'
       in eta b
    | _ -> Constr.map aux c
  in aux c

let get_mind_globrefs mind =
  let open Declarations in
  let mib = Global.lookup_mind mind in
  let map i body =
    let ind = GlobRef.IndRef (mind, i) in
    let map_cons j _ = GlobRef.ConstructRef ((mind, i), j + 1) in
    ind :: List.mapi map_cons (Array.to_list body.mind_consnames)
  in
  let l = List.mapi map (Array.to_list mib.mind_packets) in
  List.flatten l

let force_translate_inductive cat ind ids =
  (* From a kernel inductive body construct an entry for the inductive. There
     are slight mismatches in the representation, in particular in the handling
     of contexts. See {!Declarations} and {!Entries}. *)
  let open Declarations in
  let open Entries in
  let env = Global.env () in
  let (mib, _) = Global.lookup_inductive ind in
  let nparams = List.length mib.mind_params_ctxt in
  (* For each block in the inductive we build the translation *)
  let substind =
    Array.map_to_list (fun oib ->
        NamedDecl.LocalAssum (Context.annotR oib.mind_typename,
			      Inductive.type_of_inductive ((mib, oib), Univ.Instance.empty)))
      mib.mind_packets
  in
  let invsubst = List.map NamedDecl.get_id substind in
  let translator = add_translator !translator (List.map (fun id -> GlobRef.VarRef id, GlobRef.VarRef id) invsubst) in
  (* À chaque inductif I on associe une fonction λp.λparams.λindices.λ(qα), 
     (mkVar I) p params indices *)
  let sigma = Evd.from_env env in
  let (sigma, substfn) = 
    let fn_oib oib = 
      let narityctxt = List.length oib.mind_arity_ctxt in
      let args = Array.init (narityctxt + 1) (fun i -> mkRel (narityctxt + 3 - i)) in
      let fnbody = mkApp (mkVar oib.mind_typename, args) in
      let obj = cat.FTranslate.cat_obj in
      let fold (sigma, ctxt) decl =
        let (x, o, t_) = RelDecl.to_tuple decl in
        let (sigma, tr_t_) = FTranslate.translate_type translator cat env sigma t_ in
        assert (o = None);
        (sigma, RelDecl.LocalAssum (x, tr_t_) :: ctxt)
      in
      let (sigma, tr_arity) = List.fold_left fold (sigma, []) oib.mind_arity_ctxt in
      let open RelDecl in
      (sigma, it_mkLambda_or_LetIn fnbody
         ([LocalAssum (Context.anonR, FTranslate.hom cat (mkRel 3) (mkRel (3 + narityctxt)));
           LocalAssum (Context.anonR, obj)]
          @ tr_arity
          @ [LocalAssum (Context.anonR, obj)]))
    in
    let fold (sigma, acc) oib =
      let (sigma, fn) = fn_oib oib in
      (sigma, (oib.mind_typename, fn) :: acc)
    in
    Array.fold_left fold (sigma, []) mib.mind_packets
  in
  let make_one_entry params body (sigma, bodies_) =
    (* Heuristic for the return type. Can we do better? *)
    let (sigma, s) =
      if Sorts.family_leq Sorts.InType body.mind_kelim then
        let sigma, s = Evarutil.new_Type sigma in
        (sigma, EConstr.to_constr sigma s)
      else
        (sigma, mkProp)
    in
    let (sigma, arity) =
      (* On obtient l'arité de l'inductif en traduisant le type de chaque indice
         i.e : si I ... : (i1 : A1),...,(in : An),s alors l'arité traduite 
         est (i1 : [A1])...(in : [An]), s *)
      let nindexes = List.length body.mind_arity_ctxt - nparams in
      let ctx = List.firstn nindexes body.mind_arity_ctxt in
      let env' = Environ.push_rel_context mib.mind_params_ctxt env in
      let a = it_mkProd_or_LetIn s ctx in
      let (sigma, a) = FTranslate.translate_type ~toplevel:false translator cat env' sigma a in
      (* En traduisant le type, le codomaine a aussi été traduit. On le remplace par le codomaine
         originel *)
      let (a, _) = decompose_prod_n nindexes a in 
      (sigma, compose_prod a s)
    in
    let fold_lc (sigma, lc_) typ =
      (* We exploit the fact that the translation actually does not depend on
         the rel_context of the environment except for its length. *)
      let env' = Environ.push_named_context substind env in
      let envtr = Environ.push_rel_context (CList.tl params) env' in
      let _, typ = decompose_prod_n nparams typ in
      let typ = Vars.substnl (List.map mkVar invsubst) nparams typ in
      let (sigma, typ_) =
        (* The translation assumes that the first introduced variable is the
           toplevel forcing condition, which is not the case here. *)
        FTranslate.translate_type ~toplevel:false translator cat envtr sigma typ in
      let typ_ = Vars.replace_vars substfn typ_ in 
      let typ_ = FAux.clos_norm_flags CClosure.beta env typ_ in 
      let typ_ = Vars.substn_vars (List.length params + 1) invsubst typ_ in
      let envtyp_ =
        Environ.push_rel (RelDecl.LocalAssum (Context.nameR (Nameops.add_suffix body.mind_typename "_f"),
		                              it_mkProd_or_LetIn arity params))
          env
      in
      let envtyp_ = Environ.push_rel_context params envtyp_ in
      let sigma, ty = Typing.type_of envtyp_ sigma (EConstr.of_constr typ_) in
      let sigma = match Reductionops.infer_conv ~pb:Reduction.CUMUL envtyp_ sigma ty (EConstr.of_constr s) with
        | None -> assert false 
        | Some sigma -> sigma in
      (sigma, eta_reduce typ_ :: lc_)
    in
    let typename, consnames = match ids with
    | None ->
      (translate_name body.mind_typename, CArray.map_to_list translate_name body.mind_consnames)
    | Some ids when List.length ids = Array.length body.mind_consnames + 1 ->
      (List.hd ids, List.tl ids)
    | _ ->
      user_err (Pp.str "Not the right number of provided names")
    in
    let (sigma, lc_) = Array.fold_left fold_lc (sigma, []) body.mind_user_lc in
    let body_ = {
      mind_entry_typename = typename;
      mind_entry_arity = arity;
      mind_entry_consnames = consnames;
      mind_entry_lc = List.rev lc_;
    } in
    (sigma, body_ :: bodies_)
  in
  (* For template polymorphism, one would need to maintain a substitution of universes *)
  let template = false in
  (* We proceed to the whole mutual block *)
  let record = match mib.mind_record with
  | NotRecord -> None
  | FakeRecord -> Some None
  | PrimRecord info -> Some (Some (Array.map (fun (id,_,_,_) -> id) info))
  in
  let (sigma, params_) = FTranslate.translate_context translator cat env sigma mib.mind_params_ctxt in
  let (sigma, bodies_) = Array.fold_right (make_one_entry params_) mib.mind_packets (sigma, []) in
  let _debug b =
    let open Feedback in
    msg_info (Names.Id.print b.mind_entry_typename ++ str " : " ++ Printer.pr_constr_env env sigma (it_mkProd_or_LetIn b.mind_entry_arity params_));
    let cs = List.combine b.mind_entry_consnames b.mind_entry_lc in
    let pr_constructor (id, tpe) =
      msg_info (Names.Id.print id ++ str " : " ++ Printer.pr_constr_env env sigma tpe)
    in
    List.iter pr_constructor cs
  in
(*   List.iter debug bodies_; *)
  let uctx =
    match mib.mind_universes with
    | Monomorphic _ -> Monomorphic_entry (Evd.universe_context_set sigma)
    | Polymorphic _ -> Evd.univ_entry ~poly:true sigma in
  let mib_ = {
    mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params_;
    mind_entry_inds = bodies_;
    mind_entry_universes = uctx;
    mind_entry_template = template;
    mind_entry_cumulative = Option.has_some mib.mind_variance;
    mind_entry_private = mib.mind_private;
  } in
  let mib_ = DeclareInd.declare_mutual_inductive_with_eliminations mib_ UnivNames.empty_binders [] in
  let map_data gr = match gr with
  | GlobRef.IndRef (mib, i) -> (gr, GlobRef.IndRef (mib_, i))
  | GlobRef.ConstructRef ((mib, i), j) -> (gr, GlobRef.ConstructRef ((mib_, i), j))
  | _ -> assert false
  in
  List.map map_data (get_mind_globrefs (fst ind))

let force_translate (obj, hom) gr ids =
  let gr = Nametab.global gr in
  let obj = UnivGen.constr_of_monomorphic_global (Nametab.global obj) in
  let hom = UnivGen.constr_of_monomorphic_global (Nametab.global hom) in
  let cat = {
    FTranslate.cat_obj = obj;
    FTranslate.cat_hom = hom;
  } in
  let ans = match gr with
  | GlobRef.ConstRef cst -> force_translate_constant cat cst ids
  | GlobRef.IndRef ind -> force_translate_inductive cat ind ids
  | _ -> user_err (Pp.str "Translation not handled.")
  in
  let () = Lib.add_anonymous_leaf (in_translator ans) in
  let msg_translate (src, dst) =
    Feedback.msg_info (str "Global " ++ Printer.pr_global src ++
    str " has been translated as " ++ Printer.pr_global dst ++ str ".")
  in
  List.iter msg_translate ans

(** Implementation in the forcing layer *)

let force_implement (obj, hom) id typ idopt =
  let env = Global.env () in
  let obj = UnivGen.constr_of_monomorphic_global (Nametab.global obj) in
  let hom = UnivGen.constr_of_monomorphic_global (Nametab.global hom) in
  let cat = {
    FTranslate.cat_obj = obj;
    FTranslate.cat_hom = hom;
  } in
  let id_ = match idopt with
  | None -> translate_name id
  | Some id -> id
  in
  let kind = IsDefinition Definition in
  let scope = Locality.(Global ImportDefaultBehavior) in 
  let sigma = Evd.from_env env in
  let (typ, uctx) = Constrintern.interp_type env sigma typ in
  let sigma = Evd.from_ctx uctx in
  let typ = EConstr.to_constr sigma typ in
  let (sigma, typ_) = FTranslate.translate_type !translator cat env sigma typ in
  let (sigma, _) = Typing.type_of env sigma (EConstr.of_constr typ_) in
  let hook = Declare.Hook.(make (function S.{uctx;dref} ->
    (* Declare the original term as an axiom *)
    let param = (None, (typ, Entries.Monomorphic_entry (UState.context_set uctx)), None) in
    let cb = Declare.ParameterEntry param in
    let cst = Declare.declare_constant ~name:id ~kind:(IsDefinition Definition) cb in
    (* Attach the axiom to the forcing implementation *)
    Lib.add_anonymous_leaf (in_translator [GlobRef.ConstRef cst, dref])))
  in
  let sigma, _ = Typing.type_of env sigma (EConstr.of_constr typ_) in
  let info = Declare.Info.make ~hook ~kind ~scope ~poly:false () in
  let cinfo = Declare.CInfo.make ~name:id_ ~typ:(EConstr.of_constr typ_) () in
  Declare.Proof.start ~cinfo ~info sigma 

(** Error handling *)

let _ = register_handler begin function
| FTranslate.MissingGlobal gr ->
  let ref = Nametab.shortest_qualid_of_global Id.Set.empty gr in
  Some (str "No forcing translation for global " ++ Libnames.pr_qualid ref ++ str ".")
| _ -> None
end
