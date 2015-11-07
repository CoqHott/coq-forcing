open Errors
open Pp
open Util
open Names
open Term
open Decl_kinds
open Libobject
open Globnames
open Proofview.Notations

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string ("ᶠ" ^ id)

(** Record of translation between globals *)

let translator : FTranslate.translator ref =
  Summary.ref ~name:"Forcing Global Table" Refmap.empty

type translator_obj = (global_reference * global_reference) list

let cache_translator (_, l) =
  translator := List.fold_left (fun accu (src, dst) -> Refmap.add src dst accu) !translator l

let load_translator _ l = cache_translator l
let open_translator _ l = cache_translator l
let subst_translator (subst, l) =
  let map (src, dst) = (subst_global_reference subst src, subst_global_reference subst dst) in
  List.map map l

let in_translator : translator_obj -> obj =
  declare_object { (default_object "FORCING TRANSLATOR") with
    cache_function = cache_translator;
    load_function = load_translator;
    open_function = open_translator;
    discharge_function = (fun (_, o) -> Some o);
    classify_function = (fun o -> Substitute o);
  }

(** Tactic *)

let empty_translator = Refmap.empty

let force_tac cat c =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, ans) = FTranslate.translate !translator cat env sigma c in
    let sigma, _ = Typing.type_of env sigma ans in
    Proofview.Unsafe.tclEVARS sigma <*>
    Tactics.letin_tac None Names.Name.Anonymous ans None Locusops.allHyps
  end

let force_solve cat c =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, ans) = FTranslate.translate !translator cat env sigma c in
    msg_info (Termops.print_constr ans);
    let sigma, _ = Typing.type_of env sigma ans in
    Proofview.Unsafe.tclEVARS sigma <*>
    Proofview.Refine.refine_casted begin fun h -> (h, ans) end
  end

let force_translate_constant cat cst id =
  (** Translate the type *)
  let typ = Universes.unsafe_type_of_global (ConstRef cst) in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, typ) = FTranslate.translate_type !translator cat env sigma typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let uctx = Evd.evar_universe_context sigma in
  (** Define the term by tactic *)
  let body = Option.get (Global.body_of_constant cst) in
  let (sigma, body) = FTranslate.translate !translator cat env sigma body in
  let evdref = ref sigma in
  let () = Typing.check env evdref body typ in
  let sigma = !evdref in
  let (_, uctx) = Evd.universe_context sigma in
  let ce = Declare.definition_entry ~types:typ ~univs:uctx body in
  let cd = Entries.DefinitionEntry ce in
  let decl = (cd, IsProof Lemma) in
  let cst = Declare.declare_constant id decl in
  ConstRef cst

let force_translate_inductive cat ind =
  (** From a kernel inductive body construct an entry for the inductive. There
      are slight mismatches in the representation, in particular in the handling
      of contexts. See {!Declarations} and {!Entries}. *)
  let open Declarations in
  let open Entries in
  let env = Global.env () in
  let (mib, _) = Global.lookup_inductive ind in
  (** For each block in the inductive we build the translation *)
  let make_one_entry body (sigma, bodies_) =
    let template = match body.mind_arity with
    | RegularArity _ -> false
    | TemplateArity _ -> true
    in
    (** Heuristic for the return type. Can we do better? *)
    let (sigma, s) =
      if List.mem Sorts.InType body.mind_kelim then Evarutil.new_Type env sigma
      else (sigma, mkProp)
    in
    let (sigma, arity) =
      let nindexes = List.length body.mind_arity_ctxt - List.length mib.mind_params_ctxt in
      let ctx = List.firstn nindexes body.mind_arity_ctxt in
      let env' = Environ.push_rel_context mib.mind_params_ctxt env in
      let a = it_mkProd_or_LetIn s ctx in
      FTranslate.translate_type ~toplevel:false !translator cat env' sigma a
    in
    let fold_lc typ (sigma, lc_) =
      (** We exploit the fact that the translation actually does not depend on
          the rel_context of the environment except for its length. *)
      let self = List.init (Array.length mib.mind_packets) (fun _ -> (Name.Anonymous, None, mkProp)) in
      let env' = Environ.push_rel_context self env in
      let (sigma, typ_) = FTranslate.translate_type ~toplevel:false ~lift:1 !translator cat env' sigma typ in
      (** The translation assumes that the first introduced variable is the
          toplevel forcing condition, which is not the case here. *)
      (sigma, typ_ :: lc_)
    in
    let (sigma, lc_) = Array.fold_right fold_lc body.mind_user_lc (sigma, []) in
    let body_ = {
      mind_entry_typename = translate_name body.mind_typename;
      mind_entry_arity = arity;
      mind_entry_template = template;
      mind_entry_consnames = CArray.map_to_list translate_name body.mind_consnames;
      mind_entry_lc = lc_;
    } in
    (sigma, body_ :: bodies_)
  in
  (** We proceed to the whole mutual block *)
  let record = match mib.mind_record with
  | None -> None
  | Some None -> Some None
  | Some (Some (id, _, _)) -> Some (Some (translate_name id))
  in
  let sigma = Evd.from_env env in
  let (sigma, params_) = FTranslate.translate_context !translator cat env sigma mib.mind_params_ctxt in
  let (sigma, bodies_) = Array.fold_right make_one_entry mib.mind_packets (sigma, []) in
  let debug b =
    msg_info (Nameops.pr_id b.mind_entry_typename ++ str " : " ++ Termops.print_constr (it_mkProd_or_LetIn b.mind_entry_arity params_));
    let cs = List.combine b.mind_entry_consnames b.mind_entry_lc in
    let pr_constructor (id, tpe) =
      msg_info (Nameops.pr_id id ++ str " : " ++ Termops.print_constr tpe)
    in
    List.iter pr_constructor cs
  in
  List.iter debug bodies_;
  let make_param = function
  | (na, None, t) -> (Nameops.out_name na, LocalAssum t)
  | (na, Some body, _) -> (Nameops.out_name na, LocalDef body)
  in
  let params_ = List.map make_param params_ in
  let (_, uctx) = Evd.universe_context sigma in
  let mib_ = {
    mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params_;
    mind_entry_inds = bodies_;
    mind_entry_polymorphic = mib.mind_polymorphic;
    mind_entry_universes = uctx;
    mind_entry_private = mib.mind_private;
  } in
  let (_, kn), _ = Declare.declare_mind mib_ in
  let mib_ = Global.mind_of_delta_kn kn in
  IndRef (mib_, snd ind)

let force_translate (obj, hom) gr idopt =
  let r = gr in
  let gr = Nametab.global gr in
  let obj = Universes.constr_of_global (Nametab.global obj) in
  let hom = Universes.constr_of_global (Nametab.global hom) in
  let cat = {
    FTranslate.cat_obj = obj;
    FTranslate.cat_hom = hom;
  } in
  let id = match idopt with
  | None -> translate_name (Nametab.basename_of_global gr)
  | Some id -> id
  in
  let ans = match gr with
  | ConstRef cst -> force_translate_constant cat cst id
  | IndRef ind -> force_translate_inductive cat ind
  | _ -> error "Translation not handled."
  in
  let () = Lib.add_anonymous_leaf (in_translator [gr, ans]) in
  let () = Pp.msg_info (str "Global " ++ Libnames.pr_reference r ++
    str " has been translated as " ++ Nameops.pr_id id ++ str ".")
  in
  ()

(** Error handling *)

let _ = register_handler begin function
| FTranslate.MissingGlobal gr ->
  let ref = Nametab.shortest_qualid_of_global Id.Set.empty gr in
  str "No forcing translation for global " ++ Libnames.pr_qualid ref ++ str "."
| _ -> raise Unhandled
end
