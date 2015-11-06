open Errors
open Pp
open Names
open Term
open Decl_kinds
open Libobject
open Globnames
open Proofview.Notations

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string ("ℱ" ^ id)

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
    Proofview.Unsafe.tclEVARS sigma <*>
    Tactics.letin_tac None Names.Name.Anonymous ans None Locusops.allHyps
  end

let force_solve cat c =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, ans) = FTranslate.translate !translator cat env sigma c in
    msg_info (Termops.print_constr ans);
    Proofview.Unsafe.tclEVARS sigma <*>
    Proofview.Refine.refine_casted begin fun h -> (h, ans) end
  end

let force_translate_constant cat cst id uctx typ =
  let body = Option.get (Global.body_of_constant cst) in
  let tac = force_solve cat body in
  let sign = Environ.empty_named_context_val in
  let (const, safe, uctx) = Pfedit.build_constant_by_tactic id uctx sign typ tac in
  let cd = Entries.DefinitionEntry const in
  let decl = (cd, IsProof Lemma) in
  let cst = Declare.declare_constant id decl in
  ConstRef cst

let force_translate (obj, hom) gr idopt =
  let r = gr in
  let gr = Nametab.global gr in
  let obj = Universes.constr_of_global (Nametab.global obj) in
  let hom = Universes.constr_of_global (Nametab.global hom) in
  let cat = {
    FTranslate.cat_obj = obj;
    FTranslate.cat_hom = hom;
  } in
  (** Translate the type *)
  let sigma = Evd.empty in
  let typ = Universes.unsafe_type_of_global gr in
  let env = Global.env () in
  let (sigma, typ) = FTranslate.translate_type !translator cat env sigma typ in
  let uctx = Evd.evar_universe_context sigma in
  (** Define the term by tactic *)
  let id = match idopt with
  | None -> translate_name (Nametab.basename_of_global gr)
  | Some id -> id
  in
  let ans = match gr with
  | ConstRef cst -> force_translate_constant cat cst id uctx typ
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
