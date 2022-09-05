module CF = Cerb_frontend
module IT = IndexTerms


(* moving Kayvan's originally compilePredicates.ml environment definitions over here *)


module SymMap = Map.Make(Sym)
module Y = Map.Make(String)

open Resultat


type function_sig = {
    args: (Sym.t * BaseTypes.t) list;
    return_bty: BaseTypes.t;
  }

type predicate_sig = {
  pred_iargs: (Sym.t * BaseTypes.t) list;
  pred_oargs: (Sym.t * BaseTypes.t) list;
}

type resource_def =
  | RPred_owned of Sctypes.t
  | RPred_block of Sctypes.t
  | RPred_named of Sym.t
  | RPred_I_owned of Sctypes.t
  | RPred_I_block of Sctypes.t
  | RPred_I_named of Sym.t

type t = {
  logicals: BaseTypes.t SymMap.t;
  pred_names: Sym.t Y.t;
  predicates: predicate_sig SymMap.t;
  func_names: Sym.t Y.t;
  functions: function_sig SymMap.t;
  resources: resource_def SymMap.t;
  datatypes : BaseTypes.datatype_info SymMap.t;
  datatype_names : Sym.t Y.t;
  datatype_constrs : BaseTypes.constr_info SymMap.t;
  datatype_constr_names : (Sym.t * Sym.t Y.t) Y.t;
  tagDefs: CF.Core_to_mucore.Mu.mu_tag_definitions;
}

let empty tagDefs =
  { logicals= SymMap.empty; pred_names= Y.empty; predicates= SymMap.empty;
    func_names = Y.empty; functions = SymMap.empty; resources= SymMap.empty;
    datatypes = SymMap.empty; datatype_names = Y.empty;
    datatype_constrs = SymMap.empty; datatype_constr_names = Y.empty;
    tagDefs; }

let name_to_sym loc nm m = match Y.find_opt nm m with
  | None ->
    let sym = Sym.fresh_named nm in
    return sym
  | Some _ ->
    let open TypeErrors in
    fail {loc; msg = Generic (Pp.string ("redefinition of name: " ^ nm))}

let add_logical sym bTy env =
  {env with logicals= SymMap.add sym bTy env.logicals }

let add_function loc sym func_sig env =
  (* upstream of this an incorrect string->sym conversion was done *)
  let str = Sym.pp_string sym in
  let@ _ = name_to_sym loc str env.func_names in
  return {env with functions= SymMap.add sym func_sig env.functions;
    func_names = Y.add str sym env.func_names }

let add_predicate sym pred_sig env =
  {env with predicates= SymMap.add sym pred_sig env.predicates }

let add_resource sym res_def env =
  { env with resources= SymMap.add sym res_def env.resources }

let lookup_logical sym env =
  SymMap.find_opt sym env.logicals

let lookup_pred_name str env =
  Y.find_opt str env.pred_names

let lookup_predicate sym env =
  SymMap.find_opt sym env.predicates

let lookup_function sym env =
  SymMap.find_opt sym env.functions

let lookup_function_by_name nm env = match Y.find_opt nm env.func_names with
  | Some sym ->
    SymMap.find_opt sym env.functions |> Option.map (fun fs -> (sym, fs))
  | None -> None

let lookup_resource sym env =
  SymMap.find_opt sym env.resources

let lookup_struct sym env =
  match Pmap.lookup sym env.tagDefs with
    | Some (M_StructDef xs) ->
        Some xs
    | Some (M_UnionDef _)| None ->
        None

let lookup_datatype_info sym env = SymMap.find_opt sym env.datatypes

let add_datatype_name id env =
  let@ sym = name_to_sym (Id.loc id) (Id.s id) env.datatype_names in
  let datatype_names = Y.add (Id.s id) sym env.datatype_names in
  return (sym, {env with datatype_names})

let add_datatype sym info env =
  let datatypes = SymMap.add sym info env.datatypes in
  {env with datatypes}

let lookup_constr id env = match Y.find_opt (Id.s id) env.datatype_constr_names with
  | Some (sym, mem_syms) -> return (sym, mem_syms, SymMap.find sym env.datatype_constrs)
  | None -> fail (TypeErrors.{loc = Id.loc id; msg =
        TypeErrors.Unknown_datatype_constr (Sym.fresh_named (Id.s id))})

let add_datatype_constr id mem_syms info env =
  let@ sym = name_to_sym (Id.loc id) (Id.s id) env.datatype_constr_names in
  let datatype_constr_names = Y.add (Id.s id) (sym, mem_syms) env.datatype_constr_names in
  let datatype_constrs = SymMap.add sym info env.datatype_constrs in
  return (sym, {env with datatype_constrs; datatype_constr_names})

let get_datatype_maps env =
  (SymMap.bindings env.datatypes, SymMap.bindings env.datatype_constrs)


let debug_known_preds env =
  Pp.debug 2 (lazy (Pp.item "known logical predicates"
      (Pp.list (fun (nm, _) -> Pp.string nm) (Y.bindings env.func_names))));
  Pp.debug 2 (lazy (Pp.item "known resource predicate names"
      (Pp.list (fun (nm, _) -> Pp.string nm) (Y.bindings env.pred_names))))





