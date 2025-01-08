module IT = IndexTerms
module BT = BaseTypes
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module TE = TypeErrors
module Loc = Locations
module LF = Definition.Function
module LC = LogicalConstraints
module IdSet = Set.Make (Id)
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)
module CI = Coq_ir

let fail msg details =
  let open Pp in
  print stdout (format [ Bold; Red ] msg ^^ colon ^^ space ^^ details);
  failwith msg


(* print the error message, but continue with a default value when possible *)
let fail_m rv loc msg =
  let err = TypeErrors.{ loc; msg = Generic msg } in
  Pp.error loc msg [];
  let () = upd (fun st -> { st with failures = err :: st.failures }) in
  return rv


let fail_m_d = fail_m !^"<error>"

let fail_m_o = fail_m None

(* release stored failures as exceptions *)
let release_failures () =
  let@ st = get in
  match st.failures with
  | [] -> return ()
  | fs -> fun _ -> Result.Error (List.hd (List.rev fs))

type list_mono = (BT.t * Sym.t) list

let add_list_mono_datatype (bt, nm) global =
  let open Global in
  let module Dt = BT.Datatype in
  let bt_name = Sym.pp_string (Option.get (BT.is_datatype_bt bt)) in
  let nil = Sym.fresh_named ("Nil_of_" ^ bt_name) in
  let cons = Sym.fresh_named ("Cons_of_" ^ bt_name) in
  let hd = Id.id ("hd_of_" ^ bt_name) in
  let tl = Id.id ("tl_of_" ^ bt_name) in
  let mems = [ (hd, bt); (tl, BT.Datatype nm) ] in
  let datatypes =
    Sym.Map.add nm Dt.{ constrs = [ nil; cons ]; all_params = mems } global.datatypes
  in
  let datatype_constrs =
    global.datatype_constrs
    |> Sym.Map.add nil Dt.{ params = []; datatype_tag = nm }
    |> Sym.Map.add cons Dt.{ params = mems; datatype_tag = nm }
  in
  { global with datatypes; datatype_constrs }


let mono_list_bt list_mono bt =
  Option.bind (BT.is_list_bt bt) (fun arg_bt ->
    Option.bind
      (List.find_opt (fun (bt2, _) -> BT.equal arg_bt bt2) list_mono)
      (fun (_, dt_sym) -> Some (BT.Datatype dt_sym)))

let monomorphise_dt_lists global =
  let dt_lists = function BT.List (BT.Datatype sym) -> Some sym | _ -> None in
  let module Dt = BT.Datatype in
  let all_dt_types =
    Sym.Map.fold
      (fun _ dt_info ss ->
        List.filter_map dt_lists (List.map snd dt_info.Dt.all_params) @ ss)
      global.Global.datatypes
      []
  in
  let uniq_dt_types = Sym.Set.elements (Sym.Set.of_list all_dt_types) in
  let new_sym sym = (sym, Sym.fresh_named ("list_of_" ^ Sym.pp_string sym)) in
  let new_syms = List.map new_sym uniq_dt_types in
  let list_mono = List.map (fun (s1, s2) -> (BT.Datatype s1, s2)) new_syms in
  let global = List.fold_right add_list_mono_datatype list_mono global in
  let map_bt bt = Option.value ~default:bt (mono_list_bt list_mono bt) in
  let map_mems = List.map (fun (nm, bt) -> (nm, map_bt bt)) in
  let datatypes =
    Sym.Map.map
      (fun info -> Dt.{ info with all_params = map_mems info.all_params })
      global.Global.datatypes
  in
  let datatype_constrs =
    Sym.Map.map
      (fun info -> Dt.{ info with params = map_mems info.params })
      global.Global.datatype_constrs
  in
  let global = Global.{ global with datatypes; datatype_constrs } in
  (list_mono, global)


(* Auxillary functions for printing things *)

let parse_directions directions = (directions, StringSet.singleton "all")

let header filename =
  let open Pp in
  !^"(*"
  ^^^ !^filename
  ^^ !^": generated lemma specifications from CN *)"
  ^^ hardline
  ^^ hardline
  ^^ !^"Require Import ZArith Bool."
  ^^ hardline
  ^^ !^"Require CN_Lemmas.CN_Lib."
  ^^ hardline
  ^^ hardline

let cmp_line_numbers = function
| None, None -> 0
| None, _ -> 1
| _, None -> -1
| Some (a, b), Some (c, d) ->
  let x = Int.compare a c in
  if x == 0 then Int.compare b d else x

let cmp_loc_line_numbers l1 l2 =
  cmp_line_numbers (Loc.line_numbers l1, Loc.line_numbers l2)

exception Cannot_Coerce
(* attempt to coerce out the resources in this function type.
   we can do this for some lemmas where resources are passed and
   returned unchanged as a way of passing their return values. *)
let try_coerce_res (ftyp : AT.lemmat) =
let rec erase_res r t =
  match t with
  | LRT.Define (v, info, t) -> LRT.Define (v, info, erase_res r t)
  | LRT.Constraint (lc, info, t) -> LRT.Constraint (lc, info, erase_res r t)
  | LRT.Resource ((name, (re, bt)), ((loc, _) as info), t) ->
    let arg_name, arg_re = r in
    if Request.alpha_equivalent arg_re re then (
      Pp.debug 2 (lazy (Pp.item "erasing" (Sym.pp name)));
      LRT.subst (IT.make_subst [ (name, IT.sym_ (arg_name, bt, loc)) ]) t)
    else
      LRT.Resource ((name, (re, bt)), info, erase_res r t)
  | LRT.I ->
    Pp.debug 2 (lazy (Pp.string "no counterpart found"));
    raise Cannot_Coerce (* did not find a matching resource *)
in
let erase_res2 r t =
  Pp.debug 2 (lazy (Pp.item "seeking to erase counterpart" (Sym.pp (fst r))));
  let res = LAT.map (erase_res r) t in
  res
in
let rec coerce_lat t =
  match t with
  | LAT.Resource ((name, (re, bt)), info, t) ->
    let computationals, t = coerce_lat (erase_res2 (name, re) t) in
    ((name, bt, info) :: computationals, t)
  | LAT.Define (v, info, t) ->
    let computationals, t = coerce_lat t in
    (computationals, LAT.Define (v, info, t))
  | LAT.Constraint (lc, info, t) ->
    let computationals, t = coerce_lat t in
    (computationals, LAT.Constraint (lc, info, t))
  | LAT.I _ -> ([], t)
in
let rec coerce_at t =
  match t with
  | AT.Computational (v, info, t) -> AT.Computational (v, info, coerce_at t)
  | AT.L t ->
    let computationals, t = coerce_lat t in
    AT.mComputationals computationals (AT.L t)
in
try Some (coerce_at ftyp) with Cannot_Coerce -> None

type scan_res =
{ res : string option;
  res_coerce : AT.lemmat option
}

let init_scan_res = { res = None; res_coerce = None }

(* recurse over a function type and detect resources (impureness),
   non-unit return types (non-lemma trusted functions), and the set
   of uninterpreted functions used. *)

let scan (ftyp : AT.lemmat) =
  let rec scan_lrt t =
    match t with
    | LRT.Define ((_, _it), _, t) -> scan_lrt t
    | LRT.Resource ((name, _), _, t) ->
      { (scan_lrt t) with res = Some (Sym.pp_string name) }
    | LRT.Constraint (_, _, t) -> scan_lrt t
    | LRT.I -> init_scan_res
  in
  let rec scan_lat t =
    match t with
    | LAT.Define (_, _, t) -> scan_lat t
    | LAT.Resource ((name, _), _, t) ->
      { (scan_lat t) with res = Some (Sym.pp_string name) }
    | LAT.Constraint (_, _, t) -> scan_lat t
    | LAT.I t -> scan_lrt t
  in
  let rec scan_at t =
    match t with AT.Computational (_, _, t) -> scan_at t | AT.L t -> scan_lat t
  in
  let x = scan_at ftyp in
  if Option.is_none x.res then
    x
  else (
    Pp.debug 2 (lazy (Pp.item "attempting to coerce ftyp" (Pp.string "")));
    match try_coerce_res ftyp with
    | None -> x
    | Some ftyp2 ->
      let y = scan_at ftyp2 in
      if Option.is_none y.res then (
        Pp.debug 2 (lazy (Pp.item "coercion" (Pp.string "succeeded")));
        { x with res_coerce = Some ftyp2 })
      else (
        Pp.debug 2 (lazy (Pp.item "coercion" (Pp.string "failed")));
        { x with res = y.res }))

(* coq_ir to prettyprint *)

let rec pat_to_coq_pp = function
| CI.Coq_pSym (CI.Coq_sym sym) -> return (Sym.pp sym)
| CI.Coq_pWild -> rets "_"
| CI.Coq_pConstructor (CI.Coq_sym c_nm, id_ps) ->
  (* assuming here that the id's are in canonical order *)
  parensM (build ([ return (Sym.pp c_nm) ] @ List.map pat_to_coq_pp id_ps))

let rec it_coq_pp loc global list_mono (t : CI.coq_term) =
  let open Pp in
  let enc_z z =
    if Z.leq Z.zero z then
      rets (Z.to_string z)
    else
      parensM (rets (Z.to_string z))
  in
  (* TODO: fix this for better error message *)
  let do_fail msg =
    fail_m_d loc (Pp.action ("it_to_coq: unsupported " ^ msg))
  in
  let aux t = it_coq_pp loc global list_mono t in
  let abinop s x y = parensM (build [ aux x ; rets s ; aux y ]) in
  match t with
  | CI.Coq_sym (CI.Coq_sym sym) -> return (Sym.pp sym)
  | CI.Coq_const c -> (match c with
    | CI.Coq_bool b -> (rets (if b then "true" else "false"))
    | CI.Coq_bool_prop b -> (rets (if b then "true" else "false"))
    | CI.Coq_Z z -> enc_z z
    | CI.Coq_bits (info, z) -> enc_z (BT.normalise_to_range info z))
  | CI.Coq_unop (op, x) -> (match op with
    | CI.Coq_neg -> f_appM "negb" [ aux x ]
    | CI.Coq_neg_prop -> f_appM "~" [ aux x ]
    | CI.Coq_BW_FFS_NoSMT -> f_appM "CN_Lib.find_first_set_z" [ aux x ]
    | CI.Coq_BW_CTZ_NoSMT -> f_appM "CN_Lib.count_trailing_zeroes_z" [ aux x ])
  | CI.Coq_binop (op, x, y) -> (match op with
    | CI.Coq_add -> abinop "+" x y
    | CI.Coq_sub -> abinop "-" x y
    | CI.Coq_mul -> abinop "*" x y
    | CI.Coq_div -> abinop "/" x y
    | CI.Coq_mod -> abinop "mod" x y
    (* TODO: This can't be right, thomas didn't figure it out either *)
    | CI.Coq_rem -> abinop "mod" x y
    | CI.Coq_lt -> abinop "<?" x y
    | CI.Coq_lt_prop -> abinop "<" x y
    | CI.Coq_le -> abinop "<=?" x y
    | CI.Coq_le_prop -> abinop "<=" x y
    | CI.Coq_exp -> abinop "^" x y
    | CI.Coq_lxor -> f_appM "Z.lxor" [ aux x; aux y ]
    | CI.Coq_land -> f_appM "Z.land" [ aux x; aux y ]
    | CI.Coq_lor -> f_appM "Z.lor" [ aux x; aux y ]
    | CI.Coq_eq -> parensM (build [ aux x; rets "=?"; aux y ])
    | CI.Coq_eq_prop -> parensM (build [ aux x; rets "="; aux y ])
    | CI.Coq_and -> abinop "&&" x y
    | CI.Coq_or -> abinop "||" x y
    | CI.Coq_impl -> abinop "implb" x y
    | CI.Coq_impl_prop -> abinop "->" x y)
  | CI.Coq_match (x, cases) ->
    let br (pat, rhs) = build [ rets "|"; pat_to_coq_pp pat; rets "=>"; aux rhs ] in
    parensM
      (build
         ([ rets "match"; aux x; rets "with" ] @ List.map br cases @ [ rets "end" ]))
  | CI.Coq_ite (sw, x, y) ->
    parensM (build [ rets "if"; aux sw; rets "then"; aux x; rets "else"; aux y ])
  | CI.Coq_mapset (m, x, y) -> 
    let@ () = ensure_fun_upd () in
    (* TODO: original code checks if x is BaseType integer. Do I really need to? *)
    f_appM "fun_upd" [ rets "Z.eqb"; aux m; aux x; aux y ]
  | CI.Coq_mapget (m, x) -> parensM (build [ aux m ; aux x] )
  | CI.Coq_recordmember (t, CI.Coq_id m) -> 
    let ix = find_tuple_element Id.equal m Id.pp (List.map fst t) in
    let@ op_nm = ensure_tuple_op false (Id.pp_string m) ix in
     parensM (build [ rets op_nm; aux t ])
    (*
    | IT.RecordMember (t, m) ->
      let flds = BT.record_bt (IT.bt t) in
      if List.length flds == 1 then
        aux t
      else (
        let ix = find_tuple_element Id.equal m Id.pp (List.map fst flds) in
        let@ op_nm = ensure_tuple_op false (Id.pp_string m) ix in
        parensM (build [ rets op_nm; aux t ]))
    | IT.RecordUpdate ((t, m), x) ->
      let flds = BT.record_bt (IT.bt t) in
      if List.length flds == 1 then
        aux x
      else (
        let ix = find_tuple_element Id.equal m Id.pp (List.map fst flds) in
        let@ op_nm = ensure_tuple_op true (Id.pp_string m) ix in
        parensM (build [ rets op_nm; aux t; aux x ]))
    | IT.Record mems ->
      let@ xs = ListM.mapM aux (List.map snd mems) in
      parensM (return (flow (comma ^^ break 1) xs))*)

  | _ -> do_fail "unsupported"
  
type scanned =
{ sym : Sym.t;
  loc : Loc.t;
  typ : AT.lemmat;
  scan_res : scan_res
}

let convert_and_print channel global list_mono conv =
  let conv_defs, types, params, defs = convert_lemma_defs global list_mono conv in
  let () = release_failures () in
  Pp.print channel (types_spec types);
  Pp.print channel (param_spec params);
  Pp.print channel (defs_module defs conv_defs);
  Pp.print channel (mod_spec (List.map (fun (nm, _, _, _) -> nm) conv));
  return ()

let generate (global : Global.t) directions (lemmata : (Sym.t * (Loc.t * AT.lemmat)) list)
=
(* let open Mu in *)
let filename, _kinds = parse_directions directions in
let channel = open_out filename in
Pp.print channel (header filename);
Pp.debug
  1
  (lazy
    (Pp.item "lemmata generation" (Pp.braces (Pp.list Sym.pp (List.map fst lemmata)))));
let scan_lemmata =
  List.map (fun (sym, (loc, typ)) -> { sym; loc; typ; scan_res = scan typ }) lemmata
  |> List.sort (fun x (y : scanned) -> cmp_loc_line_numbers x.loc y.loc)
in
let impure, pure =
  List.partition (fun x -> Option.is_some x.scan_res.res) scan_lemmata
in
let coerce, skip =
  List.partition (fun x -> Option.is_some x.scan_res.res_coerce) impure
in
List.iter
  (fun x ->
    Pp.progress_simple
      "skipping trusted fun with resource"
      (Sym.pp_string x.sym ^ ": " ^ Option.get x.scan_res.res))
  skip;
(* let fun_info = List.fold_right (fun (s, def) m -> Sym.Map.add s def m) *)
(*       mu_file.mu_logical_predicates Sym.Map.empty in *)
(* let struct_decls = get_struct_decls mu_file in *)
(* let global = Global.{ctxt.Context.global with struct_decls} in *)
let list_mono, global = monomorphise_dt_lists global in
(* let ci = {global; fun_info; list_mono} in *)
let conv =
  List.map (fun x -> (x.sym, x.typ, x.loc, "pure")) pure
  @ List.map
      (fun x -> (x.sym, Option.get x.scan_res.res_coerce, x.loc, "coerced"))
      coerce
in
match convert_and_print channel global list_mono conv init_t with
| Result.Ok _ -> Result.Ok ()
| Result.Error e -> Result.Error e