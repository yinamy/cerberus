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

(* Generating the boilerplate parts of the Coq file *)
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

(* Scan stuff *)
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

type scanned =
  { sym : Sym.t;
    loc : Loc.t;
    typ : AT.lemmat;
    scan_res : scan_res
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

(* Line numbers stuff *)
let cmp_line_numbers = function
  | None, None -> 0
  | None, _ -> 1
  | _, None -> -1
  | Some (a, b), Some (c, d) ->
    let x = Int.compare a c in
    if x == 0 then Int.compare b d else x

let cmp_loc_line_numbers l1 l2 =
  cmp_line_numbers (Loc.line_numbers l1, Loc.line_numbers l2)


(* Monomorphisation of list data types *)
type list_mono = (BT.t * Sym.t) list

let add_list_mono_datatype (bt, nm) global =
  let open Global in
  let module Dt = BT.Datatype in
  let bt_name = Sym.pp_string (Option.get (BT.is_datatype_bt bt)) in
  let nil = Sym.fresh_named ("Nil_of_" ^ bt_name) in
  let cons = Sym.fresh_named ("Cons_of_" ^ bt_name) in
  let here = Locations.other __LOC__ in
  let hd = Id.make here ("hd_of_" ^ bt_name) in
  let tl = Id.make here ("tl_of_" ^ bt_name) in
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

(* Conversion to Coq *)

let binop s x y =
  let open Pp in
  parens (flow (break 1) [ x; !^s; y ])

let rec new_nm s nms i =
  let s2 = s ^ "_" ^ Int.to_string i in
  if List.exists (String.equal s2) nms then
    new_nm s nms (i + 1)
  else
    s2

let alpha_rename_if_pp_same s body =
  let vs = IT.free_vars body in
  let other_nms =
    List.filter (fun sym -> not (Sym.equal sym s)) (Sym.Set.elements vs)
    |> List.map Sym.pp_string
  in
  if List.exists (String.equal (Sym.pp_string s)) other_nms then (
    Pp.debug
      6
      (lazy
        (Pp.item
           "doing rename"
           (Pp.typ (Sym.pp s) (Pp.braces (Pp.list Pp.string other_nms)))));
    let s2 = Sym.fresh_named (new_nm (Sym.pp_string s) other_nms 0) in
    let body = IT.subst (IT.make_rename ~from:s ~to_:s2) body in
    (s2, body, IT.free_vars body))
  else
    (s, body, vs)

let it_adjust (global : Global.t) it =
  let rec f t =
    let loc = IT.get_loc t in
    match IT.get_term t with
    | IT.Binop (And, x1, x2) ->
      let xs = List.map f [ x1; x2 ] |> List.partition IT.is_true |> snd in
      IT.and_ xs loc
    | IT.Binop (Or, x1, x2) ->
      let xs = List.map f [ x1; x2 ] |> List.partition IT.is_false |> snd in
      IT.or_ xs loc
    | IT.Binop (EQ, x, y) ->
      let x = f x in
      let y = f y in
      if IT.equal x y then IT.bool_ true loc else IT.eq__ x y loc
    | IT.Binop (Implies, x, y) ->
      let x = f x in
      let y = f y in
      if IT.is_false x || IT.is_true y then IT.bool_ true loc else IT.impl_ (x, y) loc
    | IT.EachI ((i1, (s, bt), i2), x) ->
      let x = f x in
      let s, x, vs = alpha_rename_if_pp_same s x in
      if not (Sym.Set.mem s vs) then (
        assert (i1 <= i2);
        x)
      else
        IT.eachI_ (i1, (s, bt), i2) x loc
    | IT.Apply (name, args) ->
      let open Definition.Function in
      let def = Sym.Map.find name global.logical_functions in
      (match (def.body, def.emit_coq) with
       | Def body, false -> f (open_ def.args body args)
       | _ -> t)
    | IT.Good (ct, t2) ->
      if Option.is_some (Sctypes.is_struct_ctype ct) then
        t
      else
        f (IT.good_value global.struct_decls ct t2 loc)
    | Representable (ct, t2) ->
      if Option.is_some (Sctypes.is_struct_ctype ct) then
        t
      else
        f (IT.representable global.struct_decls ct t2 loc)
    | Aligned t -> f (IT.divisible_ (IT.addr_ t.t loc, t.align) loc)
    | IT.Let ((nm, x), y) ->
      let x = f x in
      let y = f y in
      let nm, y, vs = alpha_rename_if_pp_same nm y in
      if Option.is_some (IT.is_sym x) then
        IT.subst (IT.make_subst [ (nm, x) ]) y
      else if not (Sym.Set.mem nm vs) then
        y
      else
        IT.let_ ((nm, x), y) loc
    | _ -> t
  in
  let res = f it in
  Pp.debug 9 (lazy (Pp.item "it_adjust" (binop "->" (IT.pp it) (IT.pp res))));
  f it

let lc_to_coq_check_triv loc global list_mono = function
  | LC.T it ->
    let it = it_adjust global it in
    if IT.is_true it then
      None
    else
      let v = it_to_coq loc global list_mono it in
      (Some v)
  | LC.Forall ((sym, bt), it) ->
    let it = it_adjust global it in
    if IT.is_true it then
      None
    else
      let v = it_to_coq loc global list_mono it in
      let enc = mk_forall global list_mono loc sym bt v in
      (Some (Pp.parens enc))

let ftyp_to_coq loc global list_mono (ftyp : AT.lemmat) =
  let open Pp in
  (* First, convert *)
  let lc_to_coq_c = lc_to_coq_check_triv loc global list_mono in
  let it_tc = it_to_coq loc global list_mono in
  (* FIXME: handle underdefinition in division *)
  let oapp f opt_x y = match opt_x with Some x -> f x y | None -> y in
  let mk_and doc doc2 = doc ^^^ !^"/\\" ^^^ doc2 in
  let mk_imp doc doc2 = doc ^^^ !^"->" ^^^ doc2 in
  let omap_split f = Option.map (fun doc -> f (break 1 ^^ doc)) in
  let rec lrt_doc t =
    match t with
    | LRT.Constraint (lc, _, t) ->
      let@ d = lrt_doc t in
      let@ c = lc_to_coq_c lc in
      (match (d, c) with
       | None, _ -> return c
       | _, None -> return d
       | Some dd, Some cd -> return (Some (mk_and cd dd)))
    | LRT.Define ((sym, it), _, t) ->
      let@ d = lrt_doc t in
      let@ l = it_tc it in
      return (omap_split (mk_let sym l) d)
    | LRT.I -> return None
    | _ -> fail_m_o loc (Pp.item "ftyp_to_coq: unsupported" (LRT.pp t))
  in
  let rec lat_doc t =
    match t with
    | LAT.Define ((sym, it), _, t) ->
      let@ d = lat_doc t in
      let@ l = it_tc it in
      return (omap_split (mk_let sym l) d)
    | LAT.Resource _ ->
      fail_m_o loc (Pp.item "ftyp_to_coq: unsupported" (LAT.pp LRT.pp t))
    | LAT.Constraint (lc, _, t) ->
      let@ c = lc_to_coq_c lc in
      let@ d = lat_doc t in
      return (omap_split (oapp mk_imp c) d)
    | LAT.I t -> lrt_doc t
  in
  let rec at_doc t =
    match t with
    | AT.Computational ((sym, bt), _, t) ->
      let@ d = at_doc t in
      (match d with
       | None -> return None
       | Some doc ->
         let@ doc2 = mk_forall global list_mono loc sym bt (break 1 ^^ doc) in
         return (Some doc2))
    | AT.L t -> lat_doc t
  in
  let@ d = at_doc ftyp in
  match d with Some doc -> return doc | None -> rets "Is_true true"

(* CN to my coq ir *)  
let ftyp_to_coq2 loc global list_mono (ftyp : AT.lemmat) =
  let open Pp in
  (* First, convert *)
  let lc_to_coq_c = lc_to_coq_check_triv loc global list_mono in
  let it_tc = it_to_coq loc global list_mono in
  (* FIXME: handle underdefinition in division *)
  let oapp f opt_x y = match opt_x with Some x -> f x y | None -> y in
  let mk_and doc doc2 = doc ^^^ !^"/\\" ^^^ doc2 in
  let mk_imp doc doc2 = doc ^^^ !^"->" ^^^ doc2 in
  let omap_split f = Option.map (fun doc -> f (break 1 ^^ doc)) in
  let rec lrt_doc t =
    match t with
    | LRT.Constraint (lc, _, t) ->
      let@ d = lrt_doc t in
      let@ c = lc_to_coq_c lc in
      (match (d, c) with
       | None, _ -> return c
       | _, None -> return d
       | Some dd, Some cd -> return (Some (mk_and cd dd)))
    | LRT.Define ((sym, it), _, t) ->
      let@ d = lrt_doc t in
      let@ l = it_tc it in
      return (omap_split (mk_let sym l) d)
    | LRT.I -> return None
    | _ -> fail_m_o loc (Pp.item "ftyp_to_coq: unsupported" (LRT.pp t))
  in
  let rec lat_doc t =
    match t with
    | LAT.Define ((sym, it), _, t) ->
      let d = lat_doc t in
      let l = it_tc it in
      (omap_split (mk_let sym l) d)
    | LAT.Resource _ ->
      fail_m_o loc (Pp.item "ftyp_to_coq: unsupported" (LAT.pp LRT.pp t))
    | LAT.Constraint (lc, _, t) ->
      let c = lc_to_coq_c lc in
      let d = lat_doc t in
      (omap_split (oapp mk_imp c) d)
    | LAT.I t -> lrt_doc t
  in
  let rec at_doc t =
    match t with
    | AT.Computational ((sym, bt), _, t) ->
      let d = at_doc t in
      (match d with
       | None -> None
       | Some doc ->
        (* TODO: probably missed something here with the doc will revisit *)
         let doc2 = CI.Coq_forall (CI.Coq_sym sym, t) 
        (Some doc2))
    | AT.L t -> lat_doc t
  in
  let@ d = at_doc ftyp in
  match d with Some doc -> return doc | None -> rets "Is_true true"



let convert_lemma_defs global list_mono lemma_typs =
  let lemma_ty (nm, (typ : AT.lemmat), loc, kind) =
    Pp.progress_simple ("converting " ^ kind ^ " lemma type") (Sym.pp_string nm);
    let rhs = ftyp_to_coq loc global list_mono typ in
    return (defn (Sym.pp_string nm ^ "_type") [] (Some (Pp.string "Prop")) rhs)
  in
  let tys = ListM.mapM lemma_ty lemma_typs in
  let st = get in
  Pp.debug
    4
    (lazy
      (Pp.item
         "saved conversion elements"
         (Pp.list
            (fun (ss, _) -> Pp.parens (Pp.list Pp.string ss))
            (StringListMap.bindings st.present))));
  return
    ( tys,
      List.rev (get_section 0 st),
      List.rev (get_section 1 st),
      List.rev (get_section 2 st) )

let convert_and_print channel global list_mono conv =
  let conv_defs, types, params, defs = convert_lemma_defs global list_mono conv in
  (*let () = release_failures () in
  Pp.print channel (types_spec types);
  Pp.print channel (param_spec params);
  Pp.print channel (defs_module defs conv_defs);
  Pp.print channel (mod_spec (List.map (fun (nm, _, _, _) -> nm) conv));
  return ()*)

(* Main function *)
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
