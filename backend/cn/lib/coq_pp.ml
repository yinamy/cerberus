module BT = BaseTypes
module AT = ArgumentTypes
module Loc = Locations
module StringSet = Set.Make (String)
module CI = Coq_ir
module CC = Cn_to_coq

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

let types_spec types =
  let open Pp in
  !^"Module Types."
  ^^ hardline
  ^^ hardline
  ^^ (if List.length types == 0 then
        !^"  (* no type definitions required *)" ^^ hardline
      else
        flow hardline types)
  ^^ hardline
  ^^ !^"End Types."
  ^^ hardline
  ^^ hardline

let defs_module aux_defs lemma_tys =
  let open Pp in
  !^"Module Defs (P : Parameters)."
  ^^ hardline
  ^^ hardline
  ^^ !^"  Import Types P."
  ^^ hardline
  ^^ !^"  Open Scope Z."
  ^^ hardline
  ^^ hardline
  ^^ flow hardline aux_defs
  ^^ hardline
  ^^ flow hardline lemma_tys
  ^^ hardline
  ^^ !^"End Defs."
  ^^ hardline
  ^^ hardline

let mod_spec lemma_nms =
  let open Pp in
  let lemma nm =
    !^"  Parameter" ^^^ typ (Sym.pp nm) (Sym.pp nm ^^ !^"_type") ^^ !^"." ^^ hardline
  in
  !^"Module Type Lemma_Spec (P : Parameters)."
  ^^ hardline
  ^^ hardline
  ^^ !^"  Module D := Defs(P)."
  ^^ hardline
  ^^ !^"  Import D."
  ^^ hardline
  ^^ hardline
  ^^ flow hardline (List.map lemma lemma_nms)
  ^^ hardline
  ^^ !^"End Lemma_Spec."
  ^^ hardline
  ^^ hardline

let fail msg details =
  let open Pp in
  print stdout (format [ Bold; Red ] msg ^^ colon ^^ space ^^ details);
  failwith msg  

let build = function
  | [] -> fail "build" (Pp.string "empty")
  | xs ->
    let docs = List.map (fun x -> x) xs in
    (Pp.flow (Pp.break 1) docs)

let parensM x = (Pp.parens x)

let rets s = Pp.string s

let enc_z z =
  if Z.leq Z.zero z then
    rets (Z.to_string z)
  else
    parensM (rets (Z.to_string z))

let f_appM nm xs = parensM (build (rets nm :: xs))

let defn nm args opt_ty rhs =
  let open Pp in
  let tyeq = match opt_ty with None -> [] | Some ty -> [ colon; ty ] in
  flow (break 1) ([ !^"  Definition"; !^nm ] @ args @ tyeq @ [ !^":=" ])
  ^^ hardline
  ^^ !^"    "
  ^^ rhs
  ^^ !^"."
  ^^ hardline

let norm_bv_op bt doc_f =
  match bt with
  | BT.Bits (sign, sz) ->
    let minInt, maxInt = BT.bits_range (sign, sz) in
    f_appM "CN_Lib.wrapI" [ enc_z minInt; enc_z maxInt; doc_f ]
  | _ -> doc_f

let binop s x y =
  let open Pp in
  parens (flow (break 1) [ x; !^s; y ])

let tuple_coq_ty doc fld_tys =
  let open Pp in
  let rec stars = function
    | [] -> fail "tuple_coq_ty: empty" doc
    | [ x ] -> [ x ]
    | x :: xs -> x :: star :: stars xs
  in
  parens (flow (break 1) (stars fld_tys))  

let rec bt_to_coq (bt : CI.coq_bt) =
  let open Pp in
  match bt with
  | CI.Coq_Bool -> !^"bool"
  | CI.Coq_Integer -> !^"Z"
  | CI.Coq_Bits -> !^"Z"
  | CI.Coq_Map (x, y) ->
    let enc_x = bt_to_coq x in
    let enc_y = bt_to_coq y in
    (parens (binop "->" enc_x enc_y))
  | CI.Coq_Struct (CI.Coq_sym tag, fld_bts) ->
    let enc_fld_bts = List.map bt_to_coq fld_bts in
    (tuple_coq_ty (Sym.pp tag) enc_fld_bts)
  | CI.Coq_Record mems ->
    let enc_mem_bts = List.map bt_to_coq mems in
    (tuple_coq_ty !^"record" enc_mem_bts)
  | CI.Coq_Loc -> !^"CN_Lib.Loc"
  (* todo: probably not right *)
  | CI.Coq_Datatype (CI.Coq_sym tag) ->
    (*let p = pp_datatype gl tag in
    parensM (build ([ (Sym.pp tag) ] @ [ p ] ))*)
    Sym.pp tag
  (* todo: probably not right either*)
  | CI.Coq_List _bt2 -> bt_to_coq _bt2
  | _ -> Pp.string "unsupported_basetype"

let pp_let sym rhs_doc doc =
  let open Pp in
  !^"let" ^^^ Sym.pp sym ^^^ !^":=" ^^^ rhs_doc ^^^ !^"in" ^^^ doc

let pp_forall sym bt doc =
  let open Pp in
  let coq_bt = bt_to_coq bt in
  (!^"forall" ^^^ parens (typ (Sym.pp sym) coq_bt) ^^ !^"," ^^ break 1 ^^ doc)

let rec pat_to_coq (pat : CI.coq_pat) = match pat with
  | Coq_pSym (Coq_sym sym) -> (Sym.pp sym)
  | Coq_pWild -> rets "_"
  | Coq_pConstructor (Coq_sym s, l) -> 
      parensM (build ([ (Sym.pp s) ] @ List.map pat_to_coq l))

let lemma_to_coq global (t : CI.coq_term) = 
  let open Pp in
  let rec f global t = 
    let aux t = f global t in
    let abinop s x y = parensM (build [ aux x; rets s; aux y ]) in
    let map_split f = (fun doc -> f (break 1 ^^ doc)) in
    let mk_and doc doc2 = doc ^^^ !^"/\\" ^^^ doc2 in
    let mk_imp doc doc2 = doc ^^^ !^"->" ^^^ doc2 in
  (match t with
  | CI.Coq_sym (CI.Coq_sym s) -> Sym.pp s
  | Coq_const c -> (match c with
    | Coq_bool b -> (rets (if b then "true" else "false"))
    | Coq_bool_prop b -> f_appM "Is_true" [ (rets (if b then "true" else "false")) ]
    | Coq_Z z -> parensM (rets (Z.to_string z))
    | Coq_bits z -> parensM (rets (Z.to_string z)))
  | Coq_unop (op, x) -> (match op with
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
    (* todo: defo not right, find out correct translation*)
    | CI.Coq_rem -> abinop "mod" x y
    | CI.Coq_lt -> abinop "<?" x y
    | CI.Coq_lt_prop -> abinop "<" x y
    | CI.Coq_le -> abinop "<=?" x y
    | CI.Coq_le_prop -> abinop "<=" x y
    | CI.Coq_exp -> abinop "^" x y
    | CI.Coq_bwxor -> f_appM "Z.lxor" [ aux x; aux y ]
    | CI.Coq_bwand -> f_appM "Z.land" [ aux x; aux y ]
    | CI.Coq_bwor -> f_appM "Z.lor" [ aux x; aux y ]
    | CI.Coq_eq -> parensM (build [ aux x; rets "=?"; aux y ])
    | CI.Coq_eq_prop -> parensM (build [ aux x; rets "="; aux y ])
    | CI.Coq_and -> abinop "&&" x y
    | CI.Coq_and_prop -> abinop "/\\" x y
    | CI.Coq_or -> abinop "||" x y
    | CI.Coq_or_prop -> abinop "\\/" x y
    | CI.Coq_impl -> abinop "implb" x y
    | CI.Coq_impl_prop -> abinop "->" x y)
  | CI.Coq_match (x, cases) -> let br (pat, rhs) = 
      build [ rets "|"; pat_to_coq pat; rets "=>"; aux rhs ] in
        parensM
          (build
            ([ rets "match"; aux x; rets "with" ] @ List.map br cases @ [ rets "end" ]))
  | CI.Coq_ite (sw, x, y) -> 
      parensM (build [ rets "if"; aux sw; rets "then"; aux x; rets "else"; aux y ])
  | CI.Coq_eachI ((i1, (CI.Coq_sym s, _), i2), x) -> 
      let enc = pp_forall s CI.Coq_Integer (binop
        "->"
        (binop
          "/\\"
          (binop "<=" (Pp.int i1) (Sym.pp s))
          (binop "<=" (Sym.pp s) (Pp.int i2)))
        (aux x)) in
      (parens enc)
  | CI.Coq_mapset (m,x,y) -> f_appM "fun_upd" [ rets "Z.eqb"; aux m; aux x; aux y ]
  | CI.Coq_mapget (m, x) -> parensM (build [ aux m; aux x ])
  | CI.Coq_recordmember (t, CI.Coq_id nm) -> 
      let op_nm = "get_" ^ (Id.get_string nm) in
      parensM (build [ rets op_nm; aux t ])
  | CI.Coq_recordupdate ((t, CI.Coq_id nm), x) -> 
      let op_nm = "upd_" ^ (Id.get_string nm) in
      parensM (build [ rets op_nm; aux t; aux x ])
  | CI.Coq_record l -> 
      let xs = List.map aux l in
      parensM ((flow (comma ^^ break 1) xs))
  | CI.Coq_structmember (t, CI.Coq_id nm) ->
      let op_nm = "get_" ^ (Id.get_string nm) in
      parensM (build [ rets op_nm; aux t ])
  | CI.Coq_structupdate ((t, CI.Coq_id nm), x) -> 
      let op_nm = "upd_" ^ (Id.get_string nm) in
      parensM (build [ rets op_nm; aux t; aux x ])
  | CI.Coq_cast (_, x) -> aux x
  | CI.Coq_app_uninterp (CI.Coq_sym name, _, args, _) -> 
    let r = parensM (build ([ (Sym.pp name) ] @ List.map aux args)) in
    (*let coq_arg_typs = List.map (fun (_, bt) -> bt_to_coq global bt) arg_typs in
    let coq_rt = bt_to_coq global ret_typ in
    let ty = List.fold_right (fun at rt -> at ^^^ !^"->" ^^^ rt) coq_arg_typs coq_rt in
    let preamble = (!^"  Parameter" ^^^ typ (Sym.pp name) ty ^^ !^"." ^^ hardline) in
    build [preamble ; r]*)
    build [r]
  | CI.Coq_app_uninterp_prop (CI.Coq_sym name, _, args) -> 
    let r = parensM (build ([ (Sym.pp name) ] @ List.map aux args)) in
    (*let coq_arg_typs = List.map (fun (_, bt) -> bt_to_coq global bt) arg_typs in
    let coq_rt = !^"Prop" in
    let ty = List.fold_right (fun at rt -> at ^^^ !^"->" ^^^ rt) coq_arg_typs coq_rt in
    let preamble = (!^"  Parameter" ^^^ typ (Sym.pp name) ty ^^ !^"." ^^ hardline) in
    build [preamble ; r]*)
    build [r]
  | CI.Coq_app_def (CI.Coq_sym name, _, _, args) -> 
    let r = parensM (build ([ (Sym.pp name) ] @ List.map aux args)) in
    r
    (*let coq_body = aux body in
    let coq_args =
      List.map
        (fun (arg, bt) ->
          let coq_bt = bt_to_coq global bt in
          (Pp.parens (Pp.typ (aux arg) coq_bt)))
        arg_typs in
    build [ (defn (Sym.pp_string name) coq_args None coq_body) ; r ]*)
  | CI.Coq_app_recdef -> rets "Recdefs are unsupported"
  | CI.Coq_good (CI.Coq_sym s, _, t) -> 
      let op_nm = "good_" ^ (Sym.pp_string s) in
      parensM (build [ rets op_nm; aux t ])
  | CI.Coq_representable (CI.Coq_sym s, _, t) -> 
      let op_nm = "representable_" ^ (Sym.pp_string s) in
      parensM (build [ rets op_nm; aux t ])
  | CI.Coq_constructor (CI.Coq_sym name, args) -> 
    (*let preamble = pp_datatype global name in
    parensM (build ( [ preamble ] @ [ (Sym.pp name) ] @ List.map aux args))*)
    parensM (build ([ (Sym.pp name) ] @ List.map aux args))
  (* todo: this should somehow include the name of the list according to lemmata.ml*)
  | CI.Coq_nthlist (n, xs, d) -> 
  (* todo: this too should somehow have names for the nils/cons*)
    parensM (build [ rets "CN_Lib.nth_list_z"; aux n; aux xs; aux d ])
  | CI.Coq_arraytolist (arr, i, len) -> parensM
    (build
        [ rets "CN_Lib.array_to_list";
          aux arr;
          aux i;
          aux len
        ])
  | CI.Coq_wrapI (z1, z2, t) -> f_appM "CN_Lib.wrapI" [ enc_z z1; enc_z z2; aux t ]
  | CI.Coq_let (CI.Coq_sym nm, x, y) -> parensM (pp_let nm (aux x) (aux y))
  | CI.Coq_arrayshift (base, ct, index) -> 
    f_appM "CN_Lib.array_shift" [ aux base; enc_z ct; aux index ]
  | CI.Coq_forall (CI.Coq_sym sym, bt, t) -> pp_forall sym bt (aux t)
  | CI.Coq_Define (CI.Coq_sym sym, x, y) -> map_split (pp_let sym (aux x)) (aux y)
  | CI.Coq_Constraint_LRT (t1, t2) -> mk_and (aux t1) (aux t2)
  | CI.Coq_Constraint_LAT (t1, t2) -> mk_imp (aux t1) (aux t2)
  | CI.Coq_Resource -> rets "Resource is unsupported"
  | CI.Coq_I -> rets "Is_true true"
  | CI.Coq_unsupported -> rets "Unsupported term")
  in f global t
  
let convert_lemma_defs global (lemmas : CI.coq_lemmata list) =
  let lemma_ty (CI.Coq_lemmata (CI.Coq_sym nm, tm)) =
    Pp.progress_simple ("converting lemma type") (Sym.pp_string nm);
    let rhs = lemma_to_coq global tm in
    (defn (Sym.pp_string nm ^ "_type") [] (Some (Pp.string "Prop")) rhs)
  in
  let tys = List.map lemma_ty lemmas in  
  tys

(* print datatypes *)  

let translate_datatypes (dtys: CI.coq_dt list list) =
  let open Pp in
  let cons_line dt_tag (CI.Coq_constr(CI.Coq_sym(nm),params)) =
    let argTs = List.map (fun bt -> bt_to_coq bt) params in
      (!^"    | "
       ^^ Sym.pp nm
       ^^^ colon
       ^^^ flow !^" -> " (argTs @ [ Sym.pp dt_tag ]))
  in
  let dt_eqs (CI.Coq_dt(CI.Coq_sym nm, _, constr)) = 
             let c_lines = List.map (cons_line nm) constr in
               (!^"    "
                ^^ Sym.pp nm
                ^^^ colon
                ^^^ !^"Type :="
                ^^ hardline
                ^^ flow hardline c_lines)
  in
  let print_dt dty =  (flow
      hardline
      (List.mapi
          (fun i doc ->
            !^(if i = 0 then "  Inductive" else "    with") ^^ hardline ^^ doc)
          (List.map dt_eqs dty))
    ^^ !^"."
    ^^ hardline)
          in
  let rec f (dtys: CI.coq_dt list list) =
    (match dtys with
    | [] -> []
    | x :: xs -> print_dt x :: f xs) in
  f dtys

(* Main function *)
let generate (global : Global.t) directions (lemmata : (Sym.t * (Loc.t * AT.lemmat)) list)
  = 
  let filename, _kinds = parse_directions directions in
  let channel = open_out filename in
  Pp.print channel (header filename);

  (* translate everything to coq AST*)
  let CI.Coq_everything(dtys, _, _, lemmas) = CC.cn_to_coq_ir global lemmata in
  (* print datatypes *)
  let dtypes = translate_datatypes dtys in
  Pp.print channel (types_spec dtypes);
  (* print lemmas *)
  let translated_lemmas = convert_lemma_defs global lemmas in
  Pp.print channel (defs_module [] translated_lemmas);
  Pp.print channel (mod_spec (List.map (fun (CI.Coq_lemmata (CI.Coq_sym nm,_)) -> nm) lemmas));
