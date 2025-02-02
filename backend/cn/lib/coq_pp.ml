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

let struct_layout_field_bts xs =
  let open Memory in
  let xs2 =
    List.filter (fun x -> Option.is_some x.member_or_padding) xs
    |> List.sort (fun (x : struct_piece) y -> Int.compare x.offset y.offset)
    |> List.filter_map (fun x -> x.member_or_padding)
  in
  (List.map fst xs2, List.map (fun x -> Memory.bt_of_sct (snd x)) xs2)

let get_struct_xs struct_decls tag =
  match Sym.Map.find_opt tag struct_decls with
  | Some def -> struct_layout_field_bts def
  | None -> fail "undefined struct" (Sym.pp tag)  

let rec bt_to_coq (gl: Global.t) (bt : BT.t) =
  let open Pp in
  match bt with
  | BaseTypes.Bool -> !^"bool"
  | BaseTypes.Integer -> !^"Z"
  | BaseTypes.Bits _ -> !^"Z"
  | BaseTypes.Map (x, y) ->
    let enc_x = bt_to_coq gl x in
    let enc_y = bt_to_coq gl y in
    (parens (binop "->" enc_x enc_y))
  | BaseTypes.Struct tag ->
    let _, fld_bts = get_struct_xs gl.struct_decls tag in
    let enc_fld_bts = List.map (bt_to_coq gl) fld_bts in
    (tuple_coq_ty (Sym.pp tag) enc_fld_bts)
  | BaseTypes.Record mems ->
    let enc_mem_bts = List.map (bt_to_coq gl) (List.map snd mems) in
    (tuple_coq_ty !^"record" enc_mem_bts)
  | BaseTypes.Loc () -> !^"CN_Lib.Loc"
  (* todo: probably not right *)
  | BaseTypes.Datatype tag ->
    let p = pp_datatype gl tag in
    parensM (build ([ (Sym.pp tag) ] @ [ p ] ))
  (* todo: probably not right either*)
  | BaseTypes.List _bt2 -> bt_to_coq gl _bt2
  | _ -> fail "unsupported" (BT.pp bt)

and pp_datatype (global : Global.t) dt_tag =
  (* todo: this info should be sourced from elsewhere*)
  let family = Global.mutual_datatypes global dt_tag in
  let bt_to_coq2 bt =
    match BT.is_datatype_bt bt with
    | Some dt_tag2 ->
      if List.exists (Sym.equal dt_tag2) family then
        (Sym.pp dt_tag2)
      else
        bt_to_coq global bt
    | _ -> bt_to_coq global bt
  in
  let open Pp in
       let cons_line dt_tag c_tag =
         let info = Sym.Map.find c_tag global.datatype_constrs in
         let argTs = List.map (fun (_, bt) -> bt_to_coq2 bt) info.params in
           (!^"    | "
            ^^ Sym.pp c_tag
            ^^^ colon
            ^^^ flow !^" -> " (argTs @ [ Sym.pp dt_tag ]))
       in
       let dt_eqs =
         List.map
           (fun dt_tag ->
             let info = Sym.Map.find dt_tag global.datatypes in
             let c_lines = List.map (cons_line dt_tag) info.constrs in
               (!^"    "
                ^^ Sym.pp dt_tag
                ^^^ colon
                ^^^ !^"Type :="
                ^^ hardline
                ^^ flow hardline c_lines))
           family
       in
         (flow
            hardline
            (List.mapi
               (fun i doc ->
                 !^(if i = 0 then "  Inductive" else "    with") ^^ hardline ^^ doc)
               dt_eqs)
          ^^ !^"."
          ^^ hardline)

let pp_let sym rhs_doc doc =
  let open Pp in
  !^"let" ^^^ Sym.pp sym ^^^ !^":=" ^^^ rhs_doc ^^^ !^"in" ^^^ doc

let pp_forall global sym bt doc =
  let open Pp in
  let coq_bt = bt_to_coq global bt in
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
      let enc = pp_forall global s BaseTypes.Integer (binop
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
  | CI.Coq_app_uninterp (CI.Coq_sym name, arg_typs, args, ret_typ) -> 
    let r = parensM (build ([ (Sym.pp name) ] @ List.map aux args)) in
    let coq_arg_typs = List.map (fun (_, bt) -> bt_to_coq global bt) arg_typs in
    let coq_rt = bt_to_coq global ret_typ in
    let ty = List.fold_right (fun at rt -> at ^^^ !^"->" ^^^ rt) coq_arg_typs coq_rt in
    let preamble = (!^"  Parameter" ^^^ typ (Sym.pp name) ty ^^ !^"." ^^ hardline) in
    build [preamble ; r]
  | CI.Coq_app_uninterp_prop (CI.Coq_sym name, arg_typs, args) -> 
    let r = parensM (build ([ (Sym.pp name) ] @ List.map aux args)) in
    let coq_arg_typs = List.map (fun (_, bt) -> bt_to_coq global bt) arg_typs in
    let coq_rt = !^"Prop" in
    let ty = List.fold_right (fun at rt -> at ^^^ !^"->" ^^^ rt) coq_arg_typs coq_rt in
    let preamble = (!^"  Parameter" ^^^ typ (Sym.pp name) ty ^^ !^"." ^^ hardline) in
    build [preamble ; r]
  | CI.Coq_app_def (CI.Coq_sym name, body, arg_typs, args) -> 
    let r = parensM (build ([ (Sym.pp name) ] @ List.map aux args)) in
    let coq_body = aux body in
    let coq_args =
      List.map
        (fun (arg, bt) ->
          let coq_bt = bt_to_coq global bt in
          (Pp.parens (Pp.typ (aux arg) coq_bt)))
        arg_typs in
    build [ (defn (Sym.pp_string name) coq_args None coq_body) ; r ]
  | CI.Coq_app_recdef -> rets "Recdefs are unsupported"
  | CI.Coq_good (s, _, t) -> 
      let op_nm = "good_" ^ (Sym.pp_string s) in
      parensM (build [ rets op_nm; aux t ])
  | CI.Coq_representable (s, _, t) -> 
      let op_nm = "representable_" ^ (Sym.pp_string s) in
      parensM (build [ rets op_nm; aux t ])
  | CI.Coq_constructor (CI.Coq_sym name, args) -> 
    let preamble = pp_datatype global name in
    parensM (build ( [ preamble ] @ [ (Sym.pp name) ] @ List.map aux args))
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
  | CI.Coq_forall (CI.Coq_sym sym, bt, t) -> pp_forall global sym bt (aux t)
  | CI.Coq_Define (CI.Coq_sym sym, x, y) -> map_split (pp_let sym (aux x)) (aux y)
  | CI.Coq_Constraint_LRT (t1, t2) -> mk_and (aux t1) (aux t2)
  | CI.Coq_Constraint_LAT (t1, t2) -> mk_imp (aux t1) (aux t2)
  | CI.Coq_Resource -> rets "Resource is unsupported"
  | CI.Coq_I -> rets "Is_true true"
  | _ -> failwith "unsupported term")
  in f global t
  

(* Main function *)
let generate directions global (lemmas : (Sym.t * CI.coq_term) list) = 
  let filename, _kinds = parse_directions directions in
  let channel = open_out filename in
  Pp.print channel (header filename);
