module BT = BaseTypes
module AT = ArgumentTypes
module Loc = Locations
module StringSet = Set.Make (String)
module CI = Coq_ir
module CC = Cn_to_coq

(* Printing headers for each module in the Coq file *)

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
  ^^ !^"Require Import CN_Lemmas.CN_Lib_Iris."
  ^^ hardline
  ^^ hardline

let open_iris_mode iris_defs section_name = 
  let open Pp in
  !^"  (* Opening Iris mode *)"
  ^^ hardline
  ^^ !^"  Section " ^^ !^section_name ^^ !^"."
  ^^ hardline
  ^^ !^"  Context `{!heapGS_gen Σ}."
  ^^ hardline
  ^^ hardline
  ^^ flow hardline iris_defs
  ^^ hardline
  ^^ hardline
  ^^ !^"  (* Closing Iris mode *)"
  ^^ hardline
  ^^ !^"  End " ^^ !^section_name ^^ !^"."

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
  ^^ hardline
  ^^ open_iris_mode lemma_tys "Iris_Type_Defs"
  ^^ hardline
  ^^ !^"End Defs."
  ^^ hardline
  ^^ hardline
  
let mod_spec lemma_nms =
  let open Pp in
  let lemma nm =
    !^"  Parameter" ^^^ typ (Sym.pp nm) (!^"⊢ " ^^ Sym.pp nm ^^ !^"_type") ^^ !^"." ^^ hardline
  in
  !^"Module Type Lemma_Spec (P : Parameters)."
  ^^ hardline
  ^^ hardline
  ^^ !^"  Module D := Defs(P)."
  ^^ hardline
  ^^ !^"  Import D."
  ^^ hardline
  ^^ open_iris_mode ((!^"  Local Notation \"⊢ P\" := (⊢@{iPropI Σ} P)." 
  ^^ hardline) :: (List.map lemma lemma_nms)) "Lemma_Defs"
  ^^ hardline
  ^^ !^"End Lemma_Spec."
  ^^ hardline
  ^^ hardline

let pres_spec preds =
  let open Pp in
  !^"Module ResourcePredicates (P : Parameters)."
  ^^ hardline
  ^^ !^"  Import Types P."
  ^^ hardline
  ^^ hardline
  ^^ (if List.length preds == 0 then
        !^"  (* no resource predicates required *)" ^^ hardline
      else
        open_iris_mode preds "Iris_Pred_Defs")
  ^^ hardline
  ^^ !^"End ResourcePredicates."
  ^^ hardline
  ^^ hardline

let param_spec params =
  let open Pp in
  !^"Module Type Parameters."
  ^^ hardline
  ^^ !^"  Import Types."
  ^^ hardline
  ^^ hardline
  ^^ (if List.length params == 0 then
        !^"  (* no parameters required *)" ^^ hardline
      else
        flow hardline params)
  ^^ hardline
  ^^ !^"End Parameters."
  ^^ hardline
  ^^ hardline  


(* Convenient printing functions *)

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

let iris_pure x = build [ rets "⌜"; x; rets "⌝" ]

let rec intersperse (sep : string) (last : string) xs =
  let open Pp in
  match xs with
  | [] -> !^""
  | x :: [] -> x ^^ !^(last)
  | x :: xs -> x ^^ !^sep ^^ (intersperse sep last xs)

let print_ctype (ctyp : Sctypes.t) = 
  match ctyp with
  | Void -> "unsupported ctype void"
  | Integer _ -> "Z"
  | Array _ -> "unsupported ctype array"
  | Pointer _ -> "Ptr"
  | Struct s -> Sym.pp_string s
  | Function _ -> "unsupported ctype function"

let enc_z z =
  if Z.leq Z.zero z then
    rets (Z.to_string z)
  else
    parensM (rets (Z.to_string z))

let f_appM nm xs = parensM (build (rets nm :: xs))

let defn nm args opt_ty rhs fix =
  let open Pp in
  let if_fix = if fix then !^"  Fixpoint" else !^"  Definition" in
  let tyeq = match opt_ty with None -> [] | Some ty -> [ colon; ty ] in
  flow (break 1) ([ if_fix; !^nm ] @ args @ tyeq @ [ !^":=" ])
  ^^ hardline
  ^^ !^"    "
  ^^ rhs
  ^^ !^"."
  ^^ hardline

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


(* Getter for tuples given an index and its dimensions
  , useful because we translate records as tuples *)
let gen_get_upd ((i, list_len) : int * int) (tm : PPrint.document) =
  let open Pp in
  let pp_fst a = parens (build [ rets "fst"; a ]) in
  let pp_snd a = parens (build [ rets "snd"; a]) in
  let rec foldi i f acc =
    if i <= 0 then acc else foldi (pred i) f (f acc)
  in
  if i = 0 then
    foldi (list_len - 1) pp_fst tm
  else
    pp_snd (foldi (list_len - 1 - i) pp_fst tm)

(* CN BaseTypes to Coq *)
let rec bt_to_coq (bt : CI.coq_bt) =
  let open Pp in
  match bt with
  | CI.Coq_Bool -> !^"bool"
  | CI.Coq_Integer -> !^"Z"
  | CI.Coq_Bits _ -> !^"Z"
  | CI.Coq_Map (x, y) ->
    let enc_x = bt_to_coq x in
    let enc_y = bt_to_coq y in
    (parens (binop "->" enc_x enc_y))
  | CI.Coq_Struct (CI.Coq_sym tag, _) -> Sym.pp tag
    (*let enc_fld_bts = List.map bt_to_coq fld_bts in
    (tuple_coq_ty (Sym.pp tag) enc_fld_bts)*)
  | CI.Coq_Record mems ->
    let enc_mem_bts = List.map bt_to_coq mems in
    (tuple_coq_ty !^"record" enc_mem_bts)
  | CI.Coq_Loc -> !^"Ptr"
  | CI.Coq_Datatype (CI.Coq_sym tag) -> Sym.pp tag
  | CI.Coq_List _bt2 -> !^"list " ^^ bt_to_coq _bt2
  | CI.Coq_Unit -> !^"unsupported BT unit"
  | CI.Coq_Membyte -> !^"unsupported BT membyte"
  | CI.Coq_Real -> !^"unsupported BT real"
  | CI.Coq_Alloc_id -> !^"unsupported BT alloc_id"
  | CI.Coq_CType -> !^"unsupported BT ctype"
  | CI.Coq_Tuple fld_bts ->
    let enc_fld_bts = List.map bt_to_coq fld_bts in
    (tuple_coq_ty !^"" enc_fld_bts)
  | CI.Coq_Set _bt2 -> rets "unsupported BT set"

let pp_let sym rhs_doc doc =
  let open Pp in
  !^"let" ^^^ Sym.pp sym ^^^ !^":=" ^^^ rhs_doc ^^^ !^"in" ^^^ doc

let pp_forall sym bt doc =
  let open Pp in
  let coq_bt = bt_to_coq bt in
  (!^"∀" ^^^ parens (typ (Sym.pp sym) coq_bt) ^^ !^"," ^^ break 1 ^^ doc)

let pp_iris_exists sym bt doc =
  let open Pp in
  let coq_bt = bt_to_coq bt in
  (!^"∃" ^^^ parens (typ (Sym.pp sym) coq_bt) ^^ !^"," ^^ break 1 ^^ doc)

let norm_bv_op bt doc_f =
    match bt with
    | CI.Coq_Bits (sign, sz) ->
      (match sign with
      | CI.Coq_Unsigned -> 
        let minInt, maxInt = BT.bits_range (Unsigned, sz) in
        f_appM "CN_Lib.wrapI" [ enc_z minInt; enc_z maxInt; doc_f ]
      | CI.Coq_Signed -> 
        let minInt, maxInt = BT.bits_range (Signed, sz) in
        f_appM "CN_Lib.wrapI" [ enc_z minInt; enc_z maxInt; doc_f ])
  | _ -> doc_f

let rec pat_to_coq (pat : CI.coq_pat) = match pat with
  | Coq_pSym (Coq_sym sym) -> (Sym.pp sym)
  | Coq_pWild -> rets "_"
  | Coq_pConstructor (Coq_sym s, l) -> 
      parensM (build ([ (Sym.pp s) ] @ List.map pat_to_coq l))

(* is_clause is true when the translated term is a resource predicate clause,
    this is because resource predicate clauses use different connectives *)      
let term_to_coq (global : Global.t) (t : CI.coq_term) (is_clause : bool) = 
  let open Pp in
  let rec f (global : Global.t) (iris_bool : bool) t  = 
    let aux t = f global iris_bool t  in
    let abinop s x y = parensM (build [ aux x; rets s; aux y ]) in
    let map_split f = (fun doc -> f (break 1 ^^ doc)) in
    let mk_and doc doc2 = doc ^^^ !^"/\\" ^^^ doc2 in
    let mk_imp doc doc2 = doc ^^^ !^"->" ^^^ doc2 in
    let mk_wand doc doc2 = doc ^^^ !^"-∗" ^^^ doc2 in
    let mk_star doc doc2 = doc ^^^ !^"∗" ^^^ doc2 in
    let mk_iris_imp doc doc2 = doc ^^^ !^"→" ^^^ doc2 in
    let mk_iris_and doc doc2 = doc ^^^ !^"∧" ^^^ doc2 in
  (match t with
  | CI.Coq_sym_term (CI.Coq_sym s) -> Sym.pp s
  | Coq_const c -> (match c with
    | Coq_bool b -> (rets (if b then "true" else "false"))
    | Coq_bool_prop b -> f_appM "Is_true" [ (rets (if b then "true" else "false")) ]
    | Coq_Z z -> enc_z z
    | Coq_bits z -> parensM (rets (Z.to_string z)))
  | Coq_unop (op, x, bt) -> norm_bv_op bt (match op with
    | CI.Coq_neg -> f_appM "negb" [ aux x ]
    | CI.Coq_neg_prop -> f_appM "~" [ aux x ]
    | CI.Coq_BW_FFS_NoSMT -> f_appM "CN_Lib.find_first_set_z" [ aux x ]
    | CI.Coq_BW_CTZ_NoSMT -> f_appM "CN_Lib.count_trailing_zeroes_z" [ aux x ])
  | CI.Coq_binop (op, x, y, bt) -> norm_bv_op bt (match op with
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
    | CI.Coq_eq_prop -> if iris_bool then iris_pure (build [ aux x; rets "="; aux y ])
                          else parensM (build [ aux x; rets "="; aux y ])
    | CI.Coq_and -> abinop "&&" x y
    | CI.Coq_and_prop -> abinop "/\\" x y
    | CI.Coq_or -> abinop "||" x y
    | CI.Coq_or_prop -> abinop "\\/" x y
    | CI.Coq_impl -> abinop "implb" x y
    | CI.Coq_impl_prop -> abinop "->" x y)
  | CI.Coq_match (x, cases) -> 
    let br (pat, rhs) =
      build [ rets "|"; pat_to_coq pat; rets "=>"; aux rhs ] in
    parensM
      (build
        ([ rets "match"; aux x; rets "with"; hardline ] @ List.map br cases @ [ rets "end" ]))
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
  | CI.Coq_recordmember (t, _, ix) -> 
      (*let op_nm = "get_" ^ (Id.get_string nm) in
      parensM (build [ rets op_nm; aux t ])*)
      gen_get_upd ix (aux t)
  | CI.Coq_recordupdate ((t, _), x, ix) -> 
      (*let op_nm = "upd_" ^ (Id.get_string nm) in
      parensM (build [ rets op_nm; aux t; aux x ])*)
      let op_nm = gen_get_upd ix (aux t) in
      parensM (build [ op_nm; aux x ])
  | CI.Coq_record l -> 
      let xs = List.map aux l in
      parensM ((flow (comma ^^ break 1) xs))
  | CI.Coq_structmember (t, CI.Coq_id fieldnm, _) ->
      (*let op_nm = "get_" ^ (Id.get_string nm) in
      parensM (build [ rets op_nm; aux t ])*)
      (aux t) ^^ !^"." ^^ parens !^(Id.get_string fieldnm)
  | CI.Coq_structupdate ((t, _), x, ix) -> 
      (*let op_nm = "upd_" ^ (Id.get_string nm) in
      parensM (build [ rets op_nm; aux t; aux x ])*)
      let op_nm = gen_get_upd ix (aux t) in
      parensM (build [ op_nm; aux x ])
  | CI.Coq_cast (_, x) -> aux x
  | CI.Coq_apply (CI.Coq_sym name, args) -> 
    parensM (build ([ (Sym.pp name) ] @ List.map aux args))
  | CI.Coq_apply_prop (CI.Coq_sym name, args) -> 
    let r = parensM (build ([ (Sym.pp name) ] @ List.map aux args)) in
    f_appM "Is_true" [r]
  | CI.Coq_good (CI.Coq_sym s, _, t) -> 
      let op_nm = "good_" ^ (Sym.pp_string s) in
      parensM (build [ rets op_nm; aux t ])
  | CI.Coq_representable (CI.Coq_sym s, _, t) -> 
      let op_nm = "representable_" ^ (Sym.pp_string s) in
      parensM (build [ rets op_nm; aux t ])
  | CI.Coq_constructor (CI.Coq_sym name, args) -> 
    parensM (build ([ (Sym.pp name) ] @ List.map aux args))
  | CI.Coq_nthlist (n, xs, d) -> 
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
  | CI.Coq_Constraint_LRT (t1, t2) -> (match t1 with
  (* todo: is this right? *)
    | CI.Coq_good_go_away _ -> mk_star (aux t1) (aux t2)
    | _ -> if iris_bool then
              mk_iris_and (aux t1) (aux t2)
            else
              mk_and (aux t1) (aux t2))
  | CI.Coq_Constraint_LAT (t1, t2) -> (match t1 with
  (* todo: is this right? *)
    | CI.Coq_good_go_away _ -> if is_clause then 
              mk_star (aux t1) (aux t2)
            else
              mk_wand (aux t1) (aux t2)
    | _ -> if is_clause then 
              mk_star (aux t1) (aux t2)
            else if iris_bool then
              mk_iris_imp (aux t1) (aux t2)
            else
              iris_pure (mk_imp (aux t1) (aux t2)))
  | CI.Coq_I -> if iris_bool then
      rets "emp"
    else
      rets "Is_true true"
  | CI.Coq_Owned_LAT (CI.Coq_sym s, bt, t, pointer, _) -> 
    let forall_owned op_nm = 
      pp_forall s bt (build ([ rets op_nm; aux pointer; rets (Sym.pp_string s); g global t ])) in
    let exists_owned op_nm = 
      pp_iris_exists s bt (build ([ rets op_nm; aux pointer; rets (Sym.pp_string s); g global t ])) in
    (match bt with
    | CI.Coq_Bits (_, _) -> 
      let op_nm = "Owned_int" in
      if is_clause then exists_owned op_nm else forall_owned op_nm
    | CI.Coq_Struct (CI.Coq_sym nm, _) -> let op_nm =  "Owned" ^ (Sym.pp_string nm) in 
      if is_clause then exists_owned op_nm else forall_owned op_nm
    | _ ->  rets "Coq_Owned_LAT unsupported BT")
  | CI.Coq_Block_LAT (CI.Coq_sym s, _, t, _) ->
    let op_nm = "block_" ^ (Sym.pp_string s) in
    parensM (build [ rets op_nm; g global t ])
  | CI.Coq_Owned_LRT (CI.Coq_sym s, bt, t, pointer, _) -> (match bt with
    | CI.Coq_Bits (_, _) -> 
      let op_nm = "Owned_int" in
      pp_iris_exists s bt (build ([ rets op_nm; aux pointer; rets (Sym.pp_string s); g global t ]))
    | CI.Coq_Struct (CI.Coq_sym nm, _) -> 
      let op_nm = "Owned_"^(Sym.pp_string nm) in
      pp_iris_exists s bt (build ([ rets op_nm; aux pointer; rets (Sym.pp_string s); g global t ]))
    | _ ->  rets "Coq_Owned_LRT unsupported BT")
  | CI.Coq_Block_LRT (CI.Coq_sym s, _, t, _) ->
    let op_nm = "Block_" ^ (Sym.pp_string s) in
    parensM (build [ rets op_nm; g global t ])
    (* todo: this can't be right *)
  | CI.Coq_good_go_away _ -> rets ""
  | CI.Coq_Res_Pred (CI.Coq_sym s, _, t, iargs, _) -> 
    let args = List.map aux iargs in
    build (((Sym.pp s) :: args) @ [aux t])
  | CI.Coq_unsupported msg -> rets msg)

  (* turn on iris mode! *)
  and g global (t : CI.iris_term) = match t with
    | CI.Iris_term t -> (f global true t)

  in (if is_clause then
    f global true t
  else
    f global false t)
  
let convert_lemma_defs global (lemmas : CI.coq_lemmata list) =
  let lemma_ty (CI.Coq_lemmata (CI.Coq_sym nm, tm)) =
    Pp.progress_simple ("converting lemma type") (Sym.pp_string nm);
    let rhs = term_to_coq global tm false in
    (defn (Sym.pp_string nm ^ "_type") [] (Some (Pp.string "iProp Σ")) rhs false)
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
  let print_dt dty_clump =  (flow
      hardline
      (List.mapi
          (fun i doc ->
            !^(if i = 0 then "  Inductive" else "    with") ^^ hardline ^^ doc)
          (List.map dt_eqs dty_clump))
    ^^ !^"."
    ^^ hardline)
          in
  let rec f (dtys: CI.coq_dt list list) =
    (match dtys with
    | [] -> []
    | x :: xs -> print_dt x :: f xs) in
  f dtys

(* print function definitions *)
let translate_pred (gl: Global.t) (preds: CI.coq_resource_pred list list) = 
  let open Pp in
  let unpack_clauses (clauses: CI.coq_clause list option) =
    match clauses with
    | None -> rets "unsupported: uninterpreted predicate"
    | Some cl -> 
      let clause_to_coq (clause: CI.coq_clause) = 
        match clause with
        | CI.Coq_clause (guard, body) -> 
          let guard_doc = term_to_coq gl guard false in
          let body_doc = term_to_coq gl body true in
          parensM (build [ guard_doc; rets " ∧ "; body_doc ])
      in
      intersperse " ∨ " " . " (List.map clause_to_coq cl)
  in
  let make_args (args : (CI.coq_sym * CI.coq_bt) list) = 
    let make_one_arg arg = match arg with
      | (CI.Coq_sym id, bt) -> parens (typ (Sym.pp id) (bt_to_coq bt))
    in
    List.map make_one_arg args
  in
  let unpack_preds (pred : CI.coq_resource_pred) = match pred with
  | CI.Coq_rpred (CI.Coq_sym nm, CI.Coq_sym ptr, args, ret_ty, clauses) ->
    !^"  Fixpoint " ^^ !^(Sym.pp_string nm) 
    ^^ !^" " ^^ parens (typ !^(Sym.pp_string ptr) !^"Ptr")
    ^^ !^" " ^^ intersperse " " "" (make_args args)
    ^^ !^" " ^^ parens (typ !^"ret" (bt_to_coq ret_ty))
    ^^ !^" {struct ret} "
    ^^ !^" : iProp Σ := " 
    ^^ hardline
    ^^ (unpack_clauses clauses)
    ^^ hardline
    in
  List.map unpack_preds (List.concat preds)

let translate_fun (gl : Global.t) (funs: CI.coq_fun list list * CI.coq_fun list list) =
  let open Pp in
  let translate_one cf = 
  (match cf with
    | CI.Coq_fun_def (CI.Coq_sym nm, logical_fun, args, _) -> 
      (match logical_fun with
      | CI.Coq_def body -> 
        let coq_body = term_to_coq gl body false in
        let coq_args =
          List.map
            (fun ((CI.Coq_sym arg), bt) ->
              let coq_bt = bt_to_coq bt in
              (Pp.parens (Pp.typ (Sym.pp arg) coq_bt)))
            args in
        defn (Sym.pp_string nm) coq_args None coq_body false
      | CI.Coq_recdef body -> 
        let coq_body = term_to_coq gl body false in
        let coq_args =
          List.map
            (fun ((CI.Coq_sym arg), bt) ->
              let coq_bt = bt_to_coq bt in
              (Pp.parens (Pp.typ (Sym.pp arg) coq_bt)))
            args in
        defn (Sym.pp_string nm) coq_args None coq_body true
      )
    | CI.Coq_fun_uninterp (CI.Coq_sym nm, logical_fun, args, ret_typ) -> 
      (match logical_fun with
      | CI.Coq_uninterp -> 
        let coq_arg_typs = List.map (fun (_, bt) -> bt_to_coq bt) args in
        let coq_rt = bt_to_coq ret_typ in
        let ty = List.fold_right (fun at rt -> at ^^^ !^"->" ^^^ rt) coq_arg_typs coq_rt in
        ((!^"  Parameter" ^^^ typ (Sym.pp nm) ty ^^ !^"." ^^ hardline))
      | CI.Coq_uninterp_prop -> 
        let coq_arg_typs = List.map (fun (_, bt) -> bt_to_coq bt) args in
        let coq_rt = !^"Prop" in
        let ty = List.fold_right (fun at rt -> at ^^^ !^"->" ^^^ rt) coq_arg_typs coq_rt in
        ((!^"  Parameter" ^^^ typ (Sym.pp nm) ty ^^ !^"." ^^ hardline)))
    )
  in
  let print clump =  (flow
      hardline
      (List.mapi
          (fun i doc ->
            !^(if i = 0 then "" else "    with") ^^ doc)
          (List.map translate_one clump)))
  in
  (List.map print (fst funs), 
   List.map print (snd funs))

(* generate records and Owned_Structname predicates for all structs*)
let translate_structs (struct_decls : Memory.struct_decls) = 
  let open Pp in
  let piece_to_owned (piece : Memory.struct_piece) = 
    let make_owned (nm: string) (id : Id.t) =
      !^(nm^ " ")
      ^^ (parens !^("CN_Lib_Iris.shift l " 
                  ^ string_of_int piece.offset ^ " " 
                  ^ string_of_int piece.size))
      ^^ !^" v." ^^ parens !^(Id.get_string(id)) 
     in
    (match piece.member_or_padding with
      | Some (id,ctyp) -> (match ctyp with
        | Void -> rets "unsupported ctype void"
        | Integer _ -> make_owned "Owned_int" id
        | Array _ -> rets "unsupported ctype array"
        (* todo: probably not right? *)
        | Pointer _ -> make_owned "Owned_int" id
        | Struct s -> make_owned ("Owned_" ^ Sym.pp_string s) id
        | Function _ -> rets "unsupported ctype function")
      | None -> !^"padding " 
                ^^ parens (!^"arrayshift " 
                ^^ !^"l " ^^ !^(string_of_int piece.offset) ^^ !^" 1")
                ^^ !^(" " ^ string_of_int piece.size))
  in
  let rec decl_to_pieces (pieces : Memory.struct_piece list) = 
    (match pieces with
    | [] -> rets ""
    | x :: [] -> piece_to_owned x ^^ !^"."
    | x :: xs -> piece_to_owned x ^^ !^" ∗ " ^^ decl_to_pieces xs)
    in
  let get_struct_field (piece : Memory.struct_piece) = 
    (match piece.member_or_padding with
    | Some (id,ctype) -> !^("  " ^ Id.get_string(id) ^ " : " ^ (print_ctype ctype) ^ "; ") ^^hardline
    | None -> rets "")
    in
  let unpack_decls (decl : Sym.t * Memory.struct_layout) =
    let nm = !^(Sym.pp_string (fst decl)) in
    !^"  Record " ^^ nm ^^ !^" : Type := { " 
    ^^ hardline
    ^^ build (List.map get_struct_field (snd decl)) ^^ !^" }."
    ^^ hardline
    ^^ hardline
    ^^ !^"  Definition " ^^ !^"Owned_" ^^ nm
    ^^ !^" (l: Ptr) (v : " ^^ nm ^^ !^") : iProp Σ := "
    ^^ (decl_to_pieces (snd decl))
    ^^ hardline
    in
  List.map unpack_decls (Sym.Map.bindings struct_decls)
   
let generate (global : Global.t) directions (lemmata : (Sym.t * (Loc.t * AT.lemmat)) list)
  = 
  let f =
    let filename, _kinds = parse_directions directions in
    let channel = open_out filename in
    Pp.print channel (header filename);

    (* translate everything to coq AST*)
    let CI.Coq_everything(dtys, funs, preds, lemmas) = CC.cn_to_coq_ir global lemmata in

    (* print datatypes *)
    let dtypes = translate_datatypes dtys in
    let structs = if (global.struct_decls == Sym.Map.empty) then
     [ Pp.string "(* no struct definitions required *)" ]
        else
      translate_structs global.struct_decls
    in

    (* print datatypes and structs *)
    Pp.print channel (types_spec (dtypes @ [open_iris_mode structs "Struct_Defs"]));

    (* print uninterpreted logical functions as parameters *)
    let translated_funs = translate_fun global funs in
    Pp.print channel (param_spec (fst translated_funs));

    (* print resource predicates *)
    let translated_preds = translate_pred global preds in
    Pp.print channel (pres_spec translated_preds);
    
    (* print lemmas *)
    let translated_lemmas = convert_lemma_defs global lemmas in
    Pp.print channel (defs_module (snd translated_funs) translated_lemmas);
    Pp.print channel (mod_spec (List.map (fun (CI.Coq_lemmata (CI.Coq_sym nm,_)) -> nm) lemmas));
  in
  (Result.Ok f)