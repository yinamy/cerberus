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

let norm_bv_op bt doc_f =
  match bt with
  | BT.Bits (sign, sz) ->
    let minInt, maxInt = BT.bits_range (sign, sz) in
    f_appM "CN_Lib.wrapI" [ enc_z minInt; enc_z maxInt; doc_f ]
  | _ -> doc_f

let lemma_to_coq (t : CI.coq_term) = 
  let open Pp in
  let rec f t = 
    let aux t = f t in
    let abinop s x y = parensM (build [ aux x; rets s; aux y ]) in
  (match t with
  | CI.Coq_sym (CI.Coq_sym s) -> Sym.pp s
  | CI.Coq_const c -> (match c with
    (*todo: distinguish between bool prop and the other thing this is wrong*)
    | CI.Coq_bool b -> (rets (if b then "true" else "false"))
    | CI.Coq_bool_prop b -> f_appM "Is_true" [ (rets (if b then "true" else "false")) ]
    | CI.Coq_Z z -> parensM (rets (Z.to_string z))
    | CI.Coq_bits z -> parensM (rets (Z.to_string z)))
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
    | CI.Coq_eq -> parensM (build [ f x; rets "=?"; f y ])
    | CI.Coq_eq_prop -> parensM (build [ f x; rets "="; f y ])
    | CI.Coq_and -> abinop "&&" x y
    | CI.Coq_and_prop -> abinop "/\\" x y
    | CI.Coq_or -> abinop "||" x y
    | CI.Coq_or_prop -> abinop "\\/" x y
    | CI.Coq_impl -> abinop "implb" x y
    | CI.Coq_impl_prop -> abinop "->" x y
    | _ -> failwith "unsupported term")
  | _ -> failwith "unsupported term")
  in f t
  


(* Main function *)
let generate directions (lemmas : (Sym.t * CI.coq_term) list) = 
  let filename, _kinds = parse_directions directions in
  let channel = open_out filename in
  Pp.print channel (header filename);
