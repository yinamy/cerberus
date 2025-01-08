module BT = BaseTypes

type coq_sym = 
  | Coq_sym of Sym.t

type coq_id =
  | Coq_id of Id.t

(* Patterns in Coq *)

type coq_pat = 
  | Coq_pSym of coq_sym
  | Coq_pWild
  | Coq_pConstructor of coq_sym * (coq_pat list)

(* IndexTerm in Coq*)

type coq_const = 
  | Coq_bool of bool
  | Coq_bool_prop of bool
  | Coq_Z of Z.t
  | Coq_bits of (BT.sign * int) * Z.t

type coq_unop = 
  | Coq_neg
  | Coq_neg_prop
  | Coq_BW_FFS_NoSMT
  | Coq_BW_CTZ_NoSMT

type coq_binop =
  | Coq_add
  | Coq_sub
  | Coq_mul
  | Coq_div
  | Coq_mod
  | Coq_rem
  | Coq_lt
  | Coq_lt_prop
  | Coq_le
  | Coq_le_prop
  | Coq_exp
  | Coq_lxor
  | Coq_land
  | Coq_lor
  | Coq_eq
  | Coq_eq_prop
  | Coq_and
  | Coq_or
  | Coq_impl
  | Coq_impl_prop

type coq_term = 
  | Coq_sym of coq_sym
  | Coq_const of coq_const
  | Coq_unop of coq_unop * coq_term
  | Coq_binop of coq_binop * coq_term * coq_term
  | Coq_match of coq_term * (coq_pat * coq_term) list
  | Coq_ite of coq_term * coq_term * coq_term
  | Coq_eachI of (int * (coq_sym * BT.t) * int) * coq_term
  | Coq_mapset of coq_term * coq_term * coq_term
  | Coq_mapget of coq_term * coq_term
  | Coq_recordmember of coq_term * coq_id
  | Coq_recordupdate of (coq_term * coq_id) * coq_term
  | Coq_record of coq_term list
  | Coq_structmember of coq_term * coq_id
  | Coq_structupdate of (coq_term * coq_id) * coq_term
  | Coq_cast of BT.t * coq_term
  | Coq_apply of coq_sym * coq_term list
  (* | Coq_good 
     | Coq_representable *)
  | Coq_constructor of coq_sym * coq_term list
  | Coq_nthlist of coq_term * coq_term * coq_term
  | Coq_arraytolist of coq_term * coq_term * coq_term
  | Coq_let of coq_sym * coq_term * coq_term
  | Coq_wrapI of Z.t * Z.t * coq_term
  | Coq_arrayshift of coq_term * Z.t * coq_term
  | Coq_unsupported
