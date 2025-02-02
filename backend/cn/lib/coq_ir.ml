module BT = BaseTypes
module AT = ArgumentTypes

(* idk where this stuff goes yet *)

type coq_sym = 
  | Coq_sym of Sym.t

type coq_id =
  | Coq_id of Id.t

(* Patterns in Coq *)

type coq_pat = 
  | Coq_pSym of coq_sym
  | Coq_pWild
  | Coq_pConstructor of coq_sym * (coq_pat list)

(* IndexTerms in Coq*)

type coq_const = 
  | Coq_bool of bool
  | Coq_bool_prop of bool
  | Coq_Z of Z.t
  | Coq_bits of Z.t

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
  | Coq_bwxor
  | Coq_bwand
  | Coq_bwor
  | Coq_eq
  | Coq_eq_prop
  | Coq_and
  | Coq_and_prop
  | Coq_or
  | Coq_or_prop
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
  (* name, list of argument types, list of arguments, return type*)
  | Coq_app_uninterp of coq_sym * (coq_term * BT.t) list * coq_term list * BT.t
  | Coq_app_uninterp_prop of coq_sym * (coq_term * BT.t) list * coq_term list
  | Coq_app_def of coq_sym * coq_term * (coq_term * BT.t) list * coq_term list
  (* currently unsupported*)
  | Coq_app_recdef
  | Coq_good of Sym.t * BT.t * coq_term
  | Coq_representable of Sym.t * BT.t * coq_term
  | Coq_constructor of coq_sym * coq_term list
  | Coq_nthlist of coq_term * coq_term * coq_term
  | Coq_arraytolist of coq_term * coq_term * coq_term
  | Coq_let of coq_sym * coq_term * coq_term
  | Coq_wrapI of Z.t * Z.t * coq_term
  | Coq_arrayshift of coq_term * Z.t * coq_term
  | Coq_unsupported
  (* experiment: make everything flat*)
  (* LC in coq *)
  | Coq_forall of coq_sym * BT.t * coq_term
  (* LRT/LAT in coq*)
  | Coq_Define of coq_sym * coq_term * coq_term
  | Coq_Resource (* todo: add support *)
  | Coq_Constraint_LRT of coq_term * coq_term
  | Coq_Constraint_LAT of coq_term * coq_term
  | Coq_I
(*
(* Logical constraints in Coq *)  
type coq_LC =
  | Coq_forall of coq_sym * BT.t * coq_LC
  | Coq_T of coq_term

(* Logical return types in Coq *)
type coq_LRT =
  | Coq_Define of coq_sym * coq_term * coq_LRT
  | Coq_Resource (* todo: add support *)
  | Coq_Constraint of coq_LC * coq_LRT
  | Coq_I

(* Logical argument types in Coq *)  
type coq_LAT =
  | Coq_Define of coq_sym * coq_term  * coq_LAT
  | Coq_Resource
  | Coq_Constraint of coq_LC * coq_LAT
  | Coq_I of coq_LAT
  | Coq_unsupported

(* CN datatypes*)
type coq_constr =
  | Coq_constr of (coq_sym * BT.constr_info) list

(* CN datatype info *)
(* A datatype is a name, its dt_info, and its constructors with all associated info *)
type coq_dt = 
  | Coq_dt of (coq_sym * BT.dt_info * coq_constr list)

(* CN logical functions *)
type coq_logicfun = 
  | Coq_logicfun of (coq_sym * Definition.Function.t) list

(* CN resource predicates (unimplemented) *)
type coq_resource_pred = 
  | Coq_resource_pred

(* CN global typing context *)
type coq_global_ctx =
  | Coq_global_ctx of (coq_dt list) * (coq_logicfun list) * (coq_resource_pred list)
  *)