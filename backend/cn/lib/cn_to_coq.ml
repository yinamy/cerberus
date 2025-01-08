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

let rec pat_to_coq_ir pat = 
  match pat with
  | Terms.Pat (Terms.PSym sym, _, _) -> CI.Coq_pSym (CI.Coq_sym sym)
  | Terms.Pat (Terms.PWild, _, _) -> CI.Coq_pWild
  | Terms.Pat (Terms.PConstructor (c_nm, id_ps), _, _) ->
      CI.Coq_pConstructor (CI.Coq_sym c_nm, List.map (fun x -> pat_to_coq_ir (snd x)) id_ps)
    (* assuming here that the id's are in canonical order *)

let rec it_to_coq_ir loc global list_mono it =
  let rec f comp_bool it =
    let aux t = f comp_bool t in
    let enc_prop = Option.is_none comp_bool in
  match IT.term it with
  | IT.Const l ->
    (match l with
      | IT.Bool b -> if enc_prop && BaseTypes.equal (IT.bt it) BaseTypes.Bool then
                        CI.Coq_const (CI.Coq_bool_prop b)
                    else
                        CI.Coq_const (CI.Coq_bool b)              
      | IT.Z z -> CI.Coq_const (CI.Coq_Z z)
      | IT.Bits (info, z) -> CI.Coq_const (CI.Coq_bits (info, z))
      | _ -> CI.Coq_unsupported)
  | IT.Unop (op, a) ->
    let x = aux a in
    (match op with
    | IT.Not -> (if enc_prop then
        CI.Coq_unop (CI.Coq_neg_prop , x)
          else 
        CI.Coq_unop (CI.Coq_neg , x))
    | IT.BW_FFS_NoSMT -> CI.Coq_unop (CI.Coq_BW_FFS_NoSMT , x)
    | IT.BW_CTZ_NoSMT -> CI.Coq_unop (CI.Coq_BW_CTZ_NoSMT , x)
    | _ -> CI.Coq_unsupported)
  | IT.Binop (op, a, b) ->
    let x = aux a in
    let y = aux b in
    (match op with
    | Add -> CI.Coq_binop (CI.Coq_add, x , y)
    | Sub -> CI.Coq_binop (CI.Coq_sub, x , y)
    | Mul -> CI.Coq_binop (CI.Coq_mul, x , y)
    | MulNoSMT -> CI.Coq_binop (CI.Coq_mul, x , y)
    | Div -> CI.Coq_binop (CI.Coq_div, x , y)
    | DivNoSMT -> CI.Coq_binop (CI.Coq_div, x , y)
    | Mod -> CI.Coq_binop (CI.Coq_mod, x , y)
    | ModNoSMT -> CI.Coq_binop (CI.Coq_mod, x , y)
    (* TODO: this can't be right: mod and rem aren't the same
      - maybe they have the same semantics as Coq Z.modulo/Z.rem *)
    | Rem -> CI.Coq_binop (CI.Coq_rem, x , y)
    | RemNoSMT -> CI.Coq_binop (CI.Coq_mod, x , y)
    | LT -> (if enc_prop then
                CI.Coq_binop (CI.Coq_lt_prop, x , y) 
              else 
                CI.Coq_binop (CI.Coq_lt, x , y))
    | LE -> (if enc_prop then
                CI.Coq_binop (CI.Coq_le_prop, x , y) 
              else 
                CI.Coq_binop (CI.Coq_le, x , y))
    | Exp -> CI.Coq_binop (CI.Coq_exp, x , y)
    | ExpNoSMT -> CI.Coq_binop (CI.Coq_exp, x , y)
    | BW_Xor -> CI.Coq_binop (CI.Coq_lxor, x , y)
    | BW_And -> CI.Coq_binop (CI.Coq_land, x , y)
    | BW_Or -> CI.Coq_binop (CI.Coq_lor, x , y)
    | EQ ->
      let comp = Some (it, "argument of equality") in
      (if enc_prop then
        CI.Coq_binop (CI.Coq_eq_prop, f comp a , f comp b) 
      else 
        CI.Coq_binop (CI.Coq_eq, f comp a , f comp b))
    | LEPointer -> (if enc_prop then
                CI.Coq_binop (CI.Coq_le_prop, x , y) 
              else 
                CI.Coq_binop (CI.Coq_le, x , y))
    | LTPointer -> (if enc_prop then
                CI.Coq_binop (CI.Coq_lt_prop, x , y) 
            else 
              CI.Coq_binop (CI.Coq_lt, x , y))
    | And -> CI.Coq_binop (CI.Coq_and, x , y)
    | Or -> CI.Coq_binop (CI.Coq_or, x , y)
    | Implies -> (if enc_prop then
                CI.Coq_binop (CI.Coq_impl_prop, x , y) 
          else 
                CI.Coq_binop (CI.Coq_impl, x , y))
    | _ -> CI.Coq_unsupported)
  | IT.Match (x, cases) -> 
    let comp = Some (it, "case-discriminant") in
    let br (pat, rhs) = (pat_to_coq_ir pat, aux rhs) in
    CI.Coq_match (f comp x, List.map br cases)
  | IT.ITE (sw, x, y) ->
    let comp = Some (it, "if-condition") in
    CI.Coq_ite (f comp sw, aux x, aux y)
  | IT.EachI ((i1, (s, t), i2), x) -> CI.Coq_eachI((i1, (CI.Coq_sym s, t), i2), aux x)
  | IT.MapSet (m, x, y) -> CI.Coq_mapset(aux m, aux x, aux y)
  | IT.MapGet (m, x) -> CI.Coq_mapget(aux m, aux x)
  | IT.RecordMember (t, m) -> CI.Coq_recordmember(aux t, CI.Coq_id m)
  | IT.RecordUpdate ((t, m), x) -> CI.Coq_recordupdate((aux t , CI.Coq_id m), aux x)
  | IT.Record mems -> CI.Coq_record (List.map aux (List.map snd mems))
  | IT.StructMember (t, m) -> CI.Coq_structmember(aux t, CI.Coq_id m)
  | IT.StructUpdate ((t, m), x) -> CI.Coq_structupdate((aux t , CI.Coq_id m), aux x)
  | IT.Cast (cbt, t) -> CI.Coq_cast (cbt, aux t)
  (* TODO: the apply case is probably wrong *)
  | IT.Apply (name, args) -> CI.Coq_apply (CI.Coq_sym name, List.map aux args)
  (*| IT.Good (ct, t2) -> 
    | IT.Representable *)
  | IT.Constructor (nm, id_args) ->
    let comp = Some (it, "datatype contents") in
    (* assuming here that the id's are in canonical order *)
    CI.Coq_constructor (CI.Coq_sym nm, List.map (fun x -> f comp (snd x)) id_args)
  | IT.NthList (n, xs, d) -> CI.Coq_nthlist (aux n, aux xs, aux d)
  | IT.ArrayToList (arr, i, len) -> CI.Coq_arraytolist (aux arr, aux i, aux len)
  | IT.WrapI (ity, arg) ->
    let maxInt = Memory.max_integer_type ity in
    let minInt = Memory.min_integer_type ity in
    CI.Coq_wrapI (maxInt, minInt, aux arg)
  | IT.Let ((nm, x), y) -> CI.Coq_let(CI.Coq_sym nm, aux x, aux y)
  | IT.ArrayShift { base; ct; index } ->
    let size_of_ct = Z.of_int @@ Memory.size_of_ctype ct in
    CI.Coq_arrayshift (aux base, size_of_ct, aux index)
  | _ -> CI.Coq_unsupported
  in
  (f None it, loc, global, list_mono)
