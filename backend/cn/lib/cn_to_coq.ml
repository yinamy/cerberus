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

(* set of functions with boolean return type that we want to use
   as toplevel propositions, i.e. return Prop rather than bool
   (computational) in Coq. *)
   let prop_funs = StringSet.of_list [ "page_group_ok" ]

let fun_prop_ret (global : Global.t) nm =
  match Sym.Map.find_opt nm global.logical_functions with
  (* todo: the None case shouldn't be possible since the CN code must be well-formed *)
  | None -> true
  | Some def ->
    let open Definition.Function in
    BaseTypes.equal BaseTypes.Bool def.return_bt
    && StringSet.mem (Sym.pp_string nm) prop_funs

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
  (* the none case should be impossible *)
  | None -> [], []

let rec bt_to_coq_ir (gl: Global.t) (bt : BT.t) =
  match bt with
  | BaseTypes.Bool -> CI.Coq_Bool
  | BaseTypes.Integer -> CI.Coq_Integer
  | BaseTypes.Bits (sign, i) -> 
      (match sign with
      | BT.Signed -> CI.Coq_Bits (CI.Coq_Signed, i)
      | BT.Unsigned -> CI.Coq_Bits (CI.Coq_Unsigned, i))
  | BaseTypes.Map (x, y) ->
    let enc_x = bt_to_coq_ir gl x in
    let enc_y = bt_to_coq_ir gl y in
    CI.Coq_Map (enc_x, enc_y)
  | BaseTypes.Struct tag ->
    let _, fld_bts = get_struct_xs gl.struct_decls tag in
    let enc_fld_bts = List.map (bt_to_coq_ir gl) fld_bts in
    CI.Coq_Record enc_fld_bts
  | BaseTypes.Record mems ->
    let enc_mem_bts = List.map (bt_to_coq_ir gl) (List.map snd mems) in
    CI.Coq_Record enc_mem_bts
  | BaseTypes.Loc () -> CI.Coq_Loc
  (* todo: probably not right *)
  | BaseTypes.Datatype tag -> CI.Coq_Datatype (CI.Coq_sym tag)
  (* todo: probably not right either*)
  | BaseTypes.List _bt2 -> CI.Coq_List (bt_to_coq_ir gl bt)
  | _ -> Coq_BT_unsupported

(* map each mutually recursive list of datatypes to mutually recursive lists of coq_ir *)
let dt_to_coq_ir (gl : Global.t) nm = 
  (* find the info of a datatype *)
  let dt_info = Sym.Map.find nm gl.datatypes in
  (* get its params and translate them*)
  let dt_args = List.map (fun (_, bt) -> bt_to_coq_ir gl bt) dt_info.all_params in
  (* find the info of a constructor, given its name*)
  let constr_info constr = Sym.Map.find constr gl.datatype_constrs in
  (* get the argument types of the constructor *)
  let constr_argTs constrs_nms = List.map (fun (_, bt) -> (bt_to_coq_ir gl bt)) constrs_nms in
  let constrs = 
    List.map (fun c -> CI.Coq_constr (CI.Coq_sym c, constr_argTs (constr_info c).params)) dt_info.constrs 
  in
  CI.Coq_dt(CI.Coq_sym nm, dt_args , constrs)

let dtypes_to_coq_ir (gl : Global.t) (dtyps : Sym.t list list) =
  (* translate one particular clump of mutually recursive definitoins *)
  let dtype_clump_to_coq_ir (gl : Global.t) (nms : Sym.t list) = 
    List.map (dt_to_coq_ir gl) nms
  in
  (* wrap them all together into a big list of lists *)
  List.map (dtype_clump_to_coq_ir gl) dtyps

let find_tuple_element
  (eq : 'a -> 'a -> bool)
  (x : 'a)
  (ys : 'a list)
  =
  let n_ys = List.mapi (fun i y -> (i, y)) ys in
  match List.find_opt (fun (_i, y) -> eq x y) n_ys with
  | None -> (0,0)
  | Some (i, _) -> (i, List.length ys)

(* translate index terms to coq_ir *)
let it_to_coq_ir global it b =
  let rec f comp_bool it =
    let aux t = f comp_bool t in
    let enc_prop = Option.is_none comp_bool in
    let with_is_true =
      enc_prop && BaseTypes.equal (IT.get_bt it) BaseTypes.Bool
    in
    let bt = bt_to_coq_ir global (IT.get_bt it) in
  (match IT.get_term it with
  | IT.Sym s -> CI.Coq_sym_term (CI.Coq_sym s)
  | IT.Const l ->
    (match l with
      | IT.Bool b -> if with_is_true then
                        CI.Coq_const (CI.Coq_bool_prop b)  
                    else     
                        CI.Coq_const (CI.Coq_bool b)      
      | IT.Z z -> CI.Coq_const (CI.Coq_Z z)
      | IT.Bits (info, z) -> CI.Coq_const (CI.Coq_bits (BT.normalise_to_range info z))
      | _ -> CI.Coq_unsupported)
  | IT.Unop (op, a) ->
    let x = aux a in
    (match op with
    | IT.Not -> (if enc_prop then
        CI.Coq_unop (CI.Coq_neg_prop , x, bt)
          else 
        CI.Coq_unop (CI.Coq_neg , x, bt))
    | IT.BW_FFS_NoSMT -> CI.Coq_unop (CI.Coq_BW_FFS_NoSMT , x, bt)
    | IT.BW_CTZ_NoSMT -> CI.Coq_unop (CI.Coq_BW_CTZ_NoSMT , x, bt)
    | _ -> CI.Coq_unsupported)
  | IT.Binop (op, a, b) ->
    let x = aux a in
    let y = aux b in
    (match op with
    | Add -> CI.Coq_binop (CI.Coq_add, x , y, bt)
    | Sub -> CI.Coq_binop (CI.Coq_sub, x , y, bt)
    | Mul -> CI.Coq_binop (CI.Coq_mul, x , y, bt)
    | MulNoSMT -> CI.Coq_binop (CI.Coq_mul, x , y, bt)
    | Div -> CI.Coq_binop (CI.Coq_div, x , y, bt)
    | DivNoSMT -> CI.Coq_binop (CI.Coq_div, x , y, bt)
    | Mod -> CI.Coq_binop (CI.Coq_mod, x , y, bt)
    | ModNoSMT -> CI.Coq_binop (CI.Coq_mod, x , y, bt)
    (* TODO: this can't be right: mod and rem aren't the same
      - maybe they have the same semantics as Coq Z.modulo/Z.rem *)
    | Rem -> CI.Coq_binop (CI.Coq_rem, x , y, bt)
    | RemNoSMT -> CI.Coq_binop (CI.Coq_mod, x , y, bt)
    | LT -> (if enc_prop then
                CI.Coq_binop (CI.Coq_lt_prop, x , y, bt) 
              else 
                CI.Coq_binop (CI.Coq_lt, x , y, bt))
    | LE -> (if enc_prop then
                CI.Coq_binop (CI.Coq_le_prop, x , y, bt) 
              else 
                CI.Coq_binop (CI.Coq_le, x , y, bt))
    | Exp -> CI.Coq_binop (CI.Coq_exp, x , y, bt)
    | ExpNoSMT -> CI.Coq_binop (CI.Coq_exp, x , y, bt)
    | BW_Xor -> CI.Coq_binop (CI.Coq_bwxor, x , y, bt)
    | BW_And -> CI.Coq_binop (CI.Coq_bwand, x , y, bt)
    | BW_Or -> CI.Coq_binop (CI.Coq_bwor, x , y, bt)
    | EQ ->
      let comp = Some (it, "argument of equality") in
      (if enc_prop then
        CI.Coq_binop (CI.Coq_eq_prop, f comp a , f comp b, bt) 
      else 
        CI.Coq_binop (CI.Coq_eq, f comp a , f comp b, bt))
    | LEPointer -> (if enc_prop then
                CI.Coq_binop (CI.Coq_le_prop, x , y, bt) 
              else 
                CI.Coq_binop (CI.Coq_le, x , y, bt))
    | LTPointer -> (if enc_prop then
                CI.Coq_binop (CI.Coq_lt_prop, x , y, bt) 
            else 
                CI.Coq_binop (CI.Coq_lt, x , y, bt))
    | And -> (if enc_prop then
                CI.Coq_binop (CI.Coq_and_prop, x , y, bt) 
            else 
                CI.Coq_binop (CI.Coq_and, x , y, bt))
    | Or -> (if enc_prop then
                CI.Coq_binop (CI.Coq_or_prop, x , y, bt) 
            else 
                CI.Coq_binop (CI.Coq_or, x , y, bt))
    | Implies -> (if enc_prop then
                CI.Coq_binop (CI.Coq_impl_prop, x , y, bt) 
            else 
                CI.Coq_binop (CI.Coq_impl, x , y, bt))
    | _ -> CI.Coq_unsupported)
  | IT.Match (x, cases) -> 
    let comp = Some (it, "case-discriminant") in
    let br (pat, rhs) = (pat_to_coq_ir pat, aux rhs) in
    CI.Coq_match (f comp x, List.map br cases)
  | IT.ITE (sw, x, y) ->
    let comp = Some (it, "if-condition") in
    CI.Coq_ite (f comp sw, aux x, aux y)
  | IT.EachI ((i1, (s, t), i2), x) -> CI.Coq_eachI((i1, (CI.Coq_sym s, bt_to_coq_ir global t), i2), aux x)
  | IT.MapSet (m, x, y) -> CI.Coq_mapset(aux m, aux x, aux y)
  | IT.MapGet (m, x) -> CI.Coq_mapget(aux m, aux x)
  | IT.RecordMember (t, m) -> 
    let flds = BT.record_bt (IT.get_bt t) in
    let ix = find_tuple_element Id.equal m (List.map fst flds) in
    CI.Coq_recordmember(aux t, CI.Coq_id m, ix)
  | IT.RecordUpdate ((t, m), x) -> 
    let flds = BT.record_bt (IT.get_bt t) in
    let ix = find_tuple_element Id.equal m (List.map fst flds) in
    CI.Coq_recordupdate((aux t , CI.Coq_id m), aux x, ix)
  | IT.Record mems -> 
    CI.Coq_record (List.map aux (List.map snd mems))
  | IT.StructMember (t, m) -> 
    let tag = BaseTypes.struct_bt (IT.get_bt t) in
    let mems, _bts = get_struct_xs global.struct_decls tag in
    let ix = find_tuple_element Id.equal m mems in
    CI.Coq_structmember(aux t, CI.Coq_id m, ix)
  | IT.StructUpdate ((t, m), x) -> 
    let tag = BaseTypes.struct_bt (IT.get_bt t) in
    let mems, _bts = get_struct_xs global.struct_decls tag in
    let ix = find_tuple_element Id.equal m mems in
    CI.Coq_structupdate((aux t , CI.Coq_id m), aux x, ix)
  | IT.Cast (cbt, t) -> CI.Coq_cast (bt_to_coq_ir global cbt, aux t)
  | IT.Apply (name, args) -> 
    let prop_ret = fun_prop_ret global name in
      let body_aux = f (if prop_ret then None else Some (it, "fun-arg")) in
    if prop_ret then 
      CI.Coq_apply_prop (CI.Coq_sym name, List.map body_aux args)
    else
      CI.Coq_apply (CI.Coq_sym name, List.map body_aux args)
  | IT.Good (ct, t2) when Option.is_some (Sctypes.is_struct_ctype ct) -> 
      (match (Sctypes.is_struct_ctype ct) with
        | Some s -> CI.Coq_good (CI.Coq_sym s, CI.Coq_Struct (CI.Coq_sym s, []), aux t2)
        | None -> CI.Coq_unsupported)
  | IT.Representable (ct, t2) when Option.is_some (Sctypes.is_struct_ctype ct) ->
      (match (Sctypes.is_struct_ctype ct) with
      | Some s -> CI.Coq_representable (CI.Coq_sym s, CI.Coq_Struct (CI.Coq_sym s, []), aux t2)
      | None -> CI.Coq_unsupported)
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
  | _ -> CI.Coq_unsupported)
  in
  (f b it)

let lc_to_coq_ir (gl : Global.t) (t: LC.t) =
  match t with
  | LC.T t -> it_to_coq_ir gl t None
  | LC.Forall ((sym, bt), it) -> CI.Coq_forall (CI.Coq_sym sym, bt_to_coq_ir gl bt, it_to_coq_ir gl it None)

let rec lrt_to_coq_ir (gl : Global.t) (t: LRT.t) =
  match t with
  | LRT.Constraint (lc, _, t) ->
    let d = lrt_to_coq_ir gl t in
    let c = lc_to_coq_ir gl lc in
    CI.Coq_Constraint_LRT (c,d)
  | LRT.Define ((sym, it), _, t) ->
    let d = lrt_to_coq_ir gl t in
    let l = it_to_coq_ir gl it None in
    CI.Coq_let(CI.Coq_sym sym, l, d)
  | LRT.I -> CI.Coq_I
  | _ -> CI.Coq_unsupported

let rec lat_to_coq_ir (gl : Global.t) (t: LRT.t LAT.t) =
  match t with
  | LAT.Define ((sym, it), _, t) ->
    let d = lat_to_coq_ir gl t in
    let l = it_to_coq_ir gl it None in
    CI.Coq_Define (CI.Coq_sym sym, l, d)
  | LAT.Constraint (lc, _, t) ->
    let c = lc_to_coq_ir gl lc in
    let d = lat_to_coq_ir gl t in
    CI.Coq_Constraint_LAT (c,d)
  | LAT.I t -> lrt_to_coq_ir gl t
  | LAT.Resource _ -> CI.Coq_unsupported

let rec lemmat_to_coq_ir (gl : Global.t) (ftyp : AT.lemmat) = 
  match ftyp with
  | AT.Computational ((sym, bt), _, t) ->
    let d = lemmat_to_coq_ir gl t in
    CI.Coq_forall (CI.Coq_sym sym, bt_to_coq_ir gl bt, d)
  | AT.L t -> lat_to_coq_ir gl t

(* Logical functions to coq_ir *)
let fun_to_coq_ir (gl : Global.t) nm =
  let open Definition.Function in
  let def = Sym.Map.find nm gl.logical_functions in
  let arg_tys = List.map (fun (nm, bt) -> 
      (CI.Coq_sym nm , bt_to_coq_ir gl bt)) def.args in
  match def.body with
  | Uninterp -> if fun_prop_ret gl nm then
    CI.Coq_fun_uninterp
      (CI.Coq_sym nm, 
      CI.Coq_uninterp_prop, 
      arg_tys, 
      bt_to_coq_ir gl def.return_bt)
    else
    CI.Coq_fun_uninterp 
      (CI.Coq_sym nm, 
      CI.Coq_uninterp, 
      arg_tys, 
      bt_to_coq_ir gl def.return_bt)
  | Def body -> 
      CI.Coq_fun_def 
        (CI.Coq_sym nm, 
        (* disclaimer: no idea if this is right but it
          stops the example from breaking because of
          prop vs bool problems  *)
        CI.Coq_def (it_to_coq_ir gl body (Some (body, "logical fun def"))), 
        arg_tys, 
        bt_to_coq_ir gl def.return_bt)
  | Rec_Def body -> 
      CI.Coq_fun_def 
        (CI.Coq_sym nm, 
        CI.Coq_recdef (it_to_coq_ir gl body (Some (body, "logical fun recdef"))),
        arg_tys, 
        bt_to_coq_ir gl def.return_bt)
        

let logical_funs_to_coq_ir (gl : Global.t) (funs : Sym.t list list) =
  let logicalfun_clump_to_coq_ir (gl : Global.t) (nms : Sym.t list) = 
    List.map (fun_to_coq_ir gl) nms
  in
  let is_uninterp a = 
    (match a with
    | CI.Coq_fun_uninterp _ -> true
    | CI.Coq_fun_def _ -> false)
  in
  let translated_funs = List.map (logicalfun_clump_to_coq_ir gl) funs in
  (List.filter (fun x -> is_uninterp (List.hd x)) translated_funs, 
   List.filter (fun x -> not (is_uninterp (List.hd x))) translated_funs)

let cn_to_coq_ir (global : Global.t) (lemmata : (Sym.t * (Loc.t * AT.lemmat)) list)
  = 
  (* 1. Translate the datatypes *)
  let translated_dtypes = 
    if Option.is_some global.datatype_order 
      then
    dtypes_to_coq_ir global (Option.get global.datatype_order)
      else
    []
   in

  (* 2. Translate the logical functions *)
   let translated_logical_funs =
    if Option.is_some global.logical_function_order 
      then
        logical_funs_to_coq_ir global (Option.get global.logical_function_order)
      else
    [],[]
   in
  (* 3. Translate the resource predicates (todo) *)
  (* 4. Translate the lemma statement *)
  let translate_lemmas ((sym : Sym.t), (_, lemmat)) = 
    let d = lemmat_to_coq_ir global lemmat in
    CI.Coq_lemmata (CI.Coq_sym sym, d)
  in
  (* gives a list of pairs: (lemma name, translated lemma)*)
  CI.Coq_everything(translated_dtypes, 
                    translated_logical_funs, 
                    [], 
                    List.map translate_lemmas lemmata)
