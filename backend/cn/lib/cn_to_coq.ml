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
  | BaseTypes.Bits _ -> CI.Coq_Bits
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

(* index terms to coq_ir *)
let it_to_coq_ir global it =
  let rec f comp_bool it =
    let aux t = f comp_bool t in
    let enc_prop = Option.is_none comp_bool in
  (match IT.get_term it with
  | IT.Sym s -> CI.Coq_sym_term (CI.Coq_sym s)
  | IT.Const l ->
    (match l with
      | IT.Bool b -> if enc_prop && BaseTypes.equal (IT.get_bt it) BaseTypes.Bool then
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
    | BW_Xor -> CI.Coq_binop (CI.Coq_bwxor, x , y)
    | BW_And -> CI.Coq_binop (CI.Coq_bwand, x , y)
    | BW_Or -> CI.Coq_binop (CI.Coq_bwor, x , y)
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
    | And -> (if enc_prop then
                CI.Coq_binop (CI.Coq_and_prop, x , y) 
            else 
                CI.Coq_binop (CI.Coq_and, x , y))
    | Or -> (if enc_prop then
                CI.Coq_binop (CI.Coq_or_prop, x , y) 
            else 
                CI.Coq_binop (CI.Coq_or, x , y))
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
  | IT.EachI ((i1, (s, t), i2), x) -> CI.Coq_eachI((i1, (CI.Coq_sym s, bt_to_coq_ir global t), i2), aux x)
  | IT.MapSet (m, x, y) -> CI.Coq_mapset(aux m, aux x, aux y)
  | IT.MapGet (m, x) -> CI.Coq_mapget(aux m, aux x)
  | IT.RecordMember (t, m) -> CI.Coq_recordmember(aux t, CI.Coq_id m)
  | IT.RecordUpdate ((t, m), x) -> CI.Coq_recordupdate((aux t , CI.Coq_id m), aux x)
  | IT.Record mems -> CI.Coq_record (List.map aux (List.map snd mems))
  | IT.StructMember (t, m) -> CI.Coq_structmember(aux t, CI.Coq_id m)
  | IT.StructUpdate ((t, m), x) -> CI.Coq_structupdate((aux t , CI.Coq_id m), aux x)
  | IT.Cast (cbt, t) -> CI.Coq_cast (bt_to_coq_ir global cbt, aux t)
  | IT.Apply (name, args) -> 
    let body_aux = f (Some (it, "fun-arg")) in
    let open Definition.Function in
    let def = Sym.Map.find name global.Global.logical_functions in
    (match def.body with
      | Uninterp -> 
          if fun_prop_ret global name then
            CI.Coq_app_uninterp (CI.Coq_sym name, List.map body_aux args)
          else
            CI.Coq_app_uninterp_prop (CI.Coq_sym name, List.map body_aux args)
      | Def _ -> CI.Coq_app_def (CI.Coq_sym name, List.map body_aux args)
      | Rec_Def _ -> CI.Coq_app_recdef)
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
  (f None it)

let lc_to_coq_ir (gl : Global.t) (t: LC.t) =
  match t with
  | LC.T t -> it_to_coq_ir gl t
  | LC.Forall ((sym, bt), it) -> CI.Coq_forall (CI.Coq_sym sym, bt_to_coq_ir gl bt, it_to_coq_ir gl it)

let rec lrt_to_coq_ir (gl : Global.t) (t: LRT.t) =
  match t with
  | LRT.Constraint (lc, _, t) ->
    let d = lrt_to_coq_ir gl t in
    let c = lc_to_coq_ir gl lc in
    CI.Coq_Constraint_LRT (c,d)
  | LRT.Define ((sym, it), _, t) ->
    let d = lrt_to_coq_ir gl t in
    let l = it_to_coq_ir gl it in
    CI.Coq_let(CI.Coq_sym sym, l, d)
  | LRT.I -> CI.Coq_I
  | _ -> CI.Coq_unsupported

let rec lat_to_coq_ir (gl : Global.t) (t: LRT.t LAT.t) =
  match t with
  | LAT.Define ((sym, it), _, t) ->
    let d = lat_to_coq_ir gl t in
    let l = it_to_coq_ir gl it in
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
        CI.Coq_def (it_to_coq_ir gl body), 
        arg_tys, 
        bt_to_coq_ir gl def.return_bt)
  | Rec_Def _ -> 
      CI.Coq_fun_def 
        (CI.Coq_sym nm, 
        CI.Coq_recdef, 
        [], 
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
