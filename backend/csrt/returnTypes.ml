open Subst

module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)


type l = 
  | Logical of (Sym.t * LS.t) * l
  | Resource of RE.t * l
  | Constraint of LC.t * l
  | I

type t = Computational of (Sym.t * BT.t) * l


let mcomputational (name,bound) t = Computational ((name,bound),t)
let mlogical (name,bound) t = Logical ((name,bound),t)
let mconstraint bound t = Constraint (bound,t)
let mresource bound t = Resource (bound,t)



let rec (@@) (t1: l) (t2: l) : l = 
  match t1 with
  | I -> t2
  (* | Computational (name,bound,t) -> 
   *    Computational (name,bound, t@@t2) *)
  | Logical ((name,bound),t) -> 
     Logical ((name,bound), t@@t2)
  | Resource (bound,t) -> 
     Resource (bound, t@@t2)
  | Constraint (bound,t) -> 
     Constraint (bound, t@@t2)


let rec subst_var_l substitution = function
  | I -> I
  | Logical ((name,ls),t) -> 
     if name = substitution.s then 
       Logical ((name,ls),t) 
     else if SymSet.mem name (IT.vars_in substitution.swith) then
       let newname = Sym.fresh () in
       let t' = subst_var_l {s=name; swith=IT.S newname} t in
       let t'' = subst_var_l substitution t' in
       Logical ((newname,ls),t'')
     else
       let t' = subst_var_l substitution t in
       Logical ((name,ls),t')
  | Resource (re,t) -> 
     let re = RE.subst_var substitution re in
     let t = subst_var_l substitution t in
     Resource (re,t)
  | Constraint (lc,t) -> 
     let lc = LC.subst_var substitution lc in
     let t = subst_var_l substitution t in
     Constraint (lc,t)

let subst_var substitution = function
  | Computational ((name,bt),t) -> 
     if name = substitution.s then 
       Computational ((name,bt),t) 
     else if SymSet.mem name (IT.vars_in substitution.swith) then
       let newname = Sym.fresh () in
       let t' = subst_var_l {s=name; swith=IT.S newname} t in
       let t'' = subst_var_l substitution t' in
       Computational ((newname,bt),t'')
     else
       Computational ((name,bt),subst_var_l substitution t)

let subst_vars = Subst.make_substs subst_var


let rec free_vars_l = function
  | Logical ((sym,_),t) -> SymSet.remove sym (free_vars_l t)
  | Resource (r,t) -> SymSet.union (RE.vars_in r) (free_vars_l t)
  | Constraint (c,t) -> SymSet.union (LC.vars_in c) (free_vars_l t)
  | I -> SymSet.empty

let free_vars = function
  | Computational ((sym,_),t) -> SymSet.remove sym (free_vars_l t)



let rec instantiate_struct_member_l subst rt =
  match rt with
  | I -> I
  | Logical ((name,bound),t) -> 
     Logical ((name,bound),instantiate_struct_member_l subst t)
  | Resource (bound,t) -> 
     Resource (RE.instantiate_struct_member subst bound, 
               instantiate_struct_member_l subst t)
  | Constraint (bound,t) -> 
     Constraint (LC.instantiate_struct_member subst bound, 
                 instantiate_struct_member_l subst t)

let instantiate_struct_member subst = function
  | Computational ((name,bound),t) -> 
     Computational ((name,bound),instantiate_struct_member_l subst t)


let (pp,pp_l) = 
  
  let open Pp in

  let rec aux_l = function
    | Logical ((name,ls),t) ->
       let op = if !unicode then utf8string "\u{2203}" else !^"E" in
       (op ^^^ typ (Sym.pp name) (LS.pp false ls) ^^ dot) :: aux_l t
    | Resource (re,t) ->
       let op = if !unicode then utf8string "\u{2217}" else star in
       (RE.pp false re ^^^ op) :: aux_l t
    | Constraint (lc,t) ->
       let op = if !unicode then utf8string "\u{2227}" else slash ^^ backslash in
       (LC.pp false lc ^^^ op) :: aux_l t
    | I -> 
       [!^"I"]
  in

  let aux = function
    | Computational ((name,bt),t) ->
       let op = if !unicode then utf8string "\u{03A3}" else !^"EC" in
       (op ^^^ typ (Sym.pp name) (BT.pp false bt) ^^ dot) :: aux_l t
  in

  let pp_l rt = flow (break 1) (aux_l rt) in
  let pp rt = flow (break 1) (aux rt) in

  (pp,pp_l)



module NRT = NReturnTypes

let normalise_l rt : (NRT.l) = 
  let rec aux l r c = function
    | Logical ((name,ls),rt) -> aux (l@[(name,ls)]) r c rt
    | Resource (re,rt) -> aux l (r@[re]) c rt
    | Constraint (lc,rt) -> aux l r (c@[lc]) rt
    | I ->
       (List.fold_right NRT.mlogical l)
         (NRT.R ((List.fold_right NRT.mresource r)
                   (NRT.C (List.fold_right NRT.mconstraint c NRT.I))))
  in
  aux [] [] [] rt

let normalise_a rt : (NRT.t) =
  match rt with
  | Computational ((name,bt),rt) -> 
     NRT.Computational ((name,bt), normalise_l rt)

let normalise = normalise_a


let rec unnormalise_c = function
  | NRT.Constraint (lc,t) -> Constraint (lc,unnormalise_c t)
  | NRT.I -> I

let rec unnormalise_r = function
  | NRT.Resource (re,t) -> Resource (re,unnormalise_r t)
  | NRT.C t -> unnormalise_c t

let rec unnormalise_l = function
  | NRT.Logical ((name,ls),t) -> Logical ((name,ls),unnormalise_l t)
  | NRT.R t -> unnormalise_r t

let unnormalise_a = function
  | NRT.Computational ((name,bt),t) -> Computational ((name,bt),unnormalise_l t)

let unnormalise = unnormalise_a
