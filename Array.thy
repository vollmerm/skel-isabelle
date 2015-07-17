theory Array
imports Main
begin

type_synonym var = string

datatype val = Scl int 
datatype prim1 = Inc | Dec
datatype prim2 = Add | Sub
codatatype exp = 
    Val val 
  | Var var
  | Prim1 prim1 exp 
  | Prim2 prim2 exp exp
  | App lam exp 
  | Arr nat lam
  | Map lam exp
  | Reduce lam exp 
  | Split exp exp 
  | Join exp exp
and lam = 
    Lam var exp 
  | Compose lam lam

fun lookup :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup k [] = None" |
  "lookup k ((k',v)#ls) = (if k = k' then Some v else lookup k ls)"

type_synonym env  = "(var \<times> exp) list"

datatype result = Res exp | Error

inductive eval :: "exp \<Rightarrow> env \<Rightarrow> result \<Rightarrow> bool" where
    Val: "eval (Val v) \<rho> (Res (Val v))"
  | Var: "eval (Var v) \<rho>
      (case (lookup v \<rho>) of
        Some d \<Rightarrow> Res d
      | None \<Rightarrow> Error)"
  | Arr: "eval (Arr n l) \<rho> (Res (Arr n l))"
  | Map: "\<lbrakk> eval e \<rho> (Res (Arr n l2)) \<rbrakk> \<Longrightarrow> 
      eval (Map l1 e) \<rho> (Res (Arr n (Compose l1 l2)))"


(*
type_synonym var = string

datatype val = 
    Scl int
  | Tup val val
  | Arr nat "nat \<Rightarrow> val"
  | Null

datatype prim = Sum | Diff | Inc | Dec | Left | Right

datatype aexp = 
    Val val
  | Var var
  | Prim prim aexp
  | Lam var aexp
  | App aexp aexp
  | Compose aexp aexp aexp
  | Map aexp aexp
  | Reduce aexp aexp
  | Split aexp aexp
  | Join aexp

datatype result = Res aexp | Error

fun lookup :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup k [] = None" |
  "lookup k ((k',v)#ls) = (if k = k' then Some v else lookup k ls)"

fun eval_prim :: "prim \<Rightarrow> val \<Rightarrow> val" where
  "eval_prim Sum (Tup (Scl x1) (Scl x2)) =  (Scl (x1+x2))" |
  "eval_prim Diff (Tup (Scl x1) (Scl x2)) =  (Scl (x1-x2))" |
  "eval_prim Inc (Scl x1) =  (Scl (x1+1))" |
  "eval_prim Dec (Scl x1) =  (Scl (x1-1))" |
  "eval_prim Left (Tup a b) =  a" |
  "eval_prim Right (Tup a b) =  b" |
  "eval_prim _ _ = Null"

fun subst :: "aexp \<Rightarrow> var \<Rightarrow> val \<Rightarrow> aexp" where
  "subst (Val d') v d = (Val d')" |
  "subst (Lam v' ae) v d = 
    (if v' = v 
     then (Lam v' ae) 
     else (Lam v' (subst ae v d)))" |
  "subst (Var v') v d = 
    (if v' = v
     then (Val d)
     else (Var v'))" |
  "subst (Prim p ae) v d = (Prim p (subst ae v d))" |
  "subst (App ae1 ae2) v d = (App (subst ae1 v d)  (subst ae2 v d))" |
  "subst (Compose ae1 ae2 ae3) v d = (Compose (subst ae1 v d)  (subst ae2 v d) (subst ae3 v d))" |
  "subst (Map ae1 ae2) v d = (Map (subst ae1 v d)  (subst ae2 v d))" |
  "subst (Reduce ae1 ae2) v d = (Reduce (subst ae1 v d)  (subst ae2 v d))" |
  "subst (Split ae1 ae2) v d = (Split (subst ae1 v d)  (subst ae2 v d))" |
  "subst (Join ae) v d = (Join (subst ae v d))"

inductive 
  red :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<longmapsto>" 70)
where
    Val: "(Val d) \<longmapsto> (Val d)"
  | Var: "(Var v) \<longmapsto> (Var v)"
  | Lam: "(Lam v ae) \<longmapsto> (Lam v ae)"
  | Prim: "\<lbrakk> ae \<longmapsto> (Val d) \<rbrakk> \<Longrightarrow> (Prim p ae) \<longmapsto> (Val (eval_prim p d))"
  | App: "\<lbrakk> ae \<longmapsto> (Val d) \<rbrakk> \<Longrightarrow> (App (Lam v ae) ae) \<longmapsto> (subst ae v d)" 
  | Compose: "\<lbrakk> ae \<longmapsto> (Val d) \<rbrakk> \<Longrightarrow> (Compose (Lam v1 ae1') (Lam v2 ae2') ae) \<longmapsto> 
      (App (Lam v1 ae1')
           (App (Lam v2 ae2') (Val d)))" 
  | Map: "\<lbrakk> ae \<longmapsto> (Val d) \<rbrakk> \<Longrightarrow> (Map (Lam v1 ae1') ae) \<longmapsto> 
*)
(*
type_synonym 'a arr_elem = "nat \<Rightarrow> 'a"
type_synonym var = string

codatatype data =
    Scalar int
  | Array nat "data arr_elem"
  | Closure var exp "(var \<times> data) list"
  | Null
and exp =
    Lambda var exp
  | Value data
  | Variable var
  | Map exp exp
  | Split exp exp
  | Join exp

primrec list_to_arr_elem :: "nat \<Rightarrow> data list \<Rightarrow> data arr_elem" where
  "list_to_arr_elem _ [] = (\<lambda>_. Null)" |
  "list_to_arr_elem n (x # xs) =
    (let f = (list_to_arr_elem (Suc n) xs)
     in (\<lambda>i. if i = n then x else f i))"

fun list_to_array :: "data list \<Rightarrow> data" where
  "list_to_array xs = Array (length xs) (list_to_arr_elem 0 xs)"

type_synonym env = "(var \<times> data) list"




fun lookup_or_null :: "var \<Rightarrow> env \<Rightarrow> data" where
  "lookup_or_null v e = (case lookup v e of
                           Some d \<Rightarrow> d
                         | None \<Rightarrow> Null)"

inductive
  evalr :: "exp \<Rightarrow> env \<Rightarrow> data \<Rightarrow> bool"
where
    Lambda: "evalr (Lambda v c) e (Closure v c e)"
  | Value: "evalr (Value d) e d"
  | Variable: "evalr (Variable v) e (lookup_or_null v e)"
*)
end