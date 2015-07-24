section "Simple Language Definition"

theory Lang
imports Main
begin

subsection "Language Values"

text {*
An array is a list.
*}
type_synonym 'a array = "'a list"

text {*
Currently the only scalar value is @{text int}. They can be put in 
arrays and tuples.
*}
datatype scalar_const = IntC int
datatype const = ScalarC scalar_const | TupleC const const | ArrayC "const array"

subsection "Abstract Syntax Tree"

text {* Variable bindings are handled via strings for now. *}
type_synonym var = string

text {* 
@{text exp } is the language abstract syntax tree data-type. It is
basically an extension of the lambda calculus with collective array
operations.
 *}
datatype exp = 
    Const const         (* introduce a const value *)
  | Add exp exp         (* add two scalar values *)
  | Sub exp exp         (* subtract two scalar values *)
  | Mul exp exp         (* multiply two scalar values *)
  | PrjL exp            (* project the left part of a tuple *)
  | PrjR exp            (* project the right part of a tuple *)
  | Lam var exp         (* lambda abstraction *)
  | App exp exp         (* apply a lambda function to an expression *)
  | Tup exp exp         (* create a tuple *)
  | Var var             (* look up a value in the environment *)
  | Map exp exp         (* apply a lambda function to every element in an array *)
  | Zip exp exp         (* zip two arrays to form an array of tuples *)
  | Fold exp exp exp    (* fold an array with a function and initial value *)
  | Split exp exp       (* split an array into n chunks *)
  | Join exp            (* join the chunks of an array *)

(* I'm not sure how to represent iterate. *)

datatype ty = 
    TyInt
  | TyTuple ty ty
  | TyArray ty (* not tracking size yet *)
  | TyLam ty ty

subsection "Semantics"

fun subst :: "exp \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp" where
    "subst (Const c) v e' = Const c"
  | "subst (Add e1 e2) v e' = Add (subst e1 v e') (subst e2 v e')"
  | "subst (Sub e1 e2) v e' = Sub (subst e1 v e') (subst e2 v e')"
  | "subst (Mul e1 e2) v e' = Mul (subst e1 v e') (subst e2 v e')"
  | "subst (PrjL e) v e' = PrjL (subst e v e')"
  | "subst (PrjR e) v e' = PrjR (subst e v e')"
  | "subst (Lam v' e) v e' = 
      (if v' = v then (Lam v' e) else (Lam v' (subst e v e')))"
  | "subst (App e1 e2) v e' = App (subst e1 v e') (subst e2 v e')"
  | "subst (Tup e1 e2) v e' = Tup (subst e1 v e') (subst e2 v e')"
  | "subst (Var v') v e' = 
      (if v' = v then e' else (Var v'))"
  | "subst (Map e1 e2) v e' = Map (subst e1 v e') (subst e2 v e')"
  | "subst (Zip e1 e2) v e' = Zip (subst e1 v e') (subst e2 v e')"
  | "subst (Fold e1 e2 e3) v e' = Fold (subst e1 v e') (subst e2 v e') (subst e3 v e')"
  | "subst (Split e1 e2) v e' = Split (subst e1 v e') (subst e2 v e')"
  | "subst (Join e) v e' = Join (subst e v e')"

text {* 
The semantics of the language are given via an inductive relation
from @{text exp} to @{text result}, which is either @{text exp} or an error.
*}

datatype result = Res exp | Error

inductive
  eval :: "exp \<Rightarrow> result \<Rightarrow> bool" (infix "\<leadsto>" 70)
where
    Const: "(Const c) \<leadsto> Res (Const c)"
  | Add: "\<lbrakk> (e1) \<leadsto> Res (Const (ScalarC (IntC c1))); (e2) \<leadsto> Res (Const (ScalarC (IntC c2))) \<rbrakk>
           \<Longrightarrow> (Add e1 e2) \<leadsto> Res (Const (ScalarC (IntC (c1 + c2))))"
  | Sub: "\<lbrakk> (e1) \<leadsto> Res (Const (ScalarC (IntC c1))); (e2) \<leadsto> Res (Const (ScalarC (IntC c2))) \<rbrakk>
           \<Longrightarrow> (Add e1 e2) \<leadsto> Res (Const (ScalarC (IntC (c1 - c2))))"
  | Mul: "\<lbrakk> (e1) \<leadsto> Res (Const (ScalarC (IntC c1))); (e2) \<leadsto> Res (Const (ScalarC (IntC c2))) \<rbrakk>
           \<Longrightarrow> (Add e1 e2) \<leadsto> Res (Const (ScalarC (IntC (c1 * c2))))"
  | PrjL: "\<lbrakk> (e) \<leadsto> Res (Const (TupleC c1 c2)) \<rbrakk>
           \<Longrightarrow> (PrjL e) \<leadsto> Res (Const c1)"
  | PrjR: "\<lbrakk> (e) \<leadsto> Res (Const (TupleC c1 c2)) \<rbrakk>
           \<Longrightarrow> (PrjL e) \<leadsto> Res (Const c2)"
  | Lam: "(Lam v e) \<leadsto> Res (Lam v e)"
  | App: "\<lbrakk> (e1) \<leadsto> Res (Lam v e); (e2) \<leadsto> Res e2'; (subst e v e2') \<leadsto> e' \<rbrakk>
          \<Longrightarrow> (App e1 e2) \<leadsto> e'"
  | Var: "(Var _) \<leadsto> Error"
(*  | Map: "\<lbrakk> (e1) \<leadsto> Res (Lam v e); (e2) \<leadsto> Res e2'; *)

end