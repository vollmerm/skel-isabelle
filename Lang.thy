section "Simple Language Definition"

(*<*)
theory Lang
imports Main LaTeXsugar
begin
(*>*)

subsection "Language Values"

text {*
An array is a list.
*}
type_synonym 'a array = "'a list"

subsection "Abstract Syntax Tree"

text {* Variable bindings are handled via strings for now. *}
type_synonym var = string

text {* 
@{text exp } is the language abstract syntax tree data-type. It is
basically an extension of the lambda calculus with collective array
operations.
 *}
datatype exp = 
    CInt int            (* introduce a constant int value *)
  | Add exp exp         (* add two scalar values *)
  | Sub exp exp         (* subtract two scalar values *)
  | Mul exp exp         (* multiply two scalar values *)
  | PrjL exp            (* project the left part of a tuple *)
  | PrjR exp            (* project the right part of a tuple *)
  | Lam var exp         (* lambda abstraction *)
  | App exp exp         (* apply a lambda function to an expression *)
  | Tup exp exp         (* a tuple *)
  | Array "exp array"   (* an array of expressions *)
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
    "subst (CInt c) v e' = CInt c"
  | "subst (Add e1 e2) v e' = Add (subst e1 v e') (subst e2 v e')"
  | "subst (Sub e1 e2) v e' = Sub (subst e1 v e') (subst e2 v e')"
  | "subst (Mul e1 e2) v e' = Mul (subst e1 v e') (subst e2 v e')"
  | "subst (PrjL e) v e' = PrjL (subst e v e')"
  | "subst (PrjR e) v e' = PrjR (subst e v e')"
  | "subst (Lam v' e) v e' = 
      (if v' = v then (Lam v' e) else (Lam v' (subst e v e')))"
  | "subst (App e1 e2) v e' = App (subst e1 v e') (subst e2 v e')"
  | "subst (Tup e1 e2) v e' = Tup (subst e1 v e') (subst e2 v e')"
  | "subst (Array es) v e' = Array (map (\<lambda>i. subst i v e') es)"
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
  evalr :: "exp \<Rightarrow> result \<Rightarrow> bool" (infix "\<mapsto>" 70)
where
    Int[intro!]: "(CInt c) \<mapsto> Res (CInt c)"
  | Add[intro!]: "\<lbrakk> e1 \<mapsto> Res (CInt c1); e2 \<mapsto> Res (CInt c2) \<rbrakk>
          \<Longrightarrow> (Add e1 e2) \<mapsto> Res (CInt (c1 + c2))"
  | Sub[intro!]: "\<lbrakk> e1 \<mapsto> Res (CInt c1); e2 \<mapsto> Res (CInt c2) \<rbrakk>
          \<Longrightarrow> (Sub e1 e2) \<mapsto> Res (CInt (c1 - c2))"
  | Mul[intro!]: "\<lbrakk> (e1) \<mapsto> Res (CInt c1); (e2) \<mapsto> Res (CInt c2) \<rbrakk>
          \<Longrightarrow> (Mul e1 e2) \<mapsto> Res (CInt (c1 * c2))"
  | PrjL[intro!]: "\<lbrakk> (e) \<mapsto> Res (Tup c1 c2) \<rbrakk>
          \<Longrightarrow> (PrjL e) \<mapsto> Res c1"
  | PrjR[intro!]: "\<lbrakk> (e) \<mapsto> Res (Tup c1 c2) \<rbrakk>
          \<Longrightarrow> (PrjR e) \<mapsto> Res c2"
  | Lam[intro!]: "(Lam v e) \<mapsto> Res (Lam v e)"
  | App[intro!]: "\<lbrakk> (e1) \<mapsto> Res (Lam v e); (e2) \<mapsto> Res e2'; (subst e v e2') \<mapsto> e' \<rbrakk>
          \<Longrightarrow> (App e1 e2) \<mapsto> e'"
  | Array1[intro!]: "(Array []) \<mapsto> Res (Array [])"
  | Array2[intro!]: "\<lbrakk> (Array es) \<mapsto> Res (Array as); (e) \<mapsto> Res e' \<rbrakk>
          \<Longrightarrow> (Array (e # es)) \<mapsto> Res (Array (e' # as))"
  | Var[intro!]: "(Var _) \<mapsto> Error"
  | Map1[intro!]: "\<lbrakk> (e1) \<mapsto> Res (Lam v e); (e2) \<mapsto> Res (Array []) \<rbrakk>
          \<Longrightarrow> (Map e1 e2) \<mapsto> Res (Array [])"
  | Map2[intro!]: "\<lbrakk> (e1) \<mapsto> Res (Lam v e); (e2) \<mapsto> Res (Array (a # as));
            (Map (Lam v e) (Array as)) \<mapsto> Res (Array as'); (Apply (Lam v e) a) \<mapsto> Res a' \<rbrakk>
          \<Longrightarrow> (Map e1 e2) \<mapsto> Res (Array (a' # as'))"
  | Zip1[intro!]: "\<lbrakk> (e2) \<mapsto> Res (Array []) \<rbrakk>
          \<Longrightarrow> (Zip e1 e2) \<mapsto> Res (Array [])"
  | Zip2[intro!]: "\<lbrakk> (e1) \<mapsto> Res (Array []) \<rbrakk>
          \<Longrightarrow> (Zip e1 e2) \<mapsto> Res (Array [])"
  | Zip3[intro!]: "\<lbrakk> (e1) \<mapsto> Res (Array (a1 # a1s)); (e2) \<mapsto> Res (Array (a2 # a2s));
            (Zip (Array a1s) (Array a2s)) \<mapsto> Res (Array as) \<rbrakk>
          \<Longrightarrow> (Zip e1 e2) \<mapsto> Res (Array ((Tup a1 a2) # as))"
(* TODO: Fold Split Join *)

lemma add_int[simp]:"(Add (CInt x) (CInt y)) \<mapsto> (Res (CInt (x+y)))"
by (auto)
lemma sub_int[simp]:"(Sub (CInt x) (CInt y)) \<mapsto> (Res (CInt (x-y)))" 
by (auto)
lemma mul_int[simp]: "(Mul (CInt x) (CInt y)) \<mapsto> (Res (CInt (x*y)))"
by (auto)

(* tests *)
lemma "(Mul (CInt 1) (CInt 2)) \<mapsto> Res (CInt 2)"
by (metis mul_int mult.left_neutral)
lemma "(Add (CInt 1) (CInt 2)) \<mapsto> Res (CInt 3)"
by (metis add_int one_plus_numeral semiring_norm(3))



text{*
\begin{figure}
@{thm[mode=Rule] App [no_vars]} {\sc App} \\[1ex]
\vspace{10 mm}
@{thm[mode=Axiom] Lam [no_vars]} {\sc Lam} \\[1ex]
\vspace{10 mm}
@{thm[mode=Rule] Add [no_vars]} {\sc Add} \\[1ex]
\vspace{10 mm}
@{thm[mode=Rule] Sub [no_vars]} {\sc Sub} \\[1ex]
\vspace{10 mm}
@{thm[mode=Rule] Mul [no_vars]} {\sc Mul} \\[1ex]
\vspace{10 mm}
@{thm[mode=Axiom] Int [no_vars]} {\sc Int} \\[1ex]
\vspace{10 mm}
@{thm[mode=Rule] PrjL [no_vars]} {\sc Prj$_L$} \qquad
@{thm[mode=Rule] PrjR [no_vars]} {\sc Prj$_R$} \\[1ex]
\vspace{10 mm}
\end{figure}

\begin{figure}
@{thm[mode=Axiom] Array1 [no_vars]} {\sc Array$_1$} \\[1ex]
\vspace{10 mm}
@{thm[mode=Rule] Array2 [no_vars]} {\sc Array$_2$} \\[1ex]
\vspace{10 mm}
@{thm[mode=Rule] Map1 [no_vars]} {\sc Map$_1$} \\[1ex]
\vspace{10 mm}
@{thm[mode=Rule] Map2 [no_vars]} {\sc Map$_2$} \\[1ex]
\vspace{10 mm}
@{thm[mode=Rule] Zip1 [no_vars]} {\sc Zip$_1$} \qquad
@{thm[mode=Rule] Zip2 [no_vars]} {\sc Zip$_2$} \\[1ex]
\vspace{10 mm}
@{thm[mode=Rule] Zip3 [no_vars]} {\sc Zip$_3$} \\[1ex]
\end{figure}
*}

end
