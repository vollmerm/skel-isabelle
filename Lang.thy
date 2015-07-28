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
    C int
  | Add exp exp         (infix "+" 70)
  | Sub exp exp         (infix "-" 70)
  | Mul exp exp         (infix "*" 70)
  | PrjL exp
  | PrjR exp
  | Lam var exp
  | App exp exp         (infix "$" 70)
  | Tup exp exp         (infix "\<times>" 70)
  | A "exp array"
  | Var var
  | Map exp exp         (infix "m\<Rightarrow>" 60)
  | Zip exp exp         (infix "z\<Rightarrow>" 60)
  | Fold exp exp exp    (infix "[_]f\<Rightarrow>" 60)
  | Split exp exp       (infix "s\<Rightarrow>" 60)
  | Join exp

(* I'm not sure how to represent iterate. *)

datatype ty = 
    TyInt
  | TyTuple ty ty
  | TyA ty (* not tracking size yet *)
  | TyLam ty ty

subsection "Semantics"

fun subst :: "exp \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp" (infix "[_]\<leadsto>" 70) where
    "(C c) [v]\<leadsto> e' = C c"
  | "(e1 + e2) [v]\<leadsto> e' = (e1 [v]\<leadsto> e') + (e2 [v]\<leadsto> e')"
  | "(e1 - e2) [v]\<leadsto> e' = (e1 [v]\<leadsto> e') - (e2 [v]\<leadsto> e')"
  | "(e1 * e2) [v]\<leadsto> e' = (e1 [v]\<leadsto> e') * (e2 [v]\<leadsto> e')"
  | "(PrjL e) [v]\<leadsto> e' = PrjL (e [v]\<leadsto> e')"
  | "(PrjR e) [v]\<leadsto> e' = PrjR (e [v]\<leadsto> e')"
  | "(Lam v' e) [v]\<leadsto> e' = 
      (if v' = v then (Lam v' e) else (Lam v' (e [v]\<leadsto> e')))"
  | "(e1 $ e2) [v]\<leadsto> e' = (e1 [v]\<leadsto> e') $ (e2 [v]\<leadsto> e')"
  | "(e1 \<times> e2) [v]\<leadsto> e' = (e1 [v]\<leadsto> e') \<times> (e2 [v]\<leadsto> e')"
  | "(A es) [v]\<leadsto> e' = A (map (\<lambda>i. i [v]\<leadsto> e') es)"
  | "(Var v') [v]\<leadsto> e' = 
      (if v' = v then e' else (Var v'))"
  | "(e1 m\<Rightarrow> e2) [v]\<leadsto> e' = (e1 [v]\<leadsto> e') m\<Rightarrow> (e2 [v]\<leadsto> e')"
  | "(e1 z\<Rightarrow> e2) [v]\<leadsto> e' = (e1 [v]\<leadsto> e') z\<Rightarrow> (e2 [v]\<leadsto> e')"
  | "(e1 [e2]f\<Rightarrow> e3) [v]\<leadsto> e' = (e1 [v]\<leadsto> e') [(e2 [v]\<leadsto> e')]f\<Rightarrow> (e3 [v]\<leadsto> e')"
  | "(e1 s\<Rightarrow> e2) [v]\<leadsto> e' = (e1 [v]\<leadsto> e') s\<Rightarrow> (e2 [v]\<leadsto> e')"
  | "(Join e) [v]\<leadsto> e' = Join (e [v]\<leadsto> e')"

text {* 
The semantics of the language are given via an inductive relation
from @{text exp} to @{text result}, which is either @{text exp} or an error.
*}

datatype result = 
    R exp 
  | Error

inductive
  evalr :: "exp \<Rightarrow> result \<Rightarrow> bool" (infix "\<mapsto>" 70)
where
    Int[intro!]: "(C c) \<mapsto> R (C c)"
  | Add[intro!]: "\<lbrakk> e1 \<mapsto> R (C c1); e2 \<mapsto> R (C c2) \<rbrakk>
          \<Longrightarrow> (e1 + e2) \<mapsto> R (C (c1 + c2))"
  | Sub[intro!]: "\<lbrakk> e1 \<mapsto> R (C c1); e2 \<mapsto> R (C c2) \<rbrakk>
          \<Longrightarrow> (e1 - e2) \<mapsto> R (C (c1 - c2))"
  | Mul[intro!]: "\<lbrakk> e1 \<mapsto> R (C c1); e2 \<mapsto> R (C c2) \<rbrakk>
          \<Longrightarrow> (e1 * e2) \<mapsto> R (C (c1 * c2))"
  | PrjL[intro!]: "\<lbrakk> e \<mapsto> R (Tup c1 c2) \<rbrakk>
          \<Longrightarrow> (PrjL e) \<mapsto> R c1"
  | PrjR[intro!]: "\<lbrakk> e \<mapsto> R (Tup c1 c2) \<rbrakk>
          \<Longrightarrow> (PrjR e) \<mapsto> R c2"
  | Lam[intro!]: "(Lam v e) \<mapsto> R (Lam v e)"
  | App[intro!]: "\<lbrakk> e1 \<mapsto> R (Lam v e); e2 \<mapsto> R e2'; (e [v]\<leadsto> e2') \<mapsto> e' \<rbrakk>
          \<Longrightarrow> (e1 $ e2) \<mapsto> e'"
  | Tup[intro!]: "\<lbrakk> e1 \<mapsto> R e1'; e2 \<mapsto> R e2' \<rbrakk> \<Longrightarrow> (e1 \<times> e2) \<mapsto> R (e1' \<times> e2')"
  | Array1[intro!]: "(A []) \<mapsto> R (A [])"
  | Array2[intro!]: "\<lbrakk> (A es) \<mapsto> R (A as); e \<mapsto> R e' \<rbrakk>
          \<Longrightarrow> (A (e # es)) \<mapsto> R (A (e' # as))"
  | Var[intro!]: "(Var _) \<mapsto> Error"
  | Map1[intro!]: "\<lbrakk> e2 \<mapsto> R (A []) \<rbrakk>
          \<Longrightarrow> (e1 m\<Rightarrow> e2) \<mapsto> R (A [])"
  | Map2[intro!]: "\<lbrakk> e1 \<mapsto> R (Lam v e); e2 \<mapsto> R (A (a # as));
            ((Lam v e) m\<Rightarrow> (A as)) \<mapsto> R (A as'); ((Lam v e) $ a) \<mapsto> R a' \<rbrakk>
          \<Longrightarrow> (e1 m\<Rightarrow> e2) \<mapsto> R (A (a' # as'))"
  | Zip1[intro!]: "\<lbrakk> e2 \<mapsto> R (A []) \<rbrakk>
          \<Longrightarrow> (e1 z\<Rightarrow> e2) \<mapsto> R (A [])"
  | Zip2[intro!]: "\<lbrakk> e1 \<mapsto> R (A []) \<rbrakk>
          \<Longrightarrow> (e1 z\<Rightarrow> e2) \<mapsto> R (A [])"
  | Zip3[intro!]: "\<lbrakk> e1 \<mapsto> R (A (a1 # a1s)); e2 \<mapsto> R (A (a2 # a2s));
            ((A a1s) z\<Rightarrow> (A a2s)) \<mapsto> R (A as) \<rbrakk>
          \<Longrightarrow> (e1 z\<Rightarrow> e2) \<mapsto> R (A ((a1 \<times> a2) # as))"
(* TODO: Fold Split Join *)

lemma add_int[simp]:"(Add (C x) (C y)) \<mapsto> (R (C (x+y)))"
by (auto)
lemma sub_int[simp]:"(Sub (C x) (C y)) \<mapsto> (R (C (x-y)))" 
by (auto)
lemma mul_int[simp]: "(Mul (C x) (C y)) \<mapsto> (R (C (x*y)))"
by (auto)

(* tests *)
lemma "(Mul (C 1) (C 2)) \<mapsto> R (C 2)"
by (metis mul_int mult.left_neutral)
lemma "(Add (C 1) (C 2)) \<mapsto> R (C 3)"
by (metis add_int one_plus_numeral semiring_norm(3))
lemma "(Map (Lam x (Add (Var x) (C 1))) (A [(C 1),(C 2),(C 3)])) \<mapsto> R (A [(C 2),(C 3),(C 4)])"
apply auto apply (smt add_int)+ done


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
