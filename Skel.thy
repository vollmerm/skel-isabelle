theory Skel
imports Main
begin

datatype scalar_unary = Inc | Dec

datatype scalar_binary = Add | Mul | Sub
(* no division here makes my life easier *)

datatype scalar_const = IntC int

fun eval_scalar_unary :: "scalar_unary \<Rightarrow> scalar_const \<Rightarrow> scalar_const" where
  "eval_scalar_unary Inc (IntC n) = IntC (n + 1)" |
  "eval_scalar_unary Dec (IntC n) = IntC (n - 1)"

fun eval_scalar_binary :: "scalar_binary \<Rightarrow> scalar_const \<Rightarrow> scalar_const \<Rightarrow> scalar_const" where
  "eval_scalar_binary Add (IntC i) (IntC j) = IntC (i + j)" |
  "eval_scalar_binary Mul (IntC i) (IntC j) = IntC (i * j)" |
  "eval_scalar_binary Sub (IntC i) (IntC j) = IntC (i - j)" 

type_synonym var = nat

datatype exp = Const scalar_const
  | Unary scalar_unary exp
  | Binary scalar_binary exp
  | FVar var | BVar var 
  | LambdaE exp | AppE exp exp 
  | Map exp exp | Zip exp exp | Reduce exp exp exp
  | Split exp exp | Join exp
  | Iterate exp exp exp

abbreviation list_max :: "nat list \<Rightarrow> nat" where
  "list_max ls \<equiv> foldr max ls (0::nat)"
  
lemma list_max_fresh: fixes n::nat assumes g: "list_max ls < n" shows "n \<notin> set ls"
using g by (induction ls arbitrary: n) auto

abbreviation mklet :: "exp \<Rightarrow> exp \<Rightarrow> exp" where
  "mklet e1 e2 \<equiv> AppE (LambdaE e2) e1"

primrec FV :: "exp \<Rightarrow> var list" where
  "FV (Const c) = []" |
  "FV (Prim p e) = FV e" |
  "FV (FVar v) = [v]" |
  "FV (BVar v) = []" |
  "FV (LambdaE e) = FV e" |
  "FV (AppE e1 e2) = (FV e1 @ FV e2)" |
  "FV (Map e1 e2) = (FV e1 @ FV e2)" |
  "FV (Zip e1 e2) = FV e1 @ FV e2" |
  "FV (Reduce e1 e2 e3) = (FV e1 @ FV e2 @ FV e3)" |
  "FV (Split e1 e2) = (FV e1 @ FV e2)" |
  "FV (Join e) = FV e" |
  "FV (Iterate e1 e2 e3) = (FV e1 @ FV e2 @ FV e3)"
  
primrec bsubst :: "nat \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp" ("{_\<rightarrow>_}_" [54,54,54] 53) where
  "{j\<rightarrow>e} (Const c) = Const c" |
  "{j\<rightarrow>e} (Prim p e') = Prim p ({j\<rightarrow>e}e')" |
  "{j\<rightarrow>e} (FVar v) = FVar v" |
  "{j\<rightarrow>e} (BVar v) = (if v = j then e else (BVar v))" |
  "{j\<rightarrow>e} (LambdaE e') = LambdaE ({(Suc j)\<rightarrow>e} e')" |
  "{j\<rightarrow>e} (AppE e1 e2) = AppE ({j\<rightarrow>e} e1) ({j\<rightarrow>e} e2)" |
  "{j\<rightarrow>e} (Map e1 e2) = Map ({j\<rightarrow>e} e1) ({j\<rightarrow>e} e2)" |
  "{j\<rightarrow>e} (Zip e1 e2) = Zip ({j\<rightarrow>e} e1) ({j\<rightarrow>e} e2)" |
  "{j\<rightarrow>e} (Reduce e1 e2 e3) = Reduce ({j\<rightarrow>e} e1) ({j\<rightarrow>e} e2) ({j\<rightarrow>e} e3)" |
  "{j\<rightarrow>e} (Split e1 e2) = Split ({j\<rightarrow>e} e1) ({j\<rightarrow>e} e2)" |
  "{j\<rightarrow>e} (Join e') = Join ({j\<rightarrow>e} e')" |
  "{j\<rightarrow>e} (Iterate e1 e2 e3) = Iterate ({j\<rightarrow>e} e1) ({j\<rightarrow>e} e2) ({j\<rightarrow>e} e3)"

primrec subst :: "var \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp" ("[_\<mapsto>_]_" [72,72,72] 71) where
  "[x\<mapsto>v] (Const c) = Const c" |
  "[x\<mapsto>v] (Prim p e) = Prim p ([x\<mapsto>v]e)" |
  "[x\<mapsto>v] (FVar y) = (if y = x then v else (FVar y))" |
  "[x\<mapsto>v] (BVar y) = BVar y" |
  "[x\<mapsto>v] (LambdaE e) = LambdaE ([x\<mapsto>v] e)" |
  "[x\<mapsto>v] (AppE e1 e2) = AppE ([x\<mapsto>v] e1) ([x\<mapsto>v] e2)" |
  "[x\<mapsto>v] (Map e1 e2) = Map ([x\<mapsto>v] e1) ([x\<mapsto>v] e2)" |
  "[x\<mapsto>v] (Zip e1 e2) = Zip ([x\<mapsto>v] e1) ([x\<mapsto>v] e2)" |
  "[x\<mapsto>v] (Reduce e1 e2 e3) = Reduce ([x\<mapsto>v] e1) ([x\<mapsto>v] e2) ([x\<mapsto>v] e3)" |
  "[x\<mapsto>v] (Split e1 e2) = Split ([x\<mapsto>v] e1) ([x\<mapsto>v] e2)" |
  "[x\<mapsto>v] (Join e1) = Join ([x\<mapsto>v] e1)" |
  "[x\<mapsto>v] (Iterate e1 e2 e3) = Iterate ([x\<mapsto>v] e1) ([x\<mapsto>v] e2) ([x\<mapsto>v] e3)"

lemma subst_id: fixes e::exp 
  assumes xfv: "x \<notin> set (FV e)" shows "[x\<mapsto>v]e = e"
  using xfv by (induction e) force+

type_synonym env = "(var \<times> exp) list"

fun msubst :: "env \<Rightarrow> exp \<Rightarrow> exp" ("[_] _" [72,72] 71) where
  "msubst [] e = e" |
  "msubst ((x,v)#\<rho>) e = msubst \<rho> ([x\<mapsto>v]e)"

abbreviation assoc_dom :: "('a \<times> 'b) list \<Rightarrow> 'a set" where
 "assoc_dom \<Gamma> \<equiv> set (map fst \<Gamma>)"

lemma msubst_id: fixes e::exp assumes rfv: "assoc_dom \<rho> \<inter> set (FV e) = {}"
  shows "[\<rho>]e = e"
  using rfv apply (induction \<rho> arbitrary: e) apply simp using subst_id by auto

datatype result = Res exp | Error | TimeOut

fun extract_const :: "result \<Rightarrow> const" where
  "extract_const (Res (Const c)) = c" |
  "extract_const _ = Null"

fun interp :: "exp \<Rightarrow> nat \<Rightarrow> result" where
  "interp (Const c) (Suc n) = Res (Const c)" |
  "interp (Prim p e) (Suc n) = 
     (case interp e n of 
         Res (Const c) \<Rightarrow> (case eval_prim p c of
                            Result c' \<Rightarrow> Res (Const c')
                          | PError \<Rightarrow> Error)
     | Error \<Rightarrow> Error | TimeOut \<Rightarrow> TimeOut)" |
  "interp (FVar x) (Suc n) = Error" |
  "interp (BVar k) (Suc n) = Error" |
  "interp (LambdaE e) (Suc n) = Res (LambdaE e)" |
  "interp (AppE e1 e2) (Suc n) =
      (case (interp e1 n, interp e2 n) of
        (Res (LambdaE e), Res v) \<Rightarrow> interp (bsubst 0 v e) n
      | (TimeOut, _) \<Rightarrow> TimeOut | (_, TimeOut) \<Rightarrow> TimeOut | (_,_) \<Rightarrow> Error)" |
  "interp (Map e1 e2) (Suc n) = 
      (case (interp e1 n, interp e2 n) of 
        (Res (LambdaE e), Res (Const (ArrayC v))) \<Rightarrow> 
          Res (Const (ArrayC (map (\<lambda> i. extract_const (interp (AppE e (Const i)) n)) v)))
      | (TimeOut, _) \<Rightarrow> TimeOut | (_, TimeOut) \<Rightarrow> TimeOut | (_,_) \<Rightarrow> Error)" |
  "interp _ (Suc n) = Error" |
  "interp _ 0 = TimeOut"

