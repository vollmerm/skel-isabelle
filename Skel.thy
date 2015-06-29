theory Skel
imports Main
begin

type_synonym 'a array = "'a list"

datatype scalar_unary = Inc | Dec

datatype scalar_binary = Add | Mul | Sub

datatype scalar_const = IntC int | NullC

fun eval_scalar_unary :: "scalar_unary \<Rightarrow> scalar_const \<Rightarrow> scalar_const" where
  "eval_scalar_unary Inc (IntC n) = IntC (n + 1)" |
  "eval_scalar_unary Dec (IntC n) = IntC (n - 1)" |
  "eval_scalar_unary _ NullC = NullC"

fun eval_scalar_binary :: "scalar_binary \<Rightarrow> scalar_const \<Rightarrow> scalar_const \<Rightarrow> scalar_const" where
  "eval_scalar_binary Add (IntC i) (IntC j) = IntC (i + j)" |
  "eval_scalar_binary Mul (IntC i) (IntC j) = IntC (i * j)" |
  "eval_scalar_binary Sub (IntC i) (IntC j) = IntC (i - j)" |
  "eval_scalar_binary _ NullC _ = NullC" |
  "eval_scalar_binary _ _ NullC = NullC"

type_synonym var = nat

datatype exp = Const scalar_const
  | Unary scalar_unary exp
  | Binary scalar_binary exp exp
  | FVar var 
  | BVar var
  | Array "exp array"
  | LambdaE exp 
  | AppE exp exp
  | Map exp exp 
  | Zip exp exp 
  | Reduce exp exp exp
  | Split exp exp 
  | Join exp
  | Iterate exp exp exp

abbreviation list_max :: "nat list \<Rightarrow> nat" where
  "list_max ls \<equiv> foldr max ls (0::nat)"
  
lemma list_max_fresh: fixes n::nat assumes g: "list_max ls < n" shows "n \<notin> set ls"
using g by (induction ls arbitrary: n) auto

abbreviation mklet :: "exp \<Rightarrow> exp \<Rightarrow> exp" where
  "mklet e1 e2 \<equiv> AppE (LambdaE e2) e1"

primrec FV :: "exp \<Rightarrow> var list" where
  "FV (Const c) = []" |
  "FV (Unary c e) = FV e" |
  "FV (Binary c e1 e2) = FV e1 @ FV e2" |
  "FV (FVar v) = [v]" |
  "FV (BVar v) = []" |
  "FV (Array le) = concat (map (\<lambda> e. FV e) le)" |
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
  "{j\<rightarrow>e} (Unary c e') = Unary c ({j\<rightarrow>e}e')" |
  "{j\<rightarrow>e} (Binary c e1 e2) = Binary c ({j\<rightarrow>e}e1) ({j\<rightarrow>e}e2)" |
  "{j\<rightarrow>e} (FVar v) = FVar v" |
  "{j\<rightarrow>e} (BVar v) = (if v = j then e else (BVar v))" |
  "{j\<rightarrow>e} (Array le) = Array (map (\<lambda> e'. {j\<rightarrow>e}e') le)" |
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
  "[x\<mapsto>v] (Unary c e) = Unary c ([x\<mapsto>v]e)" |
  "[x\<mapsto>v] (Binary c e1 e2) = Binary c ([x\<mapsto>v]e1) ([x\<mapsto>v]e2)" |
  "[x\<mapsto>v] (FVar y) = (if y = x then v else (FVar y))" |
  "[x\<mapsto>v] (BVar y) = BVar y" |
  "[x\<mapsto>v] (Array le) = Array (map (\<lambda> e. [x\<mapsto>v]e) le)" |
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
  using xfv
  by (induct e, auto, simp add: map_idI)

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


(* Ideally we'd have the whole interpreter return an error if there's an error
   inside an array computation, so we need custom implementations of the primitives
   like map. *)
fun array_map :: "(exp \<Rightarrow> result) \<Rightarrow> exp array \<Rightarrow> (exp array) option" where
  "array_map f [] = Some []" |
  "array_map f (x # xs) = (case (f x) of
                              Res x' \<Rightarrow> (case (array_map f xs) of 
                                            Some xs' \<Rightarrow> Some (x' # xs')
                                          | None \<Rightarrow> None)
                            | _ \<Rightarrow> None)" 

fun error_to_null :: "result \<Rightarrow> exp" where
  "error_to_null (Res e) = e" |
  "error_to_null _ = Const NullC" 

(* Interpreter with a count down that might time out. *)
fun interp_limit :: "exp \<Rightarrow> nat \<Rightarrow> result" where
  "interp_limit (Const c) (Suc n) = Res (Const c)" |
  "interp_limit (Unary p e) (Suc n) = 
     (case interp_limit e n of 
       Res (Const c) \<Rightarrow> Res (Const (eval_scalar_unary p c))
     | Error \<Rightarrow> Error | TimeOut \<Rightarrow> TimeOut)" |
   "interp_limit (Binary p e1 e2) (Suc n) = 
     (case (interp_limit e1 n, interp_limit e2 n) of 
       (Res (Const c1), Res (Const c2)) \<Rightarrow> Res (Const (eval_scalar_binary p c1 c2))
     | (Error,_) \<Rightarrow> Error | (_,Error) \<Rightarrow> Error 
     | (TimeOut,_) \<Rightarrow> TimeOut | (_,TimeOut) \<Rightarrow> TimeOut)" |
  "interp_limit (FVar x) (Suc n) = Error" |
  "interp_limit (BVar k) (Suc n) = Error" |
  "interp_limit (LambdaE e) (Suc n) = Res (LambdaE e)" |
  "interp_limit (Array le) (Suc n) = 
    (case (array_map (\<lambda> i. interp_limit i n) le) of
      Some v' \<Rightarrow> Res (Array v')
    | None \<Rightarrow> Error)" |
  "interp_limit (AppE e1 e2) (Suc n) =
      (case (interp_limit e1 n, interp_limit e2 n) of
        (Res (LambdaE e), Res v) \<Rightarrow> interp_limit (bsubst 0 v e) n
      | (TimeOut, _) \<Rightarrow> TimeOut | (_, TimeOut) \<Rightarrow> TimeOut | (_,_) \<Rightarrow> Error)" |
   "interp_limit (Map e1 e2) (Suc n) = 
      (case (interp_limit e1 n, interp_limit e2 n) of 
        (Res (LambdaE e), Res (Array v)) \<Rightarrow> 
          Res (Array (map (\<lambda> i. error_to_null (interp_limit (bsubst 0 i e) n)) v))
      | (TimeOut, _) \<Rightarrow> TimeOut | (_, TimeOut) \<Rightarrow> TimeOut | (_,_) \<Rightarrow> Error)" |
  "interp_limit _ (Suc n) = Error" |
  "interp_limit _ 0 = TimeOut"

abbreviation p0 :: exp where "p0 \<equiv> Binary Add (Const (IntC 1)) (Const (IntC 2))"
abbreviation p1 :: exp where "p1 \<equiv> Unary Inc (Const (IntC 2))"
abbreviation p2 :: exp where "p2 \<equiv> Array [p0, p1]"
abbreviation p3 :: exp where "p3 \<equiv> Map (LambdaE (Const (IntC 1))) (Array [p0, p1])"
abbreviation p4 :: exp where "p4 \<equiv> Map (LambdaE (Unary Inc (BVar 0))) (Array [p0, p1])"
value "interp_limit p0 2"
value "interp_limit p1 2"
value "interp_limit p2 10"
value "interp_limit p3 10"
value "interp_limit p4 10"
theorem t0: assumes a1: "e = p0" and a2: "v = Const (IntC 3)"
  shows "interp_limit e (Suc 1) = Res v" using a1 a2
  apply (induct e arbitrary: v, auto)
done
theorem t0': assumes a1: "e = p0" and a2: "v = Const (IntC 3)"
  shows "\<exists>n. interp_limit e (Suc n) = Res v" using a1 a2
  apply (induct e arbitrary: v) apply auto
  (* sledgehammer! *)
  apply (smt add.commute eval_scalar_binary.simps(1) exp.simps(197) interp_limit.simps(1) 
             numeral_Bit0 numeral_Bit1 result.simps(8))
done