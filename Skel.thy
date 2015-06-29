theory Skel
imports Main
begin

type_synonym 'a array = "'a list"

datatype scalar_unary = Inc | Dec

datatype scalar_binary = Add | Mul | Sub

datatype scalar_const = IntC int

fun eval_scalar_unary :: "scalar_unary \<Rightarrow> scalar_const \<Rightarrow> scalar_const" where
  "eval_scalar_unary Inc (IntC n) = IntC (n + 1)" |
  "eval_scalar_unary Dec (IntC n) = IntC (n - 1)"

fun eval_scalar_binary :: "scalar_binary \<Rightarrow> scalar_const \<Rightarrow> scalar_const \<Rightarrow> scalar_const" where
  "eval_scalar_binary Add (IntC i) (IntC j) = IntC (i + j)" |
  "eval_scalar_binary Mul (IntC i) (IntC j) = IntC (i * j)" |
  "eval_scalar_binary Sub (IntC i) (IntC j) = IntC (i - j)"

type_synonym var = string

datatype exp = Const scalar_const
  | Unary scalar_unary exp
  | Binary scalar_binary exp exp
  | Var var
  | Array "exp array"
  | Map var exp exp 
  | Zip exp exp 
  | Reduce var var exp exp exp
  | Split exp exp 
  | Join exp

datatype result = Res exp | Error

type_synonym env = "(var \<times> exp) list"

fun lookup :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup k [] = None" |
  "lookup k ((k',v)#ls) = (if k = k' then Some v else lookup k ls)"

primrec error_to_zero :: "result \<Rightarrow> exp" where
  "error_to_zero (Res e) = e" |
  "error_to_zero Error = Const (IntC 0)"

primrec any_errors :: "result list \<Rightarrow> bool" where
  "any_errors [] = False" |
  "any_errors (x # xs) =
    (case x of 
      Res _ \<Rightarrow> any_errors xs
    | Error \<Rightarrow> True)"

fun interp :: "exp \<Rightarrow> env \<Rightarrow> result" where
  "interp (Const c) \<rho> = Res (Const c)" |
  "interp (Unary p e) \<rho> = (case interp e \<rho> of 
                            Res (Const c) \<Rightarrow> Res (Const (eval_scalar_unary p c))
                          | Error \<Rightarrow> Error)" |
  "interp (Binary p e1 e2) \<rho> = (case (interp e1 \<rho>, interp e2 \<rho>) of
                                 (Res (Const c1), Res (Const c2)) \<Rightarrow> 
                                    Res (Const (eval_scalar_binary p c1 c2))
                               | (Error,_) \<Rightarrow> Error | (_,Error) \<Rightarrow> Error)" |
  "interp (Var x) \<rho> = (case (lookup x \<rho>) of 
                        Some e \<Rightarrow> Res e
                      | None \<Rightarrow> Error)" |
  "interp (Array ve) \<rho> = Res (Array (map (\<lambda>i. error_to_zero (interp i \<rho>)) ve))" |
  "interp (Map v le ve) \<rho> = 
    (case (interp ve \<rho>) of 
      Res (Array a) \<Rightarrow> let a' = (map (\<lambda>i. interp le ((v,i)#\<rho>)) a)
                       in if (any_errors a') 
                          then Error 
                          else Res (Array (map (\<lambda>i. error_to_zero i) a'))
    | Error \<Rightarrow> Error)" |
  "interp _ \<rho> = Error"

definition eval :: "exp \<Rightarrow> result" where "eval e = interp e []"
declare eval_def[simp]

(* sanity checking the interpreter *)

abbreviation p0 :: exp where "p0 \<equiv> Binary Add (Const (IntC 1)) (Const (IntC 2))"
abbreviation p1 :: exp where "p1 \<equiv> Unary Inc (Const (IntC 2))"
abbreviation p2 :: exp where "p2 \<equiv> Array [p0, p1]"
theorem "eval (Map x (Unary Inc (Var x)) p2) = 
         Res (Array [Const (IntC 4), Const (IntC 4)])"
by fastforce
theorem "eval (Map x (Binary Add (Var x) (Const (IntC 1))) p2) = 
         Res (Array [Const (IntC 4), Const (IntC 4)])"
by fastforce
theorem "eval (Map x (Binary Mul (Var x) (Var x)) p2) = 
         Res (Array [Const (IntC 9), Const (IntC 9)])"
by fastforce