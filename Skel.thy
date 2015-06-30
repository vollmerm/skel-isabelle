theory Skel
imports Main Scalar Exp
begin

datatype result = Res const | Error

type_synonym env = "(var \<times> const) list"

fun res_cons :: "result \<Rightarrow> result \<Rightarrow> result" where
  "res_cons (Res a1) (Res (ArrayC a2)) = Res (ArrayC (a1 # a2))" |
  "res_cons _ _ = Error"

fun apply_map :: "('a \<Rightarrow> result) \<Rightarrow> 'a array \<Rightarrow> result" where
  "apply_map f [] = Res (ArrayC [])" |
  "apply_map f (x # xs) = res_cons (f x) (apply_map f xs)"

fun apply_zip :: "const array \<Rightarrow> const array \<Rightarrow> result" 
and make_tuple :: "(const \<times> const) \<Rightarrow> const" where
  "apply_zip xs ys = Res (ArrayC (map make_tuple (zip xs ys)))" |
  "make_tuple (c1, c2) = TupleC c1 c2"

fun rec_split :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a array \<Rightarrow> ('a array) array" where
  "rec_split tn sp 0 xs = [take tn (rotate sp xs)]" |
  "rec_split tn sp n xs = (take tn (rotate (sp - n) xs)) # (rec_split tn sp (n - 2) xs)"

fun apply_split :: "nat \<Rightarrow> const array \<Rightarrow> result" where
  "apply_split n xs = (let n' = ((length xs)-2) in Res (ArrayC (map ArrayC (rec_split n n' n' xs))))"

fun lookup :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup k [] = None" |
  "lookup k ((k',v)#ls) = (if k = k' then Some v else lookup k ls)"

fun interp :: "exp \<Rightarrow> env \<Rightarrow> result" where
  "interp (Const c) \<rho> = Res c" |
  "interp (Unary p e) \<rho> = (case interp e \<rho> of 
                            Res (ScalarC c) \<Rightarrow> Res (ScalarC (eval_scalar_unary p c))
                          | Error \<Rightarrow> Error)" |
  "interp (Binary p e1 e2) \<rho> = (case (interp e1 \<rho>, interp e2 \<rho>) of
                                 (Res (ScalarC c1), Res (ScalarC c2)) \<Rightarrow> 
                                    Res (ScalarC (eval_scalar_binary p c1 c2))
                               | (Error,_) \<Rightarrow> Error | (_,Error) \<Rightarrow> Error)" |
  "interp (Var x) \<rho> = (case (lookup x \<rho>) of 
                        Some e \<Rightarrow> Res e
                      | None \<Rightarrow> Error)" |
  "interp (Array []) _ = Res (ArrayC [])" |
  "interp (Array (x # xs)) \<rho> = res_cons (interp x \<rho>) (interp (Array xs) \<rho>)" |
  "interp (Map v le ve) \<rho> = 
    (case (interp ve \<rho>) of 
      Res (ArrayC a) \<Rightarrow> apply_map (\<lambda>i. interp le ((v,i)#\<rho>)) a
    | Error \<Rightarrow> Error)" |
  "interp (Zip e1 e2) \<rho> =
    (case (interp e1 \<rho>, interp e2 \<rho>) of 
      (Res (ArrayC a1), Res (ArrayC a2)) \<Rightarrow> apply_zip a1 a2
    | (Error,_) \<Rightarrow> Error | (_,Error) \<Rightarrow> Error)" |
  "interp (Split e1 e2) \<rho> = 
    (case (interp e1 \<rho>, interp e2 \<rho>) of
      (Res (ScalarC (IntC n)), Res (ArrayC a)) \<Rightarrow> apply_split (nat n) a
    | (Error,_) \<Rightarrow> Error | (_,Error) \<Rightarrow> Error)" |
  "interp _ \<rho> = Error"

definition eval :: "exp \<Rightarrow> result" where "eval e = interp e []"
declare eval_def[simp]

end