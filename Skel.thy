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

fun array_split :: "nat \<Rightarrow> 'a array \<Rightarrow> ('a array) array" where
  "array_split _ [] = []" |  
  "array_split 0 a = []" |
  "array_split n a = 
    (if n \<ge> (length a)
    then [a]
    else (take n a) # (array_split n (drop n a)))"

lemma array_split_empty [simp]: "\<forall>n. array_split n [] = []"
by simp

fun apply_split :: "nat \<Rightarrow> const array \<Rightarrow> result" where
  "apply_split n a = Res (ArrayC (map ArrayC (array_split n a)))"

lemma apply_split_empty [simp]: "\<forall>n. apply_split n [] = Res (ArrayC [])"
by simp

fun array_join :: "const array \<Rightarrow> (const array) option" where
  "array_join [] = Some []" |
  "array_join ((ArrayC a) # xs) = 
    (case (array_join xs) of 
      Some as \<Rightarrow> Some (a @ as)
    | None \<Rightarrow> None)" |
  "array_join _ = None"

fun apply_join :: "const array \<Rightarrow> result" where
  "apply_join a = 
    (case (array_join a) of 
      Some a' \<Rightarrow> Res (ArrayC a')
    | None \<Rightarrow> Error)"

lemma apply_join_empty [simp]: "apply_join [] = Res (ArrayC [])"
by force

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
  "interp (Join e) \<rho> = 
    (case (interp e \<rho>) of 
      Res (ArrayC a) \<Rightarrow> apply_join a
    | Error \<Rightarrow> Error)" |
  "interp _ \<rho> = Error"

definition eval :: "exp \<Rightarrow> result" where "eval e = interp e []"
declare eval_def[simp]

lemma eval_join_empty [simp]: "eval (Join (Const (ArrayC []))) = Res (ArrayC [])"
by simp

lemma eval_array_empty [simp]: "eval (Array []) = Res (ArrayC [])"
by simp

end