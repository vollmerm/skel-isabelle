theory Scalar
imports Main
begin

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

end