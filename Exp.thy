theory Exp
imports Main Scalar
begin

type_synonym 'a array = "'a list"

datatype const = ScalarC scalar_const | TupleC const const | ArrayC "const array"

type_synonym var = string

datatype exp = Const const
  | Unary scalar_unary exp
  | Binary scalar_binary exp exp
  | PrjL exp
  | PrjR exp
  | Tuple exp exp
  | Array "exp array"
  | Var var
  | Map var exp exp 
  | Zip exp exp 
  | Reduce var var exp exp exp
  | Split exp exp 
  | Join exp

end