theory Test
imports Main Skel
begin

(* sanity checking the interpreter *)
abbreviation p0 :: exp where "p0 \<equiv> Binary Add (Const (ScalarC (IntC 1))) (Const (ScalarC (IntC 2)))"
abbreviation p1 :: exp where "p1 \<equiv> Unary Inc (Const (ScalarC (IntC 2)))"
abbreviation p2 :: exp where "p2 \<equiv> Array [p0, p1]"
abbreviation p3 :: exp where "p3 \<equiv> Array [(Const (ScalarC (IntC 1))), (Const (ScalarC (IntC 2))),
                                          (Const (ScalarC (IntC 3))), (Const (ScalarC (IntC 4))),
                                          (Const (ScalarC (IntC 5))), (Const (ScalarC (IntC 6)))]"
theorem "eval (Map x (Unary Inc (Var x)) p2) = 
         Res (ArrayC [(ScalarC (IntC 4)), (ScalarC (IntC 4))])"
by fastforce
theorem "eval (Map x (Binary Add (Var x) (Const (ScalarC (IntC 1)))) p2) = 
         Res (ArrayC [(ScalarC (IntC 4)), (ScalarC (IntC 4))])"
by fastforce
theorem "eval (Map x (Binary Mul (Var x) (Var x)) p2) = 
         Res (ArrayC [ScalarC (IntC 9), ScalarC (IntC 9)])"
by fastforce
theorem "eval (Zip p2 p2) = 
         Res (ArrayC [TupleC (ScalarC (IntC 3)) (ScalarC (IntC 3)), 
                      TupleC (ScalarC (IntC 3)) (ScalarC (IntC 3))])"
by fastforce

theorem "array_split 2 [a, b, c, d] = [[a,b],[c,d]]"
by normalization

theorem "eval (Split (Const (ScalarC (IntC 2))) 
              (Array [Const (ScalarC (IntC 1)), Const (ScalarC (IntC 2)), 
                      Const (ScalarC (IntC 3)), Const (ScalarC (IntC 4))])) =
         Res (ArrayC [ArrayC [ScalarC (IntC 1), ScalarC (IntC 2)], ArrayC [ScalarC (IntC 3), ScalarC (IntC 4)]])"
by normalization

value "eval (Split (Const (ScalarC (IntC 2))) p3)"
value "eval (Join (Split (Const (ScalarC (IntC 2))) p3))"
value "eval p3"
theorem "eval p3 = eval (Join (Split (Const (ScalarC (IntC 2))) p3))"
by normalization

value "eval (Split (Const (ScalarC (IntC 1))) p3)"

theorem splitjoin: 
assumes 1: "n > 0"
assumes 2: "e = (Const (ArrayC a))"
assumes 3: "e' = (Join (Split (Const (ScalarC (IntC n))) (Const (ArrayC a))))"
shows "eval e' = eval e"
using 1 2 3
apply auto
sorry

end
