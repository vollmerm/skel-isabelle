theory Test
imports Main Skel
begin

(* sanity checking the interpreter *)
abbreviation p0 :: exp where "p0 \<equiv> Binary Add (Const (ScalarC (IntC 1))) (Const (ScalarC (IntC 2)))"
abbreviation p1 :: exp where "p1 \<equiv> Unary Inc (Const (ScalarC (IntC 2)))"
abbreviation p2 :: exp where "p2 \<equiv> Array [p0, p1]"
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
theorem "eval (Split (Const (ScalarC (IntC 2))) 
              (Array [Const (ScalarC (IntC 1)), Const (ScalarC (IntC 2)), 
                      Const (ScalarC (IntC 3)), Const (ScalarC (IntC 4))])) =
         Res (ArrayC [ArrayC [ScalarC (IntC 1), ScalarC (IntC 2)], 
                      ArrayC [ScalarC (IntC 3), ScalarC (IntC 4)]])"
by fastforce
