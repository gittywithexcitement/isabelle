theory 11
  imports Main "~~/src/HOL/Library/Code_Target_Nat" 
begin
  
  (* section 2.5 *)
  
  (* exercise 2.11 *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp
  
fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var v = v" |
  "eval (Const i) _ = i" |
  "eval (Add el er) v = (eval el v) + (eval er v)"|
  "eval (Mult el er) v = (eval el v) * (eval er v)"
  
value "eval (Mult (Const 3) Var) 2"
  
  (* Returns expression for x^p where x is Var*)
fun xToPow :: "nat \<Rightarrow> exp" where
  "xToPow 0 = Const 1"|
  "xToPow (Suc 0) = Var"|
  "xToPow (Suc p) = Mult Var (xToPow p)"
  
value "xToPow 0"
value "xToPow 1"
value "xToPow 2"
  
  (* Create an expression from polynomial coefficients. The nat is the power of x to be multiplied
against the head of the list. If list is empty, returns 0. *)
fun createPolyExpression :: "int list \<Rightarrow> nat \<Rightarrow> exp" where
  "createPolyExpression [] _ = Const 0"|
  "createPolyExpression [coeff] pow = Mult (Const coeff) (xToPow pow)"|
  "createPolyExpression (coeff # coeffs) 0 = Add (Const coeff) (createPolyExpression coeffs (Suc 0))"|
  "createPolyExpression (coeff # coeffs) pow = Add (Mult (Const coeff) (xToPow pow)) (createPolyExpression coeffs (Suc pow))"
  
value "createPolyExpression [4,2,-1] 0"
  
  (* Define a function evalPoly that evaluates a polynomial at the given value. *)
  (* Evaluate a polynomial, given its coefficients and x. The coefficients are assumed to start at
  x^0, be in order, and contiguous *)
fun evalPoly :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalPoly [] _ = 0"|
  "evalPoly (c#coeffs) v = c + v * (evalPoly coeffs v)"
  
value "evalPoly [4,2,-1,3] 1"  
value "evalPoly [4,2,-1,3] 3" 
  
  (* Takes the reversed coefficient list. I.e. [-1, 2, 4] represents 4+2x-x^2   *)
fun hornerHelper :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "hornerHelper [] _ = 0"|
  "hornerHelper (rc # rcs) v = rc * v^(length rcs) + (hornerHelper rcs v)"
  
  (* Evaluate a polynomial (using Horner's method) *)
fun evalPolyHorner :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalPolyHorner coeffs v = hornerHelper (rev coeffs) v"
  
value "evalPolyHorner [4,2,-1,3] 3"
  
fun numMults :: "exp \<Rightarrow> nat" where
  "numMults Var = 0"|
  "numMults (Const i) = 0"|
  "numMults (Add l r) = numMults l + numMults r"|
  "numMults (Mult l r) = Suc(numMults l + numMults r)"
  
fun hasMoreMults :: "exp \<Rightarrow> exp \<Rightarrow> bool"  where
  "hasMoreMults l r = (if numMults l > numMults r
                        then True
                        else False)"
  
  (* flatten the top-level adds out into an expression list *)
fun flattenAdds :: "exp \<Rightarrow> exp list" where
  "flattenAdds (Add l r) = flattenAdds l @ flattenAdds r"|
  "flattenAdds e = [e]"  
  
value "flattenAdds (createPolyExpression [4,2,-1] 0)"
  
fun unflattenAdds :: "exp list \<Rightarrow> exp" where
  "unflattenAdds [] = Const 0" | (* don't do this *)
  "unflattenAdds [e] = e" |
  "unflattenAdds (e # es) = Add e (unflattenAdds es)"
  
value "unflattenAdds (flattenAdds (createPolyExpression [4,2,-1] 0))"
  
  (* TODO lemma that eval . unflatten . flatten $ x = eval x.
unflatten . flatten is not identity, because the add-tree shape may change. *)
  
  (* The second list arg should be [] for initial call 
This is insertion sort. Not great; it's n^2 *)
fun sortByHelper :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sortByHelper _ [] sorteds = sorteds"|
  "sortByHelper gt (u # unsorted) [] = sortByHelper gt unsorted [u]" |
  "sortByHelper gt (u # unsorted) (s # sorteds) =
    (if (gt u s) 
      then sortByHelper gt unsorted (s # (sortByHelper gt [u] sorteds))
      else sortByHelper gt unsorted (u # (s # sorteds)))"
  
  (* This is insertion sort. Not great; it's n^2 *)
fun sortBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sortBy gt unsorted = sortByHelper gt unsorted []"
  
  (* I'm not sure if gt should be arbitrary, below *)
  (* I'm not sure if v should be arbitrary, below *)
  
  
  (* lemma sortByHelper_length_01: "length (sortByHelper gt xs ys) = length (xs @ ys)"
  (* apply(induction xs arbitrary: ys v rule: sortByHelper.induct) *)
  apply(induction xs arbitrary: ys)
   apply(auto)
  (* apply(simp_all add: algebra_simps) *)
  (* apply(simp add: sortByHelper.simps)  *)
  done *)
  
  (* lemma sortByHelper_count_01: "count v (sortByHelper gt xs ys) = count v (xs @ ys)"
  (* apply(induction xs arbitrary: ys v rule: sortByHelper.induct) *)
  apply(induction xs arbitrary: ys v) 
   apply(auto)
  (* apply(simp add: sortByHelper.simps)  *)
  done *)
  
  (* theorem sortBy_element_count_unchanged: "count v (sortBy gt xs) = count v xs"
  apply(induction xs arbitrary: v rule: sortByHelper.induct)
  (* apply(induction xs arbitrary: gt v) *)
   apply(auto)
  (* apply(simp add: sortByHelper.simps)    *)
  done  *)
  
  (* lemma sortBy_twice[simp]: "sortBy gt (sortBy gt xs) = sortBy gt xs" *)
  
value "flattenAdds (Add (Add (Mult (Const 2) Var) (Mult (Const (- 1)) (Mult Var Var))) (Const 4))"  
value "sortBy hasMoreMults (flattenAdds (Add (Add (Mult (Const 2) Var) (Mult (Const (- 1)) (Mult Var Var))) (Const 4)))"   
value "unflattenAdds (sortBy hasMoreMults (flattenAdds (Add (Add (Mult (Const 2) Var) (Mult (Const (- 1)) (Mult Var Var))) (Const 4))))"   
  
  (* A helper for simplify. Collapses (const + const) and (const * const). Returns other expressions
  unchanged *)
fun simplifyNonrecursive :: "exp \<Rightarrow> exp" where
  "simplifyNonrecursive (Add (Const l) (Const r)) = Const (l + r)"|
  "simplifyNonrecursive (Mult (Const l) (Const r)) = Const (l * r)"|  
  "simplifyNonrecursive x = x"
  
  
  (* declare [[ smt_timeout = 30 ]] *)
  
lemma simplifyNonrecursive_preserves_eval[simp]: "eval (simplifyNonrecursive expr) x = eval expr x"
  apply(induction expr rule: simplifyNonrecursive.induct) apply(auto)
  done 
    
    (* Perform algebraic simplification of constants. AKA do constant folding   *)
fun simplify :: "exp \<Rightarrow> exp" where
  "simplify Var = Var"|
  "simplify (Const i) = Const i"|
  "simplify (Add (Const l) (Const r)) = Const (l + r)"|
  "simplify (Mult (Const l) (Const r)) = Const (l * r)"|
  "simplify (Add l r) = 
    (let simpleL = simplify l;
         simpleR = simplify r
     in  simplifyNonrecursive (Add simpleL simpleR))" |
  "simplify (Mult l r) = 
    (let simpleL = simplify l;
         simpleR = simplify r
     in  simplifyNonrecursive (Mult simpleL simpleR))"
  
value "simplify (Add (Mult (Const 4) (Const 1)) (Add (Mult (Add (Const 0) (Const 2)) Var) (Mult (Const (- 1)) (Mult Var Var))))"
  
  (*       apply(induction n arbitrary: t)
   apply(simp_all add: algebra_simps) *)  
  
lemma simplify_preserves: "eval (simplify expr) x = eval expr x"
  apply(induction expr rule: simplify.induct) apply(auto) 
  done    
    
    (* Define a function coeffs that transforms an expression into a polynomial. I'm going to limit my
function to handling canonical expressions only. I assume 0 coefficients are included, 
e.g. (Mult (Const 0) Var) *)
    (* TODO/done sort the adds by number of nested multiplies *)
    (* TODO/done I think coeffs needs to do algebraic simplification of constants *)
    (* TODO insert 0 coefficients (probably best done while in exp list form, after sorting.) *)
fun coeffsOld :: "exp \<Rightarrow> int list" where
  "coeffsOld (Const i) = [i]"|
  "coeffsOld (Add l r) = coeffsOld l @ coeffsOld r"|
  "coeffsOld (Mult l r) = coeffsOld l @ coeffsOld r"|
  "coeffsOld Var = []"
  
value "coeffsOld (createPolyExpression [4,2,-1] 0)"
value "coeffsOld (createPolyExpression [4,2,-1,3] 0)"
  
fun addCoeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "addCoeffs [] r = r" |
  "addCoeffs l [] = l" |
  "addCoeffs (l#ls) (r#rs) = (l+r) # addCoeffs ls rs"
  
lemma 
  "evalPolyHorner(coeffs expr) x = eval expr x"
         hornerHelper (rev (addCoeffs (coeffs expr1) (coeffs expr2))) x = eval expr1 x + eval expr2 x

  
  (* left, right, prefix (a list of some 0s)   *)
fun multCoeffsHelper :: "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list" where
  "multCoeffsHelper [] _  _ = []" |
  "multCoeffsHelper _  [] _ = []" |
  "multCoeffsHelper (l#ls) rs prefix = 
    (let this = prefix @ (map (\<lambda>ri. l*ri) rs);
          next = multCoeffsHelper ls rs (0 # prefix)
      in addCoeffs this next)"
  
fun multCoeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where  
  "multCoeffs l r = multCoeffsHelper l r []"
  
fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]"  |
  "coeffs (Const i) = [i]"|
  "coeffs (Add l r) = addCoeffs (coeffs l) (coeffs r)" |
  "coeffs (Mult l r) = multCoeffs (coeffs l) (coeffs r)"
  
value "coeffs (createPolyExpression [4,2,-1] 0)"
value "coeffs (Mult (createPolyExpression [1,2,3] 0) (createPolyExpression [4,5] 0))"
  
theorem ceoffs_preserves_eval[simp]: "evalPoly(coeffs expr) x = eval expr x"
  apply(induction expr)
     apply(auto)
  done
  
  (* 
I have not been able to complete the proof portion of exercise 2.11.
Since I can't prove my sort is well-behaved, I think I would not be able to prove that
\<forall> expr x. evalPoly (coeffs expr) x = eval expr x

Instead I will do my own modified proof:
eval (createPolyExpression coeffs headPower) x = evalPoly coeffs x
 *)
  
  
end