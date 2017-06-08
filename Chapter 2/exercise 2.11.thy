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
  
fun evalPoly' :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "evalPoly' [] _ _ = 0"|
  "evalPoly' (c#coeffs) v pow = (c*v^pow) + (evalPoly' coeffs v (Suc pow))"  
  
  (* Define a function evalPoly that evaluates a polynomial at the given value. *)
  (* Evaluate a polynomial, given its coefficients and x. The coefficients are assumed to start at
  x^0, be in order, and contiguous *)
fun evalPoly :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalPoly coeffs v = evalPoly' coeffs v 0"
  
value "evalPoly [1,2,3] 1"  
value "evalPoly [1,2,3] 3" 
  
  (* Takes the reversed coefficient list. I.e. [-1, 2, 4] represents 4+2x-x^2   *)
fun hornerHelper :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "hornerHelper [] _ = 0"|
  "hornerHelper (rc # rcs) v = rc * v^(length rcs) + (hornerHelper rcs v)"
  
  (* Evaluate a polynomial (using Horner's method) *)
fun evalPolyHorner :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalPolyHorner coeffs v = hornerHelper (rev coeffs) v"
  
value "evalPolyHorner [4,2,-1,3] 3"
  
  (* A helper for simplify. Collapses (const + const) and (const * const). Returns other expressions
  unchanged *)
fun simplifyNonrecursive :: "exp \<Rightarrow> exp" where
  "simplifyNonrecursive (Add (Const l) (Const r)) = Const (l + r)"|
  "simplifyNonrecursive (Mult (Const l) (Const r)) = Const (l * r)"|  
  "simplifyNonrecursive x = x"
  
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
  
lemma simplify_preserves[simp]: "eval (simplify expr) x = eval expr x"
  apply(induction expr rule: simplify.induct) apply(auto) 
  done    
    
    (* Define a function coeffs that transforms an expression into a polynomial. I'm going to limit my
function to handling canonical expressions only. I assume 0 coefficients are included, 
e.g. (Mult (Const 0) Var) *)
    (* TODO/done sort the adds by number of nested multiplies *)
    (* TODO/done I think coeffs needs to do algebraic simplification of constants *)
    (* TODO insert 0 coefficients (probably best done while in exp list form, after sorting.) *)
(* fun coeffsOld :: "exp \<Rightarrow> int list" where
  "coeffsOld (Const i) = [i]"|
  "coeffsOld (Add l r) = coeffsOld l @ coeffsOld r"|
  "coeffsOld (Mult l r) = coeffsOld l @ coeffsOld r"|
  "coeffsOld Var = []" 
  
value "coeffsOld (createPolyExpression [4,2,-1] 0)"
value "coeffsOld (createPolyExpression [4,2,-1,3] 0)" *)
  
  (* TODO implement using zip and map   *)
fun addCoeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "addCoeffs [] r = r" |
  "addCoeffs l [] = l" |
  "addCoeffs (l#ls) (r#rs) = (l+r) # addCoeffs ls rs"
    
lemma addCoeffs_eval_01[simp]:
  "evalPoly' (addCoeffs r []) x p = evalPoly' r x p"
  apply(induction r)
   apply(auto)
  done
    
lemma addCoeffs_eval[simp]:
  "evalPoly'(addCoeffs a b) x p = evalPoly' a x p + evalPoly' b x p"
  apply(induction a arbitrary: p rule:addCoeffs.induct)
    apply(auto simp add: algebra_simps)
  done
    
lemma addCoeffs_zeros[simp]:
  shows "addCoeffs (replicate (length cs - 1) 0) cs = cs"
proof(induction cs)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  have "addCoeffs (replicate (length (c # cs) - 1) 0) (c # cs) 
      = addCoeffs (replicate (length cs) 0) (c # cs)" 
    by simp
  also have "... = addCoeffs (0 # replicate (length cs - 1) 0) (c # cs)"
  proof(induction cs)
    case Nil
    then show ?case by simp
  next
    case (Cons a cs)
    then show ?case by simp
  qed
  also have "... = c # addCoeffs (replicate (length cs - 1) 0) cs" by simp
  also have "... = c # cs"
    using Cons.IH by auto
  finally show ?case by simp
qed
  
lemma length_addCoeffs:
  shows "length(addCoeffs xs ys) = max (length xs) (length ys)"
proof(induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case 
  proof -
    have "\<forall>is. is = [] \<or> (\<exists>i isa. is = (i::int) # isa)"
      by (meson list.exhaust)
    then obtain ii :: "int list \<Rightarrow> int" and iis :: "int list \<Rightarrow> int list" where
      f1: "\<forall>is. is = [] \<or> is = ii is # iis is"
      by (metis (no_types))
    have f2: "\<forall>i is ia isa. addCoeffs (i # is) (ia # isa) = (ia + i) # addCoeffs is isa"
      by force
    have f3: "ii ys + x = x + ii ys"
      by linarith
    then have f4: "addCoeffs [x] (ii ys # iis ys) = (x + ii ys) # addCoeffs [] (iis ys)"
      using f2 by presburger
    have f5: "\<forall>is. length (addCoeffs xs is) = max (length xs) (length is)"
      using local.Cons by blast
    have f6: "length ([]::int list) + Suc 0 = Suc 0"
      by auto
    have "\<forall>n na nb. max (n::nat) na + nb = max (n + nb) (na + nb)"
      by (metis nat_add_max_left)
    then have f7: "ys = ii ys # iis ys \<and> xs = ii xs # iis xs \<and> addCoeffs (x # xs) ys = ii (addCoeffs (x # xs) ys) # iis (addCoeffs (x # xs) ys) \<longrightarrow> length (addCoeffs (x # xs) ys) = max (length (x # xs)) (length ys)"
      using f5 f3 f2 by (metis (no_types) list.size(4))
    have f8: "ys = [] \<or> ys = ii ys # iis ys"
      using f1 by metis
    have f9: "addCoeffs (x # xs) (ii ys # iis ys) = (x + ii ys) # addCoeffs xs (iis ys)"
      using f3 f2 by presburger
    { assume "length (addCoeffs (x # xs) ys) \<noteq> max (length (x # xs)) (length ys)"
      { assume "addCoeffs (x # xs) ys \<noteq> []"
        moreover
        { assume "addCoeffs (x # xs) ys = ii (addCoeffs (x # xs) ys) # iis (addCoeffs (x # xs) ys) \<and> length (addCoeffs (x # xs) ys) \<noteq> max (length (x # xs)) (length ys)"
          moreover
          { assume "addCoeffs (x # xs) ys = ii (addCoeffs (x # xs) ys) # iis (addCoeffs (x # xs) ys) \<and> length (addCoeffs (x # xs) ys) \<noteq> max (0 + (length ([]::int list) + Suc 0)) (length (iis ys) + (length ([]::int list) + Suc 0))"
            moreover
            { assume "addCoeffs (x # xs) ys = ii (addCoeffs (x # xs) ys) # iis (addCoeffs (x # xs) ys) \<and> max 0 (length (iis ys)) + (length ([]::int list) + Suc 0) \<noteq> length (addCoeffs [] (iis ys)) + Suc 0"
              moreover
              { assume "addCoeffs (x # xs) ys = ii (addCoeffs (x # xs) ys) # iis (addCoeffs (x # xs) ys) \<and> max 0 (length (iis ys)) \<noteq> length (addCoeffs xs (iis ys))"
                then have "addCoeffs (x # xs) ys = ii (addCoeffs (x # xs) ys) # iis (addCoeffs (x # xs) ys) \<and> xs \<noteq> []"
                  by fastforce }
              ultimately have "addCoeffs (x # xs) ys = ii (addCoeffs (x # xs) ys) # iis (addCoeffs (x # xs) ys) \<and> xs \<noteq> []"
                by simp }
            ultimately have "addCoeffs (x # xs) ys = ii (addCoeffs (x # xs) ys) # iis (addCoeffs (x # xs) ys) \<and> xs \<noteq> [] \<or> addCoeffs (x # xs) ys = ii (addCoeffs (x # xs) ys) # iis (addCoeffs (x # xs) ys) \<and> ys \<noteq> ii ys # iis ys"
              using f4 by fastforce }
          ultimately have ?thesis
            using f7 f6 f1 by (metis (full_types) addCoeffs.simps(2) list.size(3) list.size(4) max_0R) }
        ultimately have ?thesis
          using f1 by blast }
      then have ?thesis
        using f9 f8 by fastforce }
    then show ?thesis
      by metis
  qed
qed
  
lemma addCoeffs_commutative[simp]:
  shows "addCoeffs xs ys = addCoeffs ys xs"
proof(induction xs arbitrary: ys)
  case Nil
  then show ?case by (metis addCoeffs.simps(1) addCoeffs.simps(2) list.exhaust)
next
  case (Cons x xs)
  show ?case      
  proof(cases ys)
    case Nil
    then show ?thesis by simp
  next
    case (Cons yh yts)
    then show ?thesis by (simp add: Cons.IH)
  qed
qed
  
  (* left, right, prefix (a list of some 0s)   *)
fun multCoeffsHelper :: "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list" where
  "multCoeffsHelper [] _  _ = []" |
  "multCoeffsHelper _  [] _ = []" |
  "multCoeffsHelper (l#ls) rs prefix = 
    (let this = prefix @ (map (\<lambda>ri. l*ri) rs);
          next = multCoeffsHelper ls rs (0 # prefix)
      in addCoeffs this next)"
  
lemma multCoeffsHelper_01:
  "evalPoly (multCoeffsHelper [] coeffs2 []) = evalPoly (multCoeffsHelper coeffs2 [] [])"
  apply(induction coeffs2) by auto
 
fun multCoeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where  
  "multCoeffs l r = multCoeffsHelper l r []"
 
fun multCoeffs_v2 :: "int list \<Rightarrow> int list \<Rightarrow> int list" where  
  "multCoeffs_v2 [] _  = []" |
  "multCoeffs_v2 _  [] = []" |  
  "multCoeffs_v2 [l] rs = map (\<lambda>x. l*x) rs"| (* TODO remove? helper for proofs. Not sure if it's useful *)
  "multCoeffs_v2 (l#ls) (r#rs) = 
    (let l_times_rs = (map (op * l) rs);
         ls_times_rrs = multCoeffs_v2 ls (r#rs)
      in (l*r) # addCoeffs l_times_rs ls_times_rrs)"
  
lemma multCoeffs_v2_emptylist_commutative[simp]:
  "evalPoly (multCoeffs_v2 [] coeffs2) = evalPoly (multCoeffs_v2 coeffs2 [])"  
  apply(induction coeffs2) by auto
     
  (* 3rd arg is (power + 1) *)
(* fun multCoeffs_v3_helper :: "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list" where
  "multCoeffs_v3_helper [] _  _ = []" |
  "multCoeffs_v3_helper _  [] _ = []" | 
  "multCoeffs_v3_helper xs ys _ = []"
  
fun multCoeffs_v3 :: "int list \<Rightarrow> int list \<Rightarrow> int list" where  
  "multCoeffs_v3 xs ys = multCoeffs_v3_helper xs ys 1" *)
    
(* Multiply each value in coefficient list by s
equivalent to map (op * s), but supposedly easier to prove things. *)    
fun multCoeffs_by_scalar :: "int \<Rightarrow> int list \<Rightarrow> int list" where  
  "multCoeffs_by_scalar _ [] = []" |
  "multCoeffs_by_scalar s (x#xs) = x*s # multCoeffs_by_scalar s xs"
  
lemma multCoeffs_by_scalar_0[simp]: 
  shows "multCoeffs_by_scalar 0 cs = replicate (length cs) 0"
proof(induction cs)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  then show ?case by simp
qed
  
lemma multCoeffs_by_scalar_1[simp]:
  shows "multCoeffs_by_scalar 1 cs = cs"
proof(induction cs)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  then show ?case by simp
qed
  
fun multCoeffs_v4 :: "int list \<Rightarrow> int list \<Rightarrow> int list" where  
  "multCoeffs_v4 [] _  = []" |
  "multCoeffs_v4 (l#ls) rs = 
    (let mult_l = multCoeffs_by_scalar l rs;
         rest = multCoeffs_v4 ls (0 # rs)
      in addCoeffs mult_l rest)"    

lemma multCoeffs_v4_by_list0[simp]:
  shows"multCoeffs_v4 [0] cr = replicate (length cr) 0"
proof(induction cr)
  case Nil
  then show ?case by simp
next
  case (Cons c cr)
  then show ?case by simp
qed

lemma multCoeffs_v4_by_list1[simp]:
  shows"multCoeffs_v4 [1] cr = cr"
proof(induction cr)
  case Nil
  then show ?case by simp
next
  case (Cons c cr)
  then show ?case by simp
qed
  
lemma multCoeffs_by_scalar_distributes[simp]: "evalPoly' (multCoeffs_by_scalar a xs) x d = a * (evalPoly' xs x d)"
  apply(induction xs arbitrary: d)
   apply simp
  apply auto
  apply(auto simp add: algebra_simps)
  done
    
lemma multiplying_by_x_extends_coeff_list: "x * evalPoly' a x d = evalPoly' (0 # a) x d"
  apply(induction a arbitrary: d)
   apply(auto simp add: algebra_simps)
  done
    
lemma succ_of_exponent_is_times_x: "evalPoly' a x (Suc d) = x * evalPoly' a x d"
  apply(induction d)
   apply (simp add: multiplying_by_x_extends_coeff_list)
  by (simp add: multiplying_by_x_extends_coeff_list)
    
lemma evalp_mult_can_swap: "evalPoly' a x 0 * evalPoly' b x n = evalPoly' b x 0 * evalPoly' a x n"
  apply(induction n)
   apply auto
  by (simp add: succ_of_exponent_is_times_x)
    
lemma mult_is_star: "evalPoly' (multCoeffs_v4 a b) x 0 = (evalPoly' a x 0) * (evalPoly' b x 0)"
  apply(induction a arbitrary: b)
   apply simp
  apply auto
  apply(simp add: algebra_simps evalp_mult_can_swap)
  done
    
value "multCoeffs_v4 [1,2] [3,4]"
  
fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]"  |
  "coeffs (Const i) = [i]"|
  "coeffs (Add l r) = addCoeffs (coeffs l) (coeffs r)" |
  "coeffs (Mult l r) = multCoeffs_v4 (coeffs l) (coeffs r)"
  
value "coeffs (createPolyExpression [4,2,-1] 0)"
value "coeffs (Mult (createPolyExpression [1,2,3] 0) (createPolyExpression [4,5] 0))"
  
theorem ceoffs_preserves_eval[simp]: "evalPoly(coeffs expr) x = eval expr x"
  apply(induction expr)
     apply(auto)
  by (simp add: mult_is_star)
    
end
