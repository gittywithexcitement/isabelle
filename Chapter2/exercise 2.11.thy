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
    
(* fun zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zipWith _ [] _ = []"|
  "zipWith _ _  [] = []"|
  "zipWith f (x#xs) (y#ys) = (f x y) # zipWith f xs ys" *)
 
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
  
(* Can't prove this because xs could be []  
Can't assume (length xs > 0) and do induction on xs *)
(* lemma multCoeffs_v4_commutative_01:
  (* assumes "length xs > 0 \<and> y \<noteq> []" *)
  (* assumes "length xs > 0" *)
  shows "multCoeffs_v4 xs (0 # y # ys) = 0 # multCoeffs_v4 xs (y # ys)" 
proof(induction xs)
  case Nil
  then show ?case try
next
  case (Cons a xs)
  then show ?case sorry
qed *)

  
(* lemma multCoeffs_v4_commutative:
  shows "multCoeffs_v4 xs ys = multCoeffs_v4 ys xs"
proof(induction xs arbitrary: ys)
  case Nil
nitpick
  then show ?case

next
  case (Cons x xs)
  then show ?case 
  proof(cases ys)
    case Nil
    then show ?thesis by simp
  next
    case (Cons yh yt)
      (* facts *)
      (* multCoeffs_v4 xs ys = multCoeffs_v4 ys xs *)
      
      (* ?thesis \<equiv> multCoeffs_v4 (x # xs) ys = multCoeffs_v4 ys (x # xs) *)
      
      (* left side *)
    have "multCoeffs_v4 (x # xs) ys = addCoeffs (multCoeffs_by_scalar x ys) (multCoeffs_v4 xs (0 # ys))"
      by (simp add: local.Cons)
    then show ?thesis sorry
  qed
        (* "multCoeffs_v4 (l#ls) rs =  *)
    (* (let mult_l = multCoeffs_by_scalar l rs; *)
         (* rest =  *)
      (* in addCoeffs mult_l rest)"     *)
qed *)
  
value "multCoeffs_v4 [1,2] [3,4]"
    
fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]"  |
  "coeffs (Const i) = [i]"|
  "coeffs (Add l r) = addCoeffs (coeffs l) (coeffs r)" |
  "coeffs (Mult l r) = multCoeffs_v4 (coeffs l) (coeffs r)"
  
value "coeffs (createPolyExpression [4,2,-1] 0)"
value "coeffs (Mult (createPolyExpression [1,2,3] 0) (createPolyExpression [4,5] 0))"
  
(* lemma evalPoly_multiplication[simp]:"evalPoly (map (\<lambda>x. m*x) cs) x = m * (evalPoly cs x)"
  apply(induction cs) apply(auto)[1] apply(simp add: algebra_simps)
  done *)
    
(* lemma multCoeffs_v2_arg_length_1[simp]:
  assumes "evalPoly (coeffs expr) x = eval expr x"
  shows "evalPoly (multCoeffs_v2 [m] (coeffs expr)) x = m * eval expr x"
proof -
  have "evalPoly (map (\<lambda>x. m*x) (coeffs expr)) x = evalPoly (multCoeffs_v2 [m] (coeffs expr)) x"
    by (metis evalPoly.elims list.simps(8) multCoeffs_v2.simps(2) multCoeffs_v2.simps(3))
  fix cs
  have "m * (evalPoly cs x) = evalPoly (map (\<lambda>x. m*x) cs) x"
    by (simp)
  hence "m * (evalPoly (coeffs expr) x) = evalPoly (multCoeffs_v2 [m] (coeffs expr)) x"
    by (metis \<open>evalPoly (map (op * m) (coeffs expr)) x = evalPoly (multCoeffs_v2 [m] (coeffs expr)) x\<close> evalPoly_multiplication) 
  thus "evalPoly (multCoeffs_v2 [m] (coeffs expr)) x = m * eval expr x"
    by (simp add: assms) 
qed *)
  
(* lemma map_times0_equiv_replicate[simp]: "map (op * 0) (xs :: int list) = replicate (length xs) 0"
  apply(induction xs) apply(auto) done *)
    
(* lemma multCoeffs_v2_01[simp]:
  "evalPoly (multCoeffs_v2 [0, 1] cs) x = x * evalPoly cs x"
proof(induction cs)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  have "evalPoly (multCoeffs_v2 [0, 1] (c#cs)) x 
      = evalPoly ((0*c) # addCoeffs (map (op * 0) cs) (multCoeffs_v2 [1] (c#cs))) x" 
    by simp
  also have "... = evalPoly (0 # addCoeffs (map (op * 0) cs) (multCoeffs_v2 [1] (c#cs))) x" by simp
  also have "... = evalPoly (0 # addCoeffs (replicate (length cs) 0) (multCoeffs_v2 [1] (c#cs))) x" by simp
  also have "... = evalPoly (0 # (multCoeffs_v2 [1] (c#cs))) x" 
    by (metis addCoeffs_zeros length_map length_tl list.sel(3) multCoeffs_v2.simps(3))
  also have "... = evalPoly (0 # c # cs) x"
    by (metis evalPoly.simps(2) evalPoly_multiplication multCoeffs_v2.simps(3) mult_cancel_right2)
  also have "... = x * evalPoly (c # cs) x" by simp
  finally show ?case by simp
qed *)
  
(* value "multCoeffs_v2 [0, 1] [3,4,5]" *)
  
(* lemma evalPoly_multCoeffs_equiv_times: 
  assumes "evalPoly (coeffs l) x = eval l x" 
    and "evalPoly (coeffs r) x = eval r x"
    and "eval (Mult l r) x = eval l x * eval r x"
    and "evalPoly (coeffs (Mult l r)) x = evalPoly (multCoeffs_v2 (coeffs l) (coeffs r)) x"
  shows "evalPoly (multCoeffs_v2 (coeffs l) (coeffs r)) x = evalPoly (coeffs l) x * evalPoly (coeffs r) x"
proof(induction l)
  case Var
  have "evalPoly (multCoeffs_v2 (coeffs Var) (coeffs r)) x = evalPoly (multCoeffs_v2 [0,1] (coeffs r)) x" 
    by simp
  have "evalPoly (multCoeffs_v2 [0, 1] (coeffs r)) x = x * evalPoly (coeffs r) x" by simp
 
  have "evalPoly (coeffs Var) x = evalPoly [0,1] x" by simp
  hence "evalPoly (coeffs Var) x * evalPoly (coeffs r) x = evalPoly [0,1] x * evalPoly (coeffs r) x" 
    by simp
  also have "... = x * evalPoly (coeffs r) x" by simp
      
  then show ?case by simp
next
  case (Const i)
  have "evalPoly (multCoeffs_v2 (coeffs (Const i)) (coeffs r)) x 
      = evalPoly (multCoeffs_v2 [i] (coeffs r)) x" by simp
  also have left:"... = evalPoly (map (op * i) (coeffs r)) x"
    by (metis evalPoly.elims length_0_conv length_map multCoeffs_v2.simps(2) multCoeffs_v2.simps(3))
  finally have "... = i * evalPoly (coeffs r) x" by (simp)
      
  have "evalPoly (coeffs (Const i)) x * evalPoly (coeffs r) x 
      = evalPoly [i] x * evalPoly (coeffs r) x" by simp
  also have "... = i * evalPoly (coeffs r) x" by simp
  then show ?case 
    by (simp add: left)
next
  case (Add l1 l2)
 (* 1. \<And>l1 l2. 
  evalPoly (multCoeffs_v2 (coeffs l1) (coeffs r)) x = evalPoly (coeffs l1) x * evalPoly (coeffs r) x \<Longrightarrow> *)
    (* evalPoly (multCoeffs_v2 (coeffs l2) (coeffs r)) x = evalPoly (coeffs l2) x * evalPoly (coeffs r) x \<Longrightarrow> *)
    (* prove:
        evalPoly (multCoeffs_v2 (coeffs (Add l1 l2)) (coeffs r)) x 
      = evalPoly (coeffs (Add l1 l2)) x * evalPoly (coeffs r) x     *)
  have "evalPoly (multCoeffs_v2 (coeffs (Add l1 l2)) (coeffs r)) x = 
        evalPoly (multCoeffs_v2 (addCoeffs (coeffs l1) (coeffs l2)) (coeffs r)) x" by simp
  (* TODO HERE *)
  (* addCoeffs (coeffs l) (coeffs r) *)
  then show ?case try
next
  case (Mult l1 l2)
  then show ?case sorry
qed *)
  
  
(* lemma evalPoly_multCoeffs_v4_equiv_times[simp]: 
  assumes "evalPoly (coeffs l) x = eval l x" 
    and "evalPoly (coeffs r) x = eval r x"
    and "eval (Mult l r) x = eval l x * eval r x"
    and "evalPoly (coeffs (Mult l r)) x = evalPoly (multCoeffs_v4 (coeffs l) (coeffs r)) x"
  shows "evalPoly (multCoeffs_v4 (coeffs l) (coeffs r)) x = evalPoly (coeffs l) x * evalPoly (coeffs r) x"  
proof(induction l)
  case Var
(* evalPoly (multCoeffs_v4 (coeffs Var) (coeffs r)) x = evalPoly (coeffs Var) x * evalPoly (coeffs r) x *)
  fix cr assume "cr = coeffs r"
  hence "evalPoly (multCoeffs_v4 (coeffs Var) (coeffs r)) x = evalPoly (multCoeffs_v4 (coeffs Var) cr) x " 
    by simp
  also have "... = evalPoly (multCoeffs_v4 [0,1] cr) x" 
    by simp
  (* also *) finally have "... = evalPoly (multCoeffs_by_var 1 cr 1) x"
  proof -
    have "multCoeffs_v4 [0,1] cr = multCoeffs_v4_helper [0,1] cr 0" by simp
    also have "... = addCoeffs(multCoeffs_by_var 0 cr 0) (multCoeffs_v4_helper [1] cr 1)" 
      by (metis One_nat_def addCoeffs.simps(1) list.exhaust multCoeffs_by_var.simps(1) multCoeffs_v4_helper.simps(2) multCoeffs_v4_helper.simps(3))
    also have "... = addCoeffs (replicate (length cr) 0) (multCoeffs_v4_helper [1] cr 1)" 
      by simp
    also have "... = multCoeffs_v4_helper [1] cr 1"
    proof -
      have "length (multCoeffs_v4_helper [1] cr 1) = 1 + length cr" 
      proof -
        show ?thesis sorry
      qed
      show ?thesis sorry
    qed
    show ?thesis sorry
  qed
    (* finally *) 
  show ?case sorry
next
  case (Const x)
  then show ?case sorry
next
  case (Add l1 l2)
  then show ?case sorry
next
  case (Mult l1 l2)
  then show ?case sorry
qed
 *)
  
(* lemma evalPoly_coeffs_Mult_equiv_eval_Mult[simp]:
  fixes l :: exp and r :: exp and x :: int
  assumes "evalPoly (coeffs l) x = eval l x"
    and "evalPoly (coeffs r) x = eval r x"
  shows "evalPoly (coeffs (Mult l r)) x = eval (Mult l r) x"
proof -
  have "evalPoly (coeffs (Mult l r)) x = evalPoly (multCoeffs_v4 (coeffs l) (coeffs r)) x"
    by simp
  also have left:"... = evalPoly (coeffs l) x * evalPoly (coeffs r) x"
    using "5.eval.simps"(4) assms(1) assms(2) calculation evalPoly_multCoeffs_v4_equiv_times 
    by blast
      
  have "eval (Mult l r) x = (eval l x) * (eval r x)" by simp
  thus ?thesis 
    by (simp add: left assms(1) assms(2))
qed *)
  
(* lemma "evalPoly (coeffs poly) x = eval poly x"
  apply(induction poly)
     apply(simp)
    apply(simp)
   apply(simp)
    (* apply(auto simp add: algebra_simps mult_is_star add_is_plus) *)
done *)
  
  
theorem "evalPoly(coeffs expr) x = eval expr x"
proof(induction expr arbitrary: x)
  case Var
  then show ?case by simp
next
  case (Const x)
  then show ?case by simp
next
  case (Add l r)
  then show ?case by simp
next
  case (Mult l r)
 (* 1. \<And>expr1 expr2 x. *)
   (* (\<And>x. evalPoly (coeffs expr1) x = eval expr1 x) \<Longrightarrow> *)
   (* (\<And>x. evalPoly (coeffs expr2) x = eval expr2 x) \<Longrightarrow> 
  evalPoly (coeffs (Mult expr1 expr2)) x = eval (Mult expr1 expr2) x *)
    
    (* left side *)
  have "evalPoly (coeffs (Mult l r)) x = evalPoly (multCoeffs_v4 (coeffs l) (coeffs r)) x" 
    by simp
  fix cl cr assume "cl = coeffs l" and "cr = coeffs r"
  hence "evalPoly (multCoeffs_v4 (coeffs l) cr) x  = evalPoly (multCoeffs_v4 cl cr) x " 
    by simp
      (* TODO Or maybe the right side should be: eval l x * eval r x ? *)
  have "evalPoly (multCoeffs_v4 cl cr) x = evalPoly cl x * evalPoly cr x" 
  proof(induction cl)
    case Nil
    then show ?case by simp
  next
    case (Cons c cl)
      (* 1. \<And>a cl. evalPoly (multCoeffs_v4 cl (coeffs r)) x = evalPoly cl x * evalPoly (coeffs r) x \<Longrightarrow> *)
      (* evalPoly (multCoeffs_v4 (a # cl) (coeffs r)) x = evalPoly (a # cl) x * evalPoly (coeffs r) x       *)
    have "evalPoly (multCoeffs_v4 (c # cl) cr) x 
        = evalPoly (addCoeffs (multCoeffs_by_scalar c cr) (multCoeffs_v4 cl (0 # cr))) x"
    proof(induction cr)
      case Nil
 (* 1. evalPoly (multCoeffs_v4 (c # cl) []) x = evalPoly (addCoeffs (multCoeffs_by_scalar c []) (multCoeffs_v4 cl [0])) x *)
        (* left side *)
      have "evalPoly (multCoeffs_v4 (c # cl) []) x = evalPoly [] x" by simp
      hence "evalPoly (multCoeffs_v4 (c # cl) []) x = 0" by simp
          
          (* right side *)
      have "evalPoly (addCoeffs (multCoeffs_by_scalar c []) (multCoeffs_v4 cl [0])) x 
          = evalPoly (addCoeffs [] (multCoeffs_v4 cl [0])) x"
        by simp
      also have "... = evalPoly (multCoeffs_v4 cl [0]) x" by simp
      then show ?case try
    next
      case (Cons a cr)
      then show ?case sorry
    qed        
    then show ?case sorry
  qed
  
      (* right side *)
  have "eval (Mult l r) x = eval l x * eval r x" by simp
      
      (* then show ?case using evalPoly_coeffs_Mult_equiv_eval_Mult by blast *)
  (* then show ?case sorry *)
  show ?case sorry
qed
    
 (* theorem ceoffs_preserves_eval[simp]: "evalPoly(coeffs expr) x = eval expr x"
  apply(induction expr)
  apply(auto)
  done  *)
    
    (* 
I have not been able to complete the proof portion of exercise 2.11.
Since I can't prove my sort is well-behaved, I think I would not be able to prove that
\<forall> expr x. evalPoly (coeffs expr) x = eval expr x
 
Instead I will do my own modified proof:
eval (createPolyExpression coeffs headPower) x = evalPoly coeffs x
 *)
    
end
