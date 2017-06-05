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
fun coeffsOld :: "exp \<Rightarrow> int list" where
  "coeffsOld (Const i) = [i]"|
  "coeffsOld (Add l r) = coeffsOld l @ coeffsOld r"|
  "coeffsOld (Mult l r) = coeffsOld l @ coeffsOld r"|
  "coeffsOld Var = []"
  
value "coeffsOld (createPolyExpression [4,2,-1] 0)"
value "coeffsOld (createPolyExpression [4,2,-1,3] 0)"
  
  (* TODO implement using zip and map   *)
fun addCoeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "addCoeffs [] r = r" |
  "addCoeffs l [] = l" |
  "addCoeffs (l#ls) (r#rs) = (l+r) # addCoeffs ls rs"
    
lemma addCoeffs_eval[simp]:
  "evalPoly(addCoeffs coeffs1 coeffs2) x = evalPoly coeffs1 x + evalPoly coeffs2 x"
  apply(induction coeffs1 rule: addCoeffs.induct) (* adding arbitrary: coeffs2 breaks it *)
    apply(simp_all add: algebra_simps)
  by (metis addCoeffs.elims neq_Nil_conv)
    
lemma
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
  
lemma
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
  
  (* This can't be proved because each returns a different result involving addCoeffs *)
  (* "(multCoeffsHelper coeffs1 coeffs2 []) = (multCoeffsHelper coeffs2 coeffs1 [])" *)
  
lemma multCoeffsHelper_01:
  "evalPoly (multCoeffsHelper [] coeffs2 []) = evalPoly (multCoeffsHelper coeffs2 [] [])"
  apply(induction coeffs2) by auto
    
    (* lemma multCoeffsHelper_commutative[simp]:  
  "evalPoly (multCoeffsHelper coeffs1 coeffs2 []) = evalPoly (multCoeffsHelper coeffs2 coeffs1 [])" 
  apply(induction coeffs1 (* arbitrary: coeffs2 *)) using multCoeffsHelper_01 apply auto[1] 
    
  apply(induction coeffs1 rule:multCoeffsHelper.induct) apply(auto)
   apply(simp_all add: algebra_simps)
  done *)
    
fun multCoeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where  
  "multCoeffs l r = multCoeffsHelper l r []"
  
  (*lemma multCoeffs_eval[simp]:  
  "evalPoly (multCoeffs coeffs1 coeffs2) x =
       evalPoly coeffs1 x * evalPoly coeffs2 x"
  apply(induction coeffs1 arbitrary: coeffs2 rule: multCoeffsHelper.induct) apply(simp_all add: algebra_simps) *)   
  (*  apply(induction coeffs1 arbitrary: coeffs2 rule: multCoeffs.induct) apply(simp_all add: algebra_simps) *)    
  
  (* apply(induction coeffs1 rule: multCoeffs.induct) *)
  (* apply(induction coeffs1 arbitrary: coeffs2) apply(simp_all add: algebra_simps) *)
  
fun multCoeffs_v2 :: "int list \<Rightarrow> int list \<Rightarrow> int list" where  
  "multCoeffs_v2 [] _  = []" |
  "multCoeffs_v2 _  [] = []" |  
  "multCoeffs_v2 [l] rs = map (\<lambda>x. l*x) rs"| (* helper for proofs. Not sure if it's useful *)
  "multCoeffs_v2 (l#ls) (r#rs) = 
    (let l_times_rs = (map (op * l) rs);
         ls_times_rrs = multCoeffs_v2 ls (r#rs)
      in (l*r) # addCoeffs l_times_rs ls_times_rrs)"
  (* (let l_times_rs = (map (\<lambda>ri. l*ri) rs);
         ls_times_rs = multCoeffs_v2 ls rs
      in (hd l_times_rs) # addCoeffs (tl l_times_rs) ls_times_rs)" *)
  
lemma multCoeffs_v2_01[simp]:
  "evalPoly (multCoeffs_v2 [] coeffs2) = evalPoly (multCoeffs_v2 coeffs2 [])"  
  apply(induction coeffs2) by auto
    
    (* lemma multCoeffs_v2_commutative[simp]:  
  "evalPoly (multCoeffs_v2 coeffs1 coeffs2) = evalPoly (multCoeffs_v2 coeffs2 coeffs1)" 
  (* apply(induction coeffs1)     *)
  apply(induction coeffs1 arbitrary: coeffs2)
  using multCoeffs_v2_01 apply auto[1] 
    done *)
    
fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]"  |
  "coeffs (Const i) = [i]"|
  "coeffs (Add l r) = addCoeffs (coeffs l) (coeffs r)" |
  "coeffs (Mult l r) = multCoeffs_v2 (coeffs l) (coeffs r)"
  (* "coeffs (Mult l r) = multCoeffs (coeffs l) (coeffs r)" *)
  
value "coeffs (createPolyExpression [4,2,-1] 0)"
value "coeffs (Mult (createPolyExpression [1,2,3] 0) (createPolyExpression [4,5] 0))"
  
lemma evalPoly_multiplication:"m * (evalPoly cs x) = evalPoly (map (\<lambda>x. m*x) cs) x"
  apply(induction cs) apply(auto)[1] apply(simp add: algebra_simps)
  done
    
lemma 
  assumes "evalPoly (coeffs expr) x = eval expr x"
  shows "evalPoly (multCoeffs_v2 [m] (coeffs expr)) x = m * eval expr x"
proof -
  have "evalPoly (map (\<lambda>x. m*x) (coeffs expr)) x = evalPoly (multCoeffs_v2 [m] (coeffs expr)) x"
    by (metis evalPoly.elims list.simps(8) multCoeffs_v2.simps(2) multCoeffs_v2.simps(3))
  fix cs
  have "m * (evalPoly cs x) = evalPoly (map (\<lambda>x. m*x) cs) x"
    by (simp add: evalPoly_multiplication)
  hence "m * (evalPoly (coeffs expr) x) = evalPoly (multCoeffs_v2 [m] (coeffs expr)) x"
    by (simp add: \<open>evalPoly (map (op * m) (coeffs expr)) x = evalPoly (multCoeffs_v2 [m] (coeffs expr)) x\<close> evalPoly_multiplication) 
  thus "evalPoly (multCoeffs_v2 [m] (coeffs expr)) x = m * eval expr x"
    by (simp add: assms) 
qed
  
lemma map_times0_equiv_replicate[simp]: "map (op * 0) (xs :: int list) = replicate (length xs) 0"
  apply(induction xs) apply(auto) done
    
    
TODO flip xs and ys, and pr    
    
lemma
  fixes xs :: "int list" and ys :: "int list"
  assumes "length xs \<le> length ys"
  shows "addCoeffs (map (op * 0) xs) ys = ys"
proof(induction xs) (* induction on ys does not work *)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
    (* 1. \<And>a xs. addCoeffs (map (op * 0) xs) ys = ys 
             \<Longrightarrow> addCoeffs (map (op * 0) (a # xs)) ys = ys *)
  nitpick (* finds a counterexample! because a#xs is now longer by 1 *)
  fix y ys1 assume "y#ys1 = ys"
  have "addCoeffs (map (op * 0) (x # xs)) (y#ys1) = y # addCoeffs (map (op * 0) xs) ys1" by simp 
  fix zs :: "int list" assume "length zs = length ys"
  have "addCoeffs (map (op * 0) (x#xs)) zs = addCoeffs (map (op * 0) xs) zs" try
      (* have "addCoeffs (map (op * 0) (a # xs) = addCoeffs (map (op * 0) xs" by *)
      
      (* have "y # addCoeffs (map (op * 0) xs) ys1 = y # ys1" Cant easily prove *)
      (* hence "y # addCoeffs (map (op * 0) xs) ys = y # ys" using Cons.IH by blast *)
      (* have "y # addCoeffs (map (op * 0) xs) ys = y # addCoeffs (replicate (length xs) 0) ys" by simp *)
      (* hence "addCoeffs (map (op * 0) (x # xs)) (y#ys) = y # addCoeffs (replicate (length xs) 0) ys" by simp *)
      (* TODO WIP use lemma to show map (op * 0) xs is replicate *)
      
      (* then show ?case by sledgehammer *)
      
      (* "addCoeffs (l#ls) (r#rs) = (l+r) # addCoeffs ls rs" *)
  qed
    
lemma
  assumes "evalPoly (coeffs expr2) x = eval expr2 x"
  shows "evalPoly (multCoeffs_v2 [0, 1] (coeffs expr2)) x = x * eval expr2 x"  
proof -
  fix cs
    (* have "0 # (multCoeffs_v2 [1] cs) = multCoeffs_v2 [0, 1] cs" *)
    (* have "0 # cs = multCoeffs_v2 [0, 1] cs" *)
    (* have "(0*hd cs) # (addCoeffs (map (\<lambda>x. 0*x) cs) (multCoeffs_v2 [1] cs)) = multCoeffs_v2 [0, 1] cs" by auto *)
  fix c
    (* have "(0*c) # (addCoeffs (map (op * 0) cs) (multCoeffs_v2 [1] (c#cs))) = multCoeffs_v2 [0, 1] (c#cs)" *)
  have "multCoeffs_v2 [0, 1] (c#cs) = 0 # (addCoeffs (map (op * 0) cs) (multCoeffs_v2 [1] (c#cs)))"
    by simp
      
      (* TODO WIP. use lemma above to simplify  addCoeffs (map (op * 0) cs) xs = xs*)
      
      (* "multCoeffs_v2 (l#ls) (r#rs) = 
    (let l_times_rs = (map (\<lambda>ri. l*ri) rs);
         ls_times_rrs = multCoeffs_v2 ls (r#rs)
      in (l*r) # addCoeffs l_times_rs ls_times_rrs)" *)
      
      
      
      (*     (let l_times_rs = (map (\<lambda>ri. l*ri) rs);
         ls_times_rrs = multCoeffs_v2 ls (r#rs) *)
qed
  
value "multCoeffs_v2 [0, 1] [3,4,5]"
  
  
  
  (* lemma multCoeffs_v2_eval_distributive: (* \<And>expr1 expr2. *)
  "evalPoly (coeffs expr1) x = eval expr1 x \<Longrightarrow>
   evalPoly (coeffs expr2) x = eval expr2 x \<Longrightarrow>
    evalPoly (multCoeffs_v2 (coeffs expr1) (coeffs expr2)) x = eval expr1 x * eval expr2 x"
  apply(induction expr1) apply(auto)
    done *)
  (* apply(induction expr1 arbitrary:expr2) apply(auto) *)
  
  (* apply(induction arbitrary:expr1 expr2 rule:multCoeffs_v2.induct) apply(auto) *)
  (* apply(induction arbitrary: expr2 rule:multCoeffs_v2.induct) apply(auto) *)
  (* apply(induction arbitrary: expr1 rule:multCoeffs_v2.induct) apply(auto) *)
  
  
  (* Needs multCoeffs_v2_eval_distributive     *)
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