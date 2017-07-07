theory WholeChapter imports Main begin
  
section "Chapter 5"
  
subsection "Exercise 5.1"
  
lemma 
  assumes T : "\<forall> x y. T x y \<or> T y x"
    and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
    and TA: "\<forall> x y. T x y \<longrightarrow> A x y" 
    and axy:"A b c"
  shows "T b c"
proof cases
  (* NB: the positive case has to come first, negative case comes second *)
  assume "A b c \<and> A c b"
  hence "b = c" using A by blast
  thus "T b c"
    using T by blast
next
  assume "\<not>(A b c \<and> A c b)"
  hence "\<not>A c b"
    by (simp add: axy)
  moreover have "\<forall> x y. T y x \<or> A x y" using T TA by blast
  ultimately show "T b c" by metis
qed
  
subsection "Exercise 5.2"
  
lemma "(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs) 
     \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  assume "even (length xs)"
  then obtain halfLength where hl:"2 * halfLength = length xs" 
    by (metis evenE)
  then obtain ys\<^sub>p where y:"ys\<^sub>p = take halfLength xs" by simp 
  then obtain zs\<^sub>p where z:"zs\<^sub>p = drop halfLength xs" by simp
  have "ys\<^sub>p @ zs\<^sub>p = xs"
    by (simp add: y z)
  moreover have "length ys\<^sub>p = length zs\<^sub>p" using hl y z by fastforce
  ultimately show ?thesis by fastforce 
next
  assume "\<not>even (length xs)"
  hence "odd (length xs)" by simp
  then obtain halfLength where hl:"2 * halfLength + 1 = length xs"
    by (metis oddE) 
  then obtain ys\<^sub>p where y:"ys\<^sub>p = take (halfLength + 1) xs" by simp 
  then obtain zs\<^sub>p where z:"zs\<^sub>p = drop (halfLength + 1) xs" by simp
  have "ys\<^sub>p @ zs\<^sub>p = xs"
    by (simp add: y z)
  moreover have "length ys\<^sub>p = length zs\<^sub>p + 1" using hl y z by fastforce
  ultimately show ?thesis by fastforce 
qed
  
subsection "unnamed 'simple' Exercise"
  
inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"
  
lemma "\<not>ev (Suc(Suc(Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  hence "ev (Suc 0)" 
    using ev.cases by blast
  thus False by cases
qed
  
  (* I can't reproduce the proof on page 68.   *)
lemma "ev (Suc m) \<Longrightarrow> \<not>ev m"
proof(induction "Suc m" arbitrary: m rule:ev.induct)
  (* case ev0 does not exist *)
  case (evSS n)
  then show ?case 
  proof - (* (rule (* classical *) ccontr) *)
    assume "ev (Suc n)"
      (*     thus False sorry
  qed
qed *)
    oops
      
lemma "ev (Suc m) \<Longrightarrow> \<not>ev m"
proof(induction "Suc m" arbitrary: m rule:ev.induct)
  case (evSS n)
  then show ?case
    using ev.cases by auto
qed
  
subsection "Exercise 5.3"
  
  (* rule inversion *)
lemma
  assumes a:"ev(Suc(Suc n))"
  shows "ev n"
proof -
  from a show "ev n"
  proof cases
    case evSS
    then show ?thesis by simp 
  qed
qed
  
  (* Can I do the same proof with induction? ... No.  *)
  (* lemma
  assumes a:"ev(Suc(Suc n))"
  shows "ev n"
proof(induction rule: ev.induct)
  (* Failed to apply initial proof method  *)
 *)
  
subsection "Exercise 5.4"
  
lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  thus False
  proof cases
    assume "ev (Suc 0)" 
    thus False
    proof cases
    qed
  qed
qed
  
subsection "Exercise 5.5"
  
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "iter r 0 x x" |
  step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"
  
lemma "iter r n x y \<Longrightarrow> star r x y"
proof(induction rule: iter.induct)
  case (refl x)
  then show ?case using star.refl by fast
next
  case (step x y n z)
  then show ?case by (meson star.step)
qed
  
subsection "Exercise 5.6"
  
fun elems :: "'a list \<Rightarrow> 'a set" where
  "elems [] = {}" |
  "elems (x # xs) = insert x (elems xs)"
  
lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ (x # zs) \<and> x \<notin> elems ys"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  fix a xs
  let "?case" = "\<exists>ys zs. a # xs = ys @ x # zs \<and> x \<notin> elems ys"
  assume IH : "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" 
    and prems : "x \<in> elems (a # xs)"
  then show ?case
  proof cases
    assume xa:"x = a"
    moreover obtain yp :: "'a list" where yp:"yp = []" by simp
    moreover obtain zp :: "'a list" where zp:"zp = xs" by simp
    ultimately have "a # xs = yp @ x # zp \<and> x \<notin> elems yp" by simp
    then show ?thesis by blast 
  next
    assume "x \<noteq> a"
    moreover then obtain ys zs where "xs = ys @ (x # zs) \<and> x \<notin> elems ys"
      using IH prems by auto
    moreover obtain ays where "ays = a # ys" by simp
    ultimately have "a # xs = ays @ x # zs \<and> x \<notin> elems ays" by auto
    thus ?thesis by blast
  qed 
qed
  
subsection "Exercise 5.7"
  
  (* copied from exercise 4.5 *)
  
datatype alpha = a | b
  
inductive gram_S :: "alpha list \<Rightarrow> bool" where
  empty: "gram_S []" |
  aSb: "gram_S w \<Longrightarrow> gram_S (a # w @ [b])" |
  SS: "gram_S w\<^sub>0 \<Longrightarrow> gram_S w\<^sub>1 \<Longrightarrow> gram_S (w\<^sub>0 @ w\<^sub>1)"
  
  (* end of copy-pasta *)
  
  (* Is the list a balanced list of parens? *)
  (* n (the first arg) is number of open parens (number of unmatched a's) *)
fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
  "balanced 0 [] = True" |
  "balanced _ [] = False" |
  "balanced n (a # rest) = balanced (Suc n) rest" |
  "balanced 0 (b # rest) = False" |
  "balanced (Suc n) (b # rest) = balanced n rest"
  
value "balanced 0 [a,a,b,b]"
value "balanced 0 [a,b,a,b]"
  
value "balanced 0 [a,b,b,b]"
value "balanced 0 [a,a,a,b,b]"
value "balanced 0 [a,a,b,b,b]"
value "balanced 0 [a,a,b]"
  
lemma insert_ab_middle_of_S:  "gram_S (xs @ ys) \<Longrightarrow> gram_S (xs @ [a, b] @ ys)"
proof(induction "(xs @ ys)" arbitrary: xs ys rule: gram_S.induct)
  case empty
  then show ?case
    using aSb gram_S.empty by force 
next
  fix w xs ys
  let "?case" = "gram_S (xs @ [a, b] @ ys)"
  assume hyps: 
    "gram_S w" 
    "\<And>fs gs. w = fs @ gs \<Longrightarrow> gram_S (fs @ [a, b] @ gs)" 
    "a # w @ [b] = xs @ ys"    
  then show ?case
  proof(cases "length xs > 0")
    case x_nontrivial:True
    then show ?thesis
    proof(cases "length ys > 0")
      case y_nontrivial:True
      obtain fs gs where fs:"fs = drop 1 xs" and gs:"gs = butlast ys" by simp
      hence "gram_S (fs @ [a, b] @ gs)"
        by (metis One_nat_def butlast_append butlast_snoc drop_0 drop_Suc hyps(2) hyps(3) length_greater_0_conv list.sel(3) tl_append2 x_nontrivial y_nontrivial)
      hence gram_all:"gram_S (a # fs @ [a, b] @ gs @ [b])"
        by (metis append.assoc gram_S.simps) 
      moreover have "a # fs = xs"
        using fs x_nontrivial
        by (metis Cons_nth_drop_Suc One_nat_def append_eq_Cons_conv drop_0 hyps(3)
            length_greater_0_conv nth_Cons_0)
      moreover have "gs @ [b] = ys"
        using gs y_nontrivial
        by (metis hyps(3) last.simps last_appendR length_greater_0_conv snoc_eq_iff_butlast)
      ultimately show ?thesis by auto
    next
      case False
      hence "length ys = 0" by simp
      then show ?thesis 
        by (metis False SS aSb append_Nil append_Nil2 empty hyps(1) hyps(3) length_greater_0_conv) 
    qed
  next
    case False
    hence "length xs = 0" by simp
    then show ?thesis
      by (metis False SS aSb append_self_conv2 empty hyps(1) hyps(3) length_greater_0_conv) 
  qed
next
  fix w\<^sub>0 w\<^sub>1 xs ys
  let "?case" = "gram_S (xs @ [a, b] @ ys)"
  assume hyps: 
    "gram_S w\<^sub>0" 
    "\<And>fs gs. w\<^sub>0 = fs @ gs \<Longrightarrow> gram_S (fs @ [a, b] @ gs)" 
    "gram_S w\<^sub>1"
    "\<And>fs gs. w\<^sub>1 = fs @ gs \<Longrightarrow> gram_S (fs @ [a, b] @ gs)" 
    "w\<^sub>0 @ w\<^sub>1 = xs @ ys"
    (* We have no proof that w\<^sub>0=xs, so while we can easily prove
      gram_S (w\<^sub>0 @ [a,b] @ w\<^sub>1)
      It does us no good, without said proof. *)
  moreover have sab:"gram_S [a,b]"
    using aSb empty by fastforce
  ultimately show ?case 
  proof(cases "length w\<^sub>0 = length xs")
    case True
    then show ?thesis 
      by (metis SS append_eq_append_conv hyps(1) hyps(3) hyps(5) sab)
  next
    case neq:False
    then show ?thesis 
    proof(cases "length w\<^sub>0 < length xs")
      case True
        (* Then if we inserted [a,b] after xs, we'd be inserting it into the middle of w\<^sub>1. Prove
        that's ok. *)
      then obtain len_w1_prefix where lwp:"len_w1_prefix = length xs - length w\<^sub>0" by simp
      obtain lh rh where lhrh:"lh = w\<^sub>0 @ (take len_w1_prefix w\<^sub>1) \<and> rh = (drop len_w1_prefix w\<^sub>1)" by simp
      hence "gram_S (lh @ [a,b] @ rh)"
        using SS hyps(1) hyps(4) by auto
      moreover have "lh = xs \<and> rh = ys"
        by (metis True append_eq_conv_conj append_self_conv2 drop_all drop_append hyps(5) less_or_eq_imp_le lhrh lwp take_all take_append) 
      ultimately show ?thesis by simp
    next
      case False
      hence "length w\<^sub>0 > length xs" 
        using neq by auto 
          (* Then if we inserted [a,b] after xs, we'd be inserting it into the middle of w\<^sub>0. Prove
        that's ok. *)
      then obtain len_xs where "len_xs = length xs" by simp
      moreover obtain lh rh where "lh = (take len_xs w\<^sub>0) \<and> rh = (drop len_xs w\<^sub>0) @ w\<^sub>1" by simp
      moreover hence glh:"gram_S (lh @ [a,b] @ rh)"
        by (metis append.assoc append_take_drop_id gram_S.simps hyps(2) hyps(3))
      ultimately have "lh = xs \<and> rh = ys" 
        by (metis False append_eq_append_conv_if hyps(5) le_neq_implies_less)
      thus ?thesis using glh by simp
    qed
  qed
qed
  
  (* The `a` in `replicate n a` is the first constructor of datatype alpha *)
lemma balanced_implies_S:"balanced n string \<Longrightarrow> gram_S (replicate n a @ string)"
proof(induction n string rule: balanced.induct)
  case 1
  then show ?case by (simp add: empty)
next
  case (2 v)
  then show ?case by (simp add: empty)
next
  case (3 n rest)
  then show ?case 
    by (metis Cons_eq_appendI balanced.simps(3) replicate_Suc replicate_app_Cons_same) 
next
  case (4 rest)
  then show ?case 
    using balanced.simps(4) by blast 
next
  case (5 n rest)
  hence "balanced n rest"
    by simp
  hence 0:"gram_S (replicate n a @ rest)"
    by (simp add: "5.IH")
  hence "gram_S (replicate n a @ [a, b] @ rest)"
    using insert_ab_middle_of_S by simp 
  hence "gram_S (replicate (Suc n) a @ b # rest)"
    by (simp add: replicate_app_Cons_same)
  thus ?case
    by simp 
qed
  
lemma balanced_append_b:"balanced n string \<Longrightarrow> balanced (Suc n) (string @ [b])"
proof(induction "(Suc n)" "(string @ [b])" arbitrary: n string rule: balanced.induct)
  case (2 v)
  then show ?case by simp
next
  case (3 rest)
  then show ?case 
    by (metis Cons_eq_append_conv alpha.distinct(1) balanced.simps(3) list.inject)
next
  case pop_b:(5 n rest)
  moreover hence bal_sn:"balanced (Suc n) (b # string)"
    using balanced.simps(5) by simp
  ultimately show ?case
  proof(cases n)
    case 0
    moreover have "balanced (Suc n) (b # string)"
      by (metis bal_sn)
    ultimately show ?thesis
      using pop_b balanced.simps(4) by (metis butlast.simps(2) butlast_snoc)
  next
    case (Suc pred_n)
    then show ?thesis 
      using pop_b bal_sn by (metis Cons_eq_append_conv balanced.simps(5))
  qed
qed
  
lemma balanced_append_string:
  "balanced 0 (drop len_prefix string) \<Longrightarrow> balanced n (take len_prefix string)
    \<Longrightarrow> balanced n string"  
proof(induction string arbitrary: n len_prefix)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof(induction n)
    case 0
    then show ?case 
      by (metis balanced.elims(2) balanced.simps(3) balanced.simps(4) drop_Cons' list.inject
          list.simps(3) take_Cons')
  next
    case (Suc n)
    then show ?case
    proof(cases x)
      case a
      then show ?thesis
        by (metis Cons.IH Suc.prems(2) Suc.prems(3) balanced.simps(2) balanced.simps(3) drop_Cons'
            take_Cons')
    next
      case b
      then show ?thesis 
        by (metis Cons.IH Suc.prems(2) Suc.prems(3) balanced.elims(2) balanced.simps(5) drop_Cons'
            list.simps(3) take_Cons')
    qed
  qed
qed 
  
lemma S_implies_balanced:"gram_S (replicate n a @ string) \<Longrightarrow> balanced n string"
proof(induction "(replicate n a @ string)" arbitrary: n string rule: gram_S.induct)
  case empty
  then show ?case
    by simp
next
  case (aSb w)
  show ?case
  proof(cases n)
    case 0
    then show ?thesis
      using aSb.hyps(2) aSb.hyps(3) balanced_append_b by auto
  next
    case (Suc n_minus_1)
    moreover have 0:"string = butlast string @ [b]"
      by (metis Suc_neq_Zero aSb.hyps(3) alpha.distinct(1) calculation last_ConsR last_appendL last_appendR last_replicate snoc_eq_iff_butlast)
    ultimately have "w = replicate n_minus_1 a @ (butlast string)"
      by (metis aSb.hyps(3) butlast_append list.sel(3) replicate_Suc replicate_append_same snoc_eq_iff_butlast tl_append2)
    hence "balanced n_minus_1 (butlast string)"
      using aSb.hyps(2) by blast
    hence "balanced n string"
      using 0 Suc balanced_append_b by fastforce
    thus ?thesis by simp
  qed
next
  case (SS w\<^sub>0 w\<^sub>1)
  then show ?case
  proof(cases "length w\<^sub>0 = n")
    case True
    then show ?thesis 
      by (metis SS.hyps(2) SS.hyps(4) SS.hyps(5) append.right_neutral append_eq_append_conv
          append_self_conv2 balanced.simps(2) gr0_conv_Suc length_greater_0_conv length_replicate)
  next
    case len_ne:False
    then show ?thesis 
    proof(cases "length w\<^sub>0 < n")
      case len_w_lt:True
      hence "w\<^sub>0 = take (length w\<^sub>0) (replicate n a @ string)"
        using SS.hyps(5) append_eq_conv_conj by blast
      hence "w\<^sub>0 = take (length w\<^sub>0) (replicate n a)"
        using len_w_lt by fastforce
      hence "w\<^sub>0 = replicate (length w\<^sub>0) a"
        by (metis length_replicate take_replicate)
      hence "w\<^sub>0 = replicate (length w\<^sub>0) a @ []"
        by simp
      hence bal:"balanced (length w\<^sub>0) []"
        using SS.hyps(2) by blast
          (* Now work on w\<^sub>1 *)
      hence "w\<^sub>1 = drop (length w\<^sub>0) (replicate n a @ string)"
        using SS.hyps(5) append_eq_conv_conj by blast
      hence "w\<^sub>1 = replicate (n - length w\<^sub>0) a @ string"
        using len_w_lt by simp
      hence "balanced (n - length w\<^sub>0) string"
        by (simp add: SS.hyps(4))
      thus ?thesis 
        by (metis Nitpick.size_list_simp(2) SS.hyps(4) SS.hyps(5) bal balanced.simps(2)
            self_append_conv2) 
    next
      case False
      hence len_w_gt:"length w\<^sub>0 > n"
        using len_ne by auto
      hence "w\<^sub>0 = take (length w\<^sub>0) (replicate n a @ string)"
        using SS.hyps(5) append_eq_conv_conj by blast
      hence "w\<^sub>0 = replicate n a @ take (length w\<^sub>0 - n) string"
        by (metis len_w_gt length_replicate less_imp_le_nat take_all take_append)
      hence bal_w0:"balanced n (take (length w\<^sub>0 - n) string)"
        using SS.hyps(2) by blast
          (* Now work on w\<^sub>1 *)
      hence "w\<^sub>1 = drop (length w\<^sub>0) (replicate n a @ string)"
        using SS.hyps(5) append_eq_conv_conj by blast
      hence "w\<^sub>1 = drop (length w\<^sub>0 - n) string"
        using len_w_gt by simp
      hence "balanced 0 (drop (length w\<^sub>0 - n) string)"
        by (simp add: SS.hyps(4))
      then show ?thesis 
        using bal_w0 balanced_append_string by blast
    qed
  qed
qed
  
theorem "balanced n w = gram_S (replicate n a @ w)"
  using S_implies_balanced balanced_implies_S by blast
    
end