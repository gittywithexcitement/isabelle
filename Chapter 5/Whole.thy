theory Whole imports Main begin
  
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
    thus False sorry
  qed
qed
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
    obtain yp :: "'a list" where yp:"yp = []" by simp
    obtain zp :: "'a list" where zp:"zp = xs" by simp
    have "a # xs = yp @ x # zp \<and> x \<notin> elems yp" using xa yp zp by simp
    then show ?thesis by blast 
  next
    assume xa:"x \<noteq> a"
    then obtain ys zs where yz:"xs = ys @ (x # zs) \<and> x \<notin> elems ys"
      using IH prems by auto
    obtain ays where ays:"ays = a # ys" by simp
    hence "x \<notin> elems ays" using xa yz by auto
    moreover have "a # xs = ays @ x # zs"
      using ays yz by auto
    ultimately show ?thesis by blast
  qed 
qed
          
end