theory Whole imports Main begin
  
section "Chapter 5"
subsection "Exercise 5.1"
  
lemma 
  assumes T : "\<forall> x y. T x y \<or> T y x"
    and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
    and TA: "\<forall> x y. T x y \<longrightarrow> A x y" 
    and axy:"A x y" (* Should this be prefixed with \<forall> x y? *)
  shows "T x y" (* Should this be prefixed with \<forall> x y? *)
proof cases
  assume "A x y \<and> A y x"
  hence "x = y" using A by blast
  thus "T x y"
    using T by blast
next
  assume "\<not>(A x y \<and> A y x)"
  hence "\<not>A y x"
    by (simp add: axy)
  moreover have "\<forall> x y. T y x \<or> A x y" using T TA by blast
  ultimately show "T x y" by metis
qed

end