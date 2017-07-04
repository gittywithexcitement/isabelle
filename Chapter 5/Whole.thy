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
  hence 0:"\<not>A y x"
    by (simp add: axy)
  have "\<forall> x y. T y x \<or> A x y" using T TA by blast
  thus "T x y"  by (meson \<open>\<forall>x y. T y x \<or> A x y\<close> 0)
qed
    
    (* proof (rule ccontr)
  assume "\<not>(T x y)"
    (* If I can prove \<not>(A x y), then that implies \<not>(T x y)
      Not sure how that helps. *)
  hence "\<forall> x y. T y x"  
    using T A TA assms(4) by blast
  have "\<forall> x y. T y x \<or> A x y" using T TA by blast
      (* If I can prove x \<noteq> y, then \<not>(A x y \<and> A y x)
                                   ... = (\<not>A x y) \<or> (\<not>A y x) 
          because A x y, we have \<not>A y x*)
  show False sorry
qed
 *)  
    
    (* Is A y x true? *)
    
    
end