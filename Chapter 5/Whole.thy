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
  
end