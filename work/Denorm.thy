theory Denorm
  imports Main "~~/src/HOL/Library/Code_Target_Nat" 
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE"
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE_Properties"
begin
  
  
  (* Negative (finite) numbers are \<le> 0 *)
lemma negative_lt_zero:
  fixes x :: float
  assumes finite:"Finite x"
    and negative:"Sign x = 1"
  shows "x \<le> Plus_zero"
proof -
  have zero:"Val Plus_zero = (0 :: real)"
  proof -
    have "(0,0,0) = Rep_float Plus_zero"
      using Abs_float_inverse Plus_zero_def is_valid_special(5) by fastforce
    moreover have "valof float_format (0,0,0) = 0" by simp
    ultimately show ?thesis 
      by (simp add: Val_def)
  qed
  obtain s e f where sef:"(s, e, f) = Rep_float x"
    by (metis Abs_float_inverse finite_nan float_double_neg_eq float_neg_def fneg_def
        is_valid_defloat local.finite mem_Collect_eq neg_valid)
  hence s1:"s = 1"
    by (metis Sign_def negative sign.simps)
  hence "valof float_format (1, e, f) \<le> 0"
    by simp
  hence "valof float_format (s, e, f) \<le> 0"
    using s1 by simp
  thus ?thesis 
    using Finite_def Val_def float_zero1 local.finite sef zero by auto
qed
    
  
(*   TODO 
definition float_format :: format
  where "float_format = (8, 23)" *)

(* Let's write a proof about what's the smallest positive denormal   *)
  (* definition is_denormal :: "format \<Rightarrow> representation \<Rightarrow> bool" *)
  (* where "is_denormal x a \<longleftrightarrow> exponent a = 0 \<and> fraction a \<noteq> 0" *)
definition small_positive_denorm :: "format \<Rightarrow> representation"
  where "small_positive_denorm x = (0, 0, 1)"
definition SmallPositiveDenorm :: "float"
  where "SmallPositiveDenorm = Abs_float (small_positive_denorm float_format)"

lemma SmallestPositiveDenorm:
  fixes x :: float
    (* I could probably use \<not>Isnan x *)
  (* assumes finite:"Finite x"  *)
  shows "\<nexists>x. x < SmallPositiveDenorm \<and> x > Plus_zero \<and> Finite x"
proof(rule ccontr)
  assume "\<not>(\<nexists>x. x < SmallPositiveDenorm \<and> x > Plus_zero \<and> Finite x)"
  hence 0:"(\<exists>x. x < SmallPositiveDenorm \<and> x > Plus_zero  \<and> Finite x)" by auto
  then obtain y where y:"y > Plus_zero \<and> Finite y" by auto
  have "Sign y < 2"
    using Sign_def is_valid_defloat is_valid by auto
  hence 1:"Sign y = 0 \<or> Sign y = 1"
    by (simp add: less_2_cases)
  hence "Sign y = 0"
  proof(cases "Sign y = 0")
    case True
    then show ?thesis by simp
  next
    case False
      (* If sign is 1, then it's negative, which means it breaks larger than zero *)
    hence "Sign y = 1" 
      using 1 by simp
    hence "y \<le> Plus_zero"
      try
    then show ?thesis try sorry
  qed
    
    try
    sorry
  then show False sorry
qed

 (* by contradiction *)
  have "x > Plus_zero" 
    (* 1. \<exists>x<SmallPositiveDenorm. Plus_zero < x \<Longrightarrow> False *)
  try
    
  oops
  
value "is_denormal float_format (0,0,1)"
value "is_valid float_format (0,0,1)"
value "valof float_format (0,0,1)"
  
value "Abs_float (0,0,1)"
value "Val (Abs_float (0,0,1))"
value "valof float_format (0,0,1)"

value "Topfloat"
value "Val (Topfloat)"
value "valof float_format (0, 254, 8388607)"

value "Bottomfloat" 
value "Val (Bottomfloat)"  
value "valof float_format (1, 254, 8388607)"

value "1 / 7 :: real"  
value "Float (1 / 7 :: real)"  

value "Float (1/1)"
  
value "Float 1"
  
value "Isdenormal (0,0,1)"   
value "Iszero (0,0,1)"
value "Iszero (Float (0,0,1))"
  
value "is_zero float_format (Rep_float a)"  
value "is_zero float_format (0,0,0)"  
  
  
(* lemma smallest_denorm:""   *)