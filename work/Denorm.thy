theory Denorm
  imports Main "~~/src/HOL/Library/Code_Target_Nat" 
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE"
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE_Properties"
begin
  
lemma Val_zero:"Val Plus_zero = (0 :: real)"
proof -
  have "(0,0,0) = Rep_float Plus_zero"
    using Abs_float_inverse Plus_zero_def is_valid_special(5) by fastforce
  moreover have "valof float_format (0,0,0) = 0" by simp
  ultimately show ?thesis 
    by (simp add: Val_def)
qed
  
  (* Negative (finite) numbers are \<le> 0 *)
lemma negative_lt_zero:
  fixes x :: float
  assumes finite:"Finite x"
    and negative:"Sign x = 1"
  shows "x \<le> Plus_zero"
proof -
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
    using Finite_def Val_def float_zero1 local.finite sef Val_zero by auto
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
  shows "\<nexists>x :: float. x < SmallPositiveDenorm \<and> x > Plus_zero \<and> Finite x"
proof(rule ccontr)
  assume "\<not>(\<nexists>x. x < SmallPositiveDenorm \<and> x > Plus_zero \<and> Finite x)"
  hence 0:"(\<exists>x. x < SmallPositiveDenorm \<and> x > Plus_zero  \<and> Finite x)" by auto
  then obtain y where y:"y < SmallPositiveDenorm \<and> y > Plus_zero \<and> Finite y" by auto
  obtain ys ye yf where ysef:"(ys, ye, yf) = Rep_float y" 
    by (metis Abs_float_inverse finite_nan float_double_neg_eq float_neg_def fneg_def 
        is_valid_defloat mem_Collect_eq neg_valid y)
  hence fesy:"Sign y = ys \<and> Exponent y = ye \<and> Fraction y = yf"
    by (metis Exponent_def Fraction_def Sign_def exponent.simps fraction.simps sign.simps)

  have "Sign y < 2"
    using Sign_def is_valid_defloat is_valid by auto
  hence 1:"Sign y = 0 \<or> Sign y = 1"
    by (simp add: less_2_cases)
  hence ypos:"Sign y = 0"
  proof(cases "Sign y = 0")
    case True
    then show ?thesis by simp
  next
    case False
    hence "Sign y = 1" 
      using 1 by simp
    hence "y \<le> Plus_zero"
      by (simp add: negative_lt_zero y)
    then show ?thesis 
      using Finite_def float_le_neg float_zero1 y by blast 
  qed
    
  have "Val y > 0"
    using Finite_def Val_zero float_zero1 y by auto
  hence valof:"valof float_format (0, ye, yf) > 0"
    using Val_def fesy ypos ysef by auto

  have "Fraction y > 0"
  proof(rule ccontr)
    assume "\<not>(Fraction y > 0)"
    hence "Fraction y \<le> 0" by simp
    hence "yf \<le> 0"
      by (simp add: fesy)
    hence "yf = 0" by simp 
    hence "valof float_format (0, ye, 0) > 0"      
      using valof by auto
        
    have "\<forall>exp. valof float_format (0, exp, 0) = 0"
    proof
      fix exp
      have "valof float_format (0, exp, 0) = 0"
      proof(cases "exp = 0")
        case True
        then show ?thesis 
          by simp 
      next
        case False
          (* Crap, I forgot about the implicit 1 *)
        hence "valof float_format (0, exp, 0) = ((2^exp) / (2^bias float_format)) * (1 + 0)"
          by simp
        then show ?thesis try
      qed
        
      show ?thesis
        proof
      have "valof float_format (0, exp, 0) = (-1::real)^0 * (2 / (2^bias float_format)) * (real 0/2^(fracwidth float_format))"
      (* have "valof float_format (0, exp, 0) = 1 * (2 / (2^bias float_format)) * (real 0)" *)
        sledgehammer
          sorry
    qed
(*     hence "valof float_format (0, ye, yf) > 0"
      try *)
    then show False 
      sledgehammer sorry
  qed
    
  have "Exponent y = 0"
  proof(rule ccontr)
    assume "Exponent y \<noteq> 0"
    (* hence 0:"(\<exists>x. x < SmallPositiveDenorm \<and> x > Plus_zero  \<and> Finite x)" by auto *)
    then show False sorry
  qed

    (* using 0 *)
    (* try *)
    
    

  then show False sorry
qed
  
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