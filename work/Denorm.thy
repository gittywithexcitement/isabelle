theory Denorm
  imports Main "~~/src/HOL/Library/Code_Target_Nat" 
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE"
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE_Properties"
begin
  
subsection \<open>Special values\<close>

definition topfraction :: "format \<Rightarrow> nat"
  where "topfraction x = 2^(fracwidth x) - 1"
    
subsection \<open>Properties of Special values\<close>
  
lemma topfraction_largest:
  assumes valid:"is_valid fmt a"
  shows "fraction a \<le> topfraction fmt"
proof (rule ccontr)
  assume "\<not> fraction a \<le> topfraction fmt"
  hence "fraction a > topfraction fmt"
    by simp
  hence "fraction a > 2^(fracwidth fmt) - 1"
    by (simp add: topfraction_def)
  hence "fraction a \<ge> 2^(fracwidth fmt)"
    by linarith 
  moreover have "fraction a < 2^(fracwidth fmt)"
    using is_valid_def valid by simp
  thus False
    using calculation not_le by blast
qed

lemma Val_zero:"Val Plus_zero = 0"
proof -
  have "(0,0,0) = Rep_float Plus_zero"
    using Abs_float_inverse Plus_zero_def is_valid_special(5) by fastforce
  moreover have "valof float_format (0,0,0) = 0" by simp
  ultimately show ?thesis 
    by (simp add: Val_def)
qed
  
  
subsection \<open>Properties about ordering and bounding\<close>
  
  (* Negative (finite) numbers are \<le> 0 *)
lemma negative_lt_zero:
  fixes x :: representation
  assumes finite:"is_valid fmt x"
    and negative:"sign x = 1"
  shows "valof fmt x \<le> valof fmt (plus_zero fmt) \<and> valof fmt x \<le> valof fmt (minus_zero fmt)"
proof -
  obtain s e f where sef:"(s, e, f) = x"
    by (metis fraction.cases)
  hence s1:"s = 1"
    by (metis negative sign.simps)
  hence "valof fmt (s, e, f) \<le> 0"
    using s1 by simp
  moreover have "valof fmt (plus_zero fmt) = 0 \<and> valof fmt (minus_zero fmt) = 0"
    by simp
  ultimately show ?thesis
    by (simp add: sef)
qed
  
lemma positive_next_larger_fraction:
  fixes fmt :: format
  shows "valof fmt (0, ye, yf) < valof fmt (0, ye, Suc yf)"
proof(cases "ye = 0")
  case ye0:True
  have l0:"valof fmt (0, ye, yf) = (2 / (2^bias fmt)) * (real yf/2^(fracwidth fmt))"
    using ye0 by simp
  have r0:"valof fmt (0, ye, Suc yf) = (2 / (2^bias fmt)) * (real (Suc yf)/2^(fracwidth fmt))"
    using ye0 by simp
  have "(real yf/2^(fracwidth fmt)) < (real (Suc yf)/2^(fracwidth fmt))"
    by (simp add: divide_strict_right_mono)
  hence "(2 / (2^bias fmt)) * (real yf/2^(fracwidth fmt)) < (2 / (2^bias fmt)) * (real (Suc yf)/2^(fracwidth fmt))"
    by (simp add: pos_less_divide_eq)
  hence "valof fmt (0, ye, yf) < valof fmt (0, ye, Suc yf)"
    using l0 r0 by linarith
  thus ?thesis by simp
next
  case False
  hence yegt0:"ye > 0"
    by auto
  moreover obtain exp :: real where exp:"exp = 2 ^ ye / 2 ^ bias fmt"
    by simp
  ultimately show ?thesis 
  proof(induction yf (* arbitrary: ye *))
    case 0
    have l0:"valof fmt (0, ye, 0) = exp"
      using "0.prems" by simp
    have r0:"valof fmt (0, ye, Suc 0) = 2 ^ ye / 2 ^ bias fmt * (1 + 1 / 2 ^ fracwidth fmt)"
      using "0.prems" by simp
    hence "1 / 2 ^ fracwidth fmt > (0 :: real)"
      by simp
    hence i0:"1 + 1 / 2 ^ fracwidth fmt > (1 :: real)"
      by simp
    hence "exp < (exp + exp * 1 / 2 ^ fracwidth fmt :: real)"
      by (simp add: exp)
    hence "exp < exp * (1 + 1 / 2 ^ fracwidth fmt :: real)"
      by (metis i0 add_pos_pos divide_less_eq_1_pos divide_pos_pos less_numeral_extra(1) exp
          mult_pos_pos nonzero_divide_mult_cancel_left r0 zero_less_numeral zero_less_power)
    hence "2 ^ ye / 2 ^ bias fmt < (2 ^ ye / 2 ^ bias fmt * (1 + 1 / 2 ^ fracwidth fmt) :: real)"
      using exp by blast
    then show ?case by simp
  next
    case (Suc yf)
    obtain plus1 :: real where plus1:"plus1 = (1 + (1 + real yf) / 2 ^ fracwidth fmt)"
      by simp
    obtain plus2 :: real where plus2:"plus2 = (1 + (2 + real yf) / 2 ^ fracwidth fmt)"
      by simp
    have l0:"valof fmt (0, ye, Suc yf) = exp * plus1"
      by (simp add: False exp plus1)
    have r0:"valof fmt (0, ye, Suc (Suc yf)) = exp * plus2"
      by (simp add: False exp plus2)
    have i0:"(1 + (1 + real yf) / 2 ^ fracwidth fmt) < (1 + (2 + real yf) / 2 ^ fracwidth fmt)"
      by (simp add: divide_strict_right_mono)
    have "plus1 < plus2"
      using i0 plus1 plus2 by simp
    hence "exp * plus1 < exp * plus2"
      by (metis divide_pos_pos exp zero_less_power
          linordered_comm_semiring_strict_class.comm_mult_strict_left_mono rel_simps(51))
    then show ?case 
      using l0 r0 by auto      
  qed
qed

lemma positive_larger_fraction_is_larger:
  fixes fmt :: format
    and fl :: nat
    and fs :: nat
  assumes lgts:"fl > fs" 
  shows "\<lbrakk>fl > fs\<rbrakk> 
      \<Longrightarrow> valof fmt (0, e, fl) > valof fmt (0, e, fs)"
proof(induction fl arbitrary: fs)
  case 0
  then show ?case by simp
next
  case (Suc fli)
  then show ?case
  proof(cases "fli > fs")
    case True
    hence "valof fmt (0, e, fs) < valof fmt (0, e, fli)"
      using Suc.IH Suc.prems by (simp add: True)
    moreover have "... < valof fmt (0, e, Suc fli)"
      using positive_next_larger_fraction Suc.prems by auto 
    ultimately show ?thesis 
      by linarith
  next
    case False
    hence "fli = fs"
      by (simp add: Suc.prems(1) less_antisym)
    then show ?thesis 
      using Suc.prems positive_next_larger_fraction by auto
  qed
qed
  
lemma positive_next_larger_exponent:
  fixes fmt :: format
  assumes valid0:"is_valid fmt (0, e, fa)"
    and valid1:"is_valid fmt (0, Suc e, fb)"
    (* \<lbrakk>is_valid fmt (0, e, f0); is_valid fmt (0, Suc e, f1)\<rbrakk> \<Longrightarrow> *)
  shows "valof fmt (0, e, fa) < valof fmt (0, Suc e, fb)" (is "?L < ?R")
proof(cases e)
  case 0
    
    (* obtain  *)
 (* apply_end simp *)
     (* 2 * real fa / (2 ^ bias fmt * 2 ^ fracwidth fmt) < (2 + 2 * real fb / 2 ^ fracwidth fmt) / 2 ^ bias fmt *)
  then show ?thesis 
    try
    sorry
next
  case (Suc nat)
  then show ?thesis sorry
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

(*     Note: `Finite x` is not necessary, I believe \<not>Isnan x is the minimal requirement.
    I think I'm using `Finite x` so that I can use `lemma float_le` *)
lemma SmallestPositiveDenorm:
  shows "\<nexists>x :: float. x < SmallPositiveDenorm \<and> x > Plus_zero \<and> Finite x"
proof(rule ccontr)
  assume "\<not>(\<nexists>x. x < SmallPositiveDenorm \<and> x > Plus_zero \<and> Finite x)"
  hence 0:"(\<exists>x. x < SmallPositiveDenorm \<and> x > Plus_zero  \<and> Finite x)" by auto
  then obtain y :: float where y:"y < SmallPositiveDenorm \<and> y > Plus_zero \<and> Finite y" by auto
  obtain ys ye yf where ysef:"(ys, ye, yf) = Rep_float y" 
    by (metis Abs_float_inverse finite_nan float_double_neg_eq float_neg_def fneg_def 
        is_valid_defloat mem_Collect_eq neg_valid y)
  hence fesy:"Sign y = ys \<and> Exponent y = ye \<and> Fraction y = yf"
    by (metis Exponent_def Fraction_def Sign_def exponent.simps fraction.simps sign.simps)
      
  have ypos:"Sign y = 0"
  proof(cases "Sign y = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have "Sign y < 2"
      using Sign_def is_valid_defloat is_valid by auto
    hence "Sign y = 0 \<or> Sign y = 1"
      by (simp add: less_2_cases)
    hence "Sign y = 1"
      by (simp add: False)
    hence "y \<le> Plus_zero"
      by (metis Abs_float_inverse Finite_def Plus_zero_def Sign_def Val_def float_le float_zero1 
          is_valid_defloat is_valid_special(5) mem_Collect_eq negative_lt_zero y)
    then show ?thesis 
      using Finite_def float_le_neg float_zero1 y by blast 
  qed
  hence ys0:"ys = 0"
    by (simp add: fesy)
    
  have "Val y > 0"
    using Finite_def Val_zero float_zero1 y by auto
      
      (*       We can't say
      Fraction y > 0
      because of the implicit leading 1 in the significand *)
      
  have "Exponent y = 0"
  proof(rule ccontr)
    assume "Exponent y \<noteq> 0"
    hence "Exponent y > 0" by simp
    hence yegt0:"ye > 0"
      by (simp add: fesy)
    obtain mul_exp :: real where mul_exp:"mul_exp = (1 / (2^bias float_format))" by simp    
    hence megt0:"mul_exp > 0" by simp 
    obtain part_frac :: real where part_frac:"part_frac = 1/2^(fracwidth float_format)" by simp    
    hence pfgt0:"part_frac > 0" by simp
        
    have i0:"valof float_format (0, ye, 0) = ((2^ye) / (2^bias float_format)) * 1"
      using yegt0 by auto
    have i1:"... = (2^ye) * mul_exp * 1"
      by (simp add: mul_exp part_frac)
        
    have i2:"valof float_format (0, 0, 1) = (2 / (2^bias float_format)) * (real 1/2^(fracwidth float_format))"
      by auto
    have i3:"... = 2 * mul_exp * part_frac"
      by (simp add: mul_exp part_frac)
        
    have i4:"(2^ye) * mul_exp * 1 > (2^ye) * mul_exp * part_frac"
      using megt0
    proof -
      have "1 > part_frac"
      proof -
        have "1 > (1/2^52 :: real)"
          by simp
        have "fracwidth float_format = 52"
          by (simp add: float_format_def)
        hence "1 > (1/2^(fracwidth float_format) :: real)"
          by simp
        thus ?thesis
          by (simp add: part_frac)
      qed
      thus ?thesis
        by (simp add: megt0)
    qed
      
    have i5:"(2^ye) * mul_exp * part_frac \<ge> 2 * mul_exp * part_frac"
      using yegt0 pfgt0 megt0 i4
    proof(induction ye)
      case 0
      then show ?case 
        by simp
    next
      case (Suc ye)
      then show ?case by simp
    qed
    hence "(2^ye) * mul_exp * 1 \<ge> 2 * mul_exp * part_frac"
      using i4 by linarith
        
    hence "valof float_format (0, ye, 0) > valof float_format (0, 0, 1)"
      using i0 i1 i2 i3 i4 i5 by linarith
    hence "valof float_format (0, ye, yf) > valof float_format (0, 0, 1)"
    proof(induction yf)
      case 0
      then show ?case by simp
    next
      case (Suc yf)
      have ii1:"valof float_format (0, 0, 1) < valof float_format (0, ye, yf)"
        using Suc.IH Suc.prems by auto
      have ii2:"valof float_format (0, ye, yf) < valof float_format (0, ye, Suc yf)"
        using positive_next_larger_fraction by blast
      then show ?case 
        using Suc.IH Suc.prems ii2 by linarith
    qed
    hence "valof float_format (ys, ye, yf) > valof float_format (0, 0, 1)"
      using ys0 by auto
    hence "y > SmallPositiveDenorm"
    proof -
      have "Isdenormal SmallPositiveDenorm"
        sledgehammer
        sorry
      have "Finite SmallPositiveDenorm"
        sledgehammer
        sorry
          
    qed
    using SmallPositiveDenorm_def ysef ypos ys0 float_lt
      sledgehammer
      sorry
      
(*       Now we have both:
      x < SmallPositiveDenorm
      valof float_format (0, 0, 1) < valof float_format (0, ye, yf)
      So we can show false *)
      
    then show False 
      sledgehammer
      sorry
  qed
    
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