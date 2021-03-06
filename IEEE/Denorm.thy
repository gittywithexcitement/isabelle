theory Denorm
  imports Main 
    "~~/src/HOL/Library/Code_Target_Nat"
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE"
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE_Properties"
begin

section \<open>Floating point stepping stones\<close>
  
subsection \<open>Special values (definitions)\<close>

definition topfraction :: "format \<Rightarrow> nat"
  where "topfraction x = 2^(fracwidth x) - 1"
    
text "1-\<epsilon> is the largest number that's < 1. Or it's the number after 1, towards -\<infinity>"
definition one_minus_eps :: "format \<Rightarrow> representation"
  where "one_minus_eps x = (0, bias x - 1, topfraction x)"
    
definition largest_positive_denorm :: "format \<Rightarrow> representation"
  where "largest_positive_denorm x = (0, 0, topfraction x)"

subsection \<open>Properties of fields\<close>
  
text "A few proofs require that exponent or fraction width is > 0"
definition smallest_format :: "format \<Rightarrow> bool"
  where "smallest_format fmt = (expwidth fmt \<ge> 1 \<and> fracwidth fmt \<ge> 1)"

text "one_minus_eps < 1 is true when exponent width \<ge> 2. Combine with fracwidth \<ge> 1"
definition reasonable_format :: "format \<Rightarrow> bool"
  where "reasonable_format fmt = (expwidth fmt \<ge> 2 \<and> fracwidth fmt \<ge> 1)"
    
lemma normalized_frac_lt2:
  assumes "is_normal fmt (s, e, f)"
    and "is_valid fmt (s, e, f)"
    and "smallest_format fmt"
  shows "1 + real f/2^fracwidth fmt < 2"
  using assms(2) is_valid_def by auto

subsection \<open>Properties about ordering and bounding\<close>
  
subsubsection \<open>Ordering between floating point values\<close>

text "For positive floats with same exponent, the greater (by one) fraction is also the greater value"
lemma pos_gt_suc_frac:
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

text "For positive floats with same exponent, the greater fraction is also the greater value"
lemma pos_gt_if_frac_gt:
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
      using pos_gt_suc_frac Suc.prems by auto 
    ultimately show ?thesis 
      by linarith
  next
    case False
    hence "fli = fs"
      by (simp add: Suc.prems(1) less_antisym)
    then show ?thesis 
      using Suc.prems pos_gt_suc_frac by auto
  qed
qed
  
text "For normalized values, when all else is equal, an exponent one greater means the value is twice as large"
lemma exponent_doubles:
  shows "\<lbrakk>is_valid fmt (s, e, f); is_normal fmt (s, e, f); 
          is_valid fmt (s, Suc e, f); is_normal fmt (s, Suc e, f)\<rbrakk>  
      \<Longrightarrow> valof fmt (s, e, f) * 2 = valof fmt (s, Suc e, f)"
proof(induction e)
  case 0
  then show ?case 
     by (simp add: is_normal_def)
next
  case (Suc e)
  show ?case     
    by simp 
qed  
  
text "For positive floats, the greater (by one) exponent is the greater value, regardless of fraction"
lemma pos_gt_suc_exp:
  fixes fmt :: format
  shows "\<lbrakk>is_finite fmt (0, e, fa); is_finite fmt (0, Suc e, fb)\<rbrakk> 
      \<Longrightarrow> valof fmt (0, e, fa) < valof fmt (0, Suc e, fb)"
proof(induction e)
  case 0
  let ?L = "valof fmt (0, 0, fa)"
  let ?R = "valof fmt (0, Suc 0, fb)"
  obtain exp :: real where exp:"exp = 2 / (2^bias fmt)"
    by simp
  have "?L = (2 / (2^bias fmt)) * (real fa/2^(fracwidth fmt))"
    using 0 by simp
  hence l1:"?L = exp * (real fa/2^(fracwidth fmt))"
    using exp by simp
  have "?R = (2 / (2^bias fmt)) * (1 + real fb/2^(fracwidth fmt))"
    using 0 by simp
  hence r1:"?R = exp * (1 + real fb/2^(fracwidth fmt))"
    using exp by simp
  have lt0:"real fa/2^(fracwidth fmt) < 1 + real fb/2^(fracwidth fmt)"
  proof -
    have "real 2^(fracwidth fmt) > 0"
      by simp
    hence "real fa /  2^(fracwidth fmt) < 1"
      by (metis "0"(1) divide_less_eq_1_pos finite_valid fraction.simps is_valid_def 
          numeral_2_eq_2 of_nat_numeral real_of_nat_less_numeral_power_cancel_iff)
    moreover have "real fb/2^(fracwidth fmt) \<ge> 0"
      by simp
    ultimately show ?thesis
       by linarith
  qed
  hence "exp * (real fa/2^(fracwidth fmt)) < exp * (1 + real fb/2^(fracwidth fmt))"
  proof -
    have "exp > 0"
      using exp by force
    thus ?thesis
      using linordered_comm_semiring_strict_class.comm_mult_strict_left_mono lt0 by blast
  qed
  then show ?case
    using l1 r1 by linarith
next
  case sucout:(Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v)
  let ?L = "valof fmt (0, Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)"
  let ?R = "valof fmt (0, Suc (Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v), fb)"
  have "is_finite fmt (0, e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)"
    using fraction.simps is_denormal_def is_finite_def is_normal_def is_valid_def is_zero_def sucout.prems(1) by auto
  hence prem_gt:"valof fmt (0, e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa) < valof fmt (0, Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fb)" (is "?Lp < ?Rp")
    using is_denormal_def is_finite_def is_normal_def is_valid_def is_zero_def sucout.IH sucout.prems(2) by auto
  then show ?case
  proof(cases "e\<^sub>p\<^sub>r\<^sub>e\<^sub>v")
    case 0
    hence s1:"Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v = 1"
      by simp
    hence ss2:"Suc (Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v) = 2"
      by simp
    have l0:"?L = (2 / (2^bias fmt)) * (1 + real fa/2^fracwidth fmt)"
      by (simp add: s1)
    have r0:"?R = (4 / (2^bias fmt)) * (1 + real fb/2^fracwidth fmt)"
      by (simp add: ss2)
    obtain exp :: real where exp:"exp = (2 / (2^bias fmt))"
      by simp
    hence l1:"?L = exp * (1 + real fa/2^fracwidth fmt)"
      using l0 by blast
    have r1:"?R = 2 * exp * (1 + real fb/2^fracwidth fmt)"
      using exp r0 by auto
    have "1 + real fa/2^fracwidth fmt < 2"
    proof -
      have "is_normal fmt (0, Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)"
        using is_denormal_def is_finite_def is_zero_def sucout.prems(1) by auto
      moreover have "is_valid fmt (0, Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)"
        by (simp add: finite_valid sucout.prems(1))
      ultimately show ?thesis
        using normalized_frac_lt2 by (simp add: is_valid_def)
    qed
    moreover have "exp > 0"
      by (simp add: exp)
    ultimately have lt0:"exp * (1 + real fa/2^fracwidth fmt) < 2 * exp"
      by auto
    hence "exp * (1 + real fa/2^fracwidth fmt) < 2 * exp * (1 + real fb/2^fracwidth fmt)"
    proof -
      have "real fb/2^fracwidth fmt \<ge> 0"
        by simp
      hence "2 * exp * (1 + real fb/2^fracwidth fmt) \<ge> 2 * exp"
        by (simp add: \<open>0 < exp\<close>)
      thus ?thesis 
        using lt0 by linarith
    qed
    then show ?thesis 
      using l1 r1 by linarith
  next
    case sucin:(Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v\<^sub>g\<^sub>t\<^sub>0)
    have vs:"is_valid fmt (0, Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)"
      by (simp add: finite_valid sucout.prems(1))
    have ns:"is_normal fmt (0, Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)"
      using is_denormal_def is_finite_def is_zero_def sucout.prems(1) by auto
    have "?Lp * 2 = ?L"
    proof -
      have "is_valid fmt (0, e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)"
        by (simp add: \<open>is_finite fmt (0, e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)\<close> finite_valid)
      moreover have "is_normal fmt (0, e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)"
        using is_normal_def sucin \<open>is_finite fmt (0, e\<^sub>p\<^sub>r\<^sub>e\<^sub>v, fa)\<close> is_denormal_def is_finite_def 
          is_zero_def by auto
      ultimately show ?thesis
        using exponent_doubles vs ns by blast
    qed 
    moreover have "?Rp * 2 = ?R"
    proof -
      have "is_valid fmt (0, Suc (Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v), fa)"
        by (metis exponent.simps finite_valid fraction.simps is_valid_def prod.sel(1) sign sucout.prems(2) vs)
      moreover have "is_normal fmt (0, Suc (Suc e\<^sub>p\<^sub>r\<^sub>e\<^sub>v), fa)"
        using is_normal_def sucin is_denormal_def is_finite_def is_zero_def sucout.prems(2) by auto
      ultimately show ?thesis
        using exponent_doubles vs ns by force
    qed         
    ultimately show ?thesis 
      using prem_gt by linarith
  qed
qed

text "For positive floats, the greater exponent is the greater value, regardless of fraction"
lemma pos_gt_if_exp_gt:
  assumes lgts:"el > es" 
  shows "\<lbrakk>el > es; is_finite fmt (0, el, fa); is_finite fmt (0, es, fb)\<rbrakk> 
      \<Longrightarrow> valof fmt (0, el, fa) > valof fmt (0, es, fb)"
proof(induction el arbitrary: es)
  case 0
  then show ?case by simp
next
  case (Suc eli)
  then show ?case
  proof(cases "eli > es")
    case True
    have fineli:"is_finite fmt (0, eli, fa)"
      using Suc.prems(2) is_denormal_def is_finite_def is_normal_def is_valid_def is_zero_def by auto
    moreover have "is_finite fmt (0, es, fb)"
      by (simp add: Suc.prems(3))
    ultimately have "valof fmt (0, es, fb) < valof fmt (0, eli, fa)"
      using Suc.IH True by blast
    moreover have "... < valof fmt (0, Suc eli, fa)"
      using pos_gt_suc_exp Suc.prems(2) fineli by blast
    ultimately show ?thesis 
      by linarith
  next
    case False
    hence "eli = es"
      by (simp add: Suc.prems(1) less_antisym)
    then show ?thesis 
      using Suc.prems pos_gt_suc_frac pos_gt_suc_exp by blast
  qed
qed
  
subsubsection \<open>Relation to zero\<close>

text "If the value is greater than 0, then sign is 0"
lemma sign0_if_gt_zero:
  fixes e :: nat
  assumes xgt0:"valof fmt (s,e,f) > 0"
    and valid:"is_valid fmt (s,e,f)"
  shows "sign (s,e,f) = 0 \<and> s = 0"
proof(cases e)
  case 0
  obtain fe ::real where fe:"2 / (2^bias fmt) = fe"
    by simp
  obtain fp ::real where fp:"real f/2^(fracwidth fmt) = fp"
    by simp
  have 1:"valof fmt (s,e,f) = (-1::real)^s * fe * fp"
    by (simp add: "0" fe fp)
  hence "... > 0"
    using xgt0 by linarith
  moreover have "fe > 0"
    using fe by auto
  moreover have "fp > 0"
    using fp
    by (metis calculation(1) divide_less_0_iff linorder_neqE_linordered_idom mult.commute 
        mult_zero_left not_numeral_less_zero of_nat_less_0_iff power_less_zero_eq)
  ultimately have "(-1::real)^s > 0"
    using zero_less_mult_pos2 by blast
  moreover have "s = 0 \<or> s = 1"
    using is_valid_def valid by auto
  then show ?thesis
    using calculation by auto
next
  case (Suc nat)
  obtain fe ::real where fe:"((2^e) / (2^bias fmt)) = fe"
    by simp
  obtain fp ::real where fp:"1 + real f/2^fracwidth fmt = fp"
    by simp
  have 1:"valof fmt (s,e,f) = (-1::real)^s * fe * fp"
    using Suc fe fp by auto
  hence "... > 0"
    using xgt0 by linarith
  moreover have "fe > 0"
    using fe by auto
  moreover have "fp > 0"
    using fp
    by (metis add_less_same_cancel1 add_pos_pos divide_less_0_iff less_add_same_cancel1 
        less_numeral_extra(1) linorder_neqE_linordered_idom not_numeral_less_zero 
        of_nat_less_0_iff power_less_zero_eq)
  ultimately have "(-1::real)^s > 0"
    using zero_less_mult_pos2 by blast
  moreover have "s = 0 \<or> s = 1"
    using is_valid_def valid by auto
  then show ?thesis
    using calculation by auto
qed

text "The value of negative numbers is \<le> 0"
lemma negative_lt_zero:
  fixes x :: representation
  assumes negative:"sign x = 1"
  shows "valof fmt x \<le> 0"
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
  
text "Positive numbers with a nonzero exponent or fraction are > 0"
lemma positive_gt_zero:
  assumes val:"is_valid fmt (s, e, f)"
    and s0:"s = 0"
    and e_or_f_gt0:"e > 0 \<or> f > 0"
  shows "valof fmt (s, e, f) > valof fmt (plus_zero fmt) \<and> valof fmt (s, e, f) > valof fmt (minus_zero fmt)"
proof -
  show ?thesis
  proof(cases "e = 0")
    case e0:True
    hence fgt0:"f > 0"
      using e_or_f_gt0 by fastforce
    then show ?thesis
    proof(induction f)
      case 0
      then show ?case by blast
    next
      case (Suc f)
      then show ?case
      proof(cases "f = 0")
        case True
        then show ?thesis by (simp add: e0 s0) 
      next
        case False
        then show ?thesis using add_divide_distrib e0 s0 by fastforce
      qed
    qed
  next
    case False
    hence egt0:"e > 0"
      by auto
    then show ?thesis
    proof(induction f)
      case 0
      then show ?case
        by (simp add: s0)
    next
      case (Suc f)
      hence 1:"valof fmt (plus_zero fmt) < valof fmt (s, e, f) \<and> valof fmt (minus_zero fmt) < valof fmt (s, e, f)"
        by blast
      hence "valof fmt (plus_zero fmt) < valof fmt (s, e, Suc f)"
        using less_eq_real_def less_le_trans pos_gt_suc_frac s0 by blast 
      moreover have "valof fmt (minus_zero fmt) < valof fmt (s, e, Suc f)"
        using less_eq_real_def less_le_trans pos_gt_suc_frac s0 1 by blast
      ultimately show ?case
        by blast
    qed
  qed
qed

subsection \<open>Properties of Special values\<close>
text "This section appears down here because it uses some of the proofs above."
  
text "topfraction is the largest possible (valid) fraction"
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
  
text "(for valof) topfraction divided by 2^(fracwidth fmt) < 1"
lemma topfraction_over_divisor_lt_one:
  "topfraction fmt/(2^fracwidth fmt) < real 1"
  using topfraction_def by auto
    
lemma largest_positive_denorm_gt0:
  assumes rsnbl:"smallest_format fmt"
  shows "valof fmt (largest_positive_denorm fmt) > 0"
  using rsnbl largest_positive_denorm_def apply(simp)
  by (metis One_nat_def Suc_le_lessD divide_pos_pos mult_pos_pos of_nat_0_less_iff 
      one_less_numeral_iff one_less_power smallest_format_def semiring_norm(76) topfraction_def 
      zero_less_diff zero_less_numeral zero_less_power)
    
text "largest positive denorm is as the name describes"
lemma largest_positive_denorm:
  assumes validlpd:"is_valid fmt (largest_positive_denorm fmt)"
    and rsnbl:"smallest_format fmt"
  assumes validx:"is_valid fmt x"
    and denormx:"is_denormal fmt x"
  shows "valof fmt x \<le> valof fmt (largest_positive_denorm fmt)"
proof (rule ccontr)
  assume "\<not> (valof fmt x \<le> valof fmt (largest_positive_denorm fmt))"
  hence assm:"valof fmt x > valof fmt (largest_positive_denorm fmt)"
    by simp
  obtain s e f where sef:"(s,e,f) = x"
    by (metis fraction.cases)
  obtain sl el fl where sefl:"(sl,el,fl) = largest_positive_denorm fmt"
    by (metis fraction.cases)
  thus False
  proof(cases "s = 0")
    case seq0:True
    then show ?thesis
    proof(cases "e > el")
      case True
        \<comment> \<open>Show it can't be denormal because exponent is too big\<close>
      hence "\<not>is_denormal fmt x"
        using is_denormal_def sef by auto
      then show ?thesis
        using denormx by auto
    next
      case expneq:False
      then show ?thesis 
      proof(cases "e = el")
        case expeq:True \<comment> \<open>signs and exponents are equal\<close>
        then show ?thesis 
        proof(cases "f > fl")
          case True
            \<comment> \<open>Show it can't be valid because fraction is too big\<close>
          hence "\<not>is_valid fmt x"
            by (metis fraction.simps largest_positive_denorm_def not_less sef sefl 
                topfraction_largest validx)
          then show ?thesis
            using validx by auto
        next
          case False
          then show ?thesis 
          proof(cases "f = fl")
            case True
              \<comment> \<open>same value as lpd, thus violates assumption\<close>
            hence "(s,e,f) = (sl,el,fl)"
              using expeq largest_positive_denorm_def sefl seq0 by auto
            then show ?thesis
              using assm sef sefl by auto
          next
            case False
            hence "f < fl"
              by (metis fraction.simps largest_positive_denorm_def le_neq_implies_less sef sefl 
                  topfraction_largest validx)
                \<comment> \<open>smaller than lpd, thus violates assumption\<close>
            hence "valof fmt (s,e,f) < valof fmt (sl,el,fl)"
              by (metis expeq largest_positive_denorm_def pos_gt_if_frac_gt prod.sel(1) sefl seq0)
            then show ?thesis
              using assm sef sefl by auto
          qed
        qed
      next
        case False
        hence "e < el"  \<comment> \<open>Show that lpd > x, violating assumption\<close>
          using expneq by auto
        hence "valof fmt (s,e,f) < valof fmt (sl,el,fl)"
          using largest_positive_denorm_def sefl by auto
        then show ?thesis
          using assm sef sefl by auto
      qed
    qed      
  next
    case False
    hence "s = 1" \<comment> \<open>x < lpd, violating assumption\<close>
      using sef sign_0_1 validx by fastforce
    hence "valof fmt x \<le> 0"
      using negative_lt_zero sef sign.simps by blast
    moreover have "0 < valof fmt (largest_positive_denorm fmt)"
      using largest_positive_denorm_gt0 rsnbl by simp
    ultimately show ?thesis
      using assm by auto
  qed
qed
  
text "one_minus_eps is valid"
lemma valid_one_minus_eps:"is_valid fmt (one_minus_eps fmt)"
proof -
  have "sign (one_minus_eps fmt) = 0"
    by (simp add: one_minus_eps_def)
  moreover have "fraction (one_minus_eps fmt) = 2^(fracwidth fmt) - 1"
    by (simp add: one_minus_eps_def topfraction_def)  
  moreover have "exponent (one_minus_eps fmt) < 2^(expwidth fmt)"
  proof -
    have "exponent (one_minus_eps fmt) = bias fmt - 1"
      by (simp add: one_minus_eps_def)
    thus ?thesis
      by (metis bias_def diff_less less_imp_diff_less less_numeral_extra(1) neq0_conv 
          one_less_numeral_iff power_0 power_strict_increasing_iff semiring_norm(76) zero_diff)
  qed
  ultimately show ?thesis
    by (simp add: is_valid)
qed
  
text "one_minus_eps is greater than 0 for a reasonable float format"
lemma eps_gt_zero:
  assumes rsnbl:"smallest_format fmt"
  shows "valof fmt (one_minus_eps fmt) > 0"
proof -
  obtain s e f where sef:"(s,e,f) = one_minus_eps fmt"
    by (simp add: one_minus_eps_def)
  hence fgt0:"f > 0"
  proof -
    have "fracwidth fmt \<ge> 1"
      using smallest_format_def rsnbl by auto
    hence "real 2^(fracwidth fmt) - 1 \<ge> 1"
      using exp_less by fastforce
    hence "topfraction fmt > real 0"
      by (simp add: of_nat_diff topfraction_def)
    thus ?thesis
      using sef one_minus_eps_def by auto
  qed
  moreover have s0:"s = 0"
    using one_minus_eps_def sef by auto
  then show ?thesis
    using positive_gt_zero s0
    by (metis divide_eq_0_iff exponent.simps fgt0 fraction.simps mult_cancel_right2 of_nat_0 
        plus_zero_def sef valid_one_minus_eps valof_eq)
qed
  
text "one_minus_eps is finite"
lemma finite_eps:
  shows "is_finite fmt (one_minus_eps fmt)"
proof -
  have 0:"one_minus_eps fmt = (0, bias fmt - 1, topfraction fmt)"
    by (simp add: one_minus_eps_def)
  have valid:"is_valid fmt (0, bias fmt - 1, topfraction fmt)"
    by (metis 0 valid_one_minus_eps)
  show ?thesis 
  proof(cases "bias fmt - 1 = 0")
    case True
    have "is_denormal fmt (0, bias fmt - 1, topfraction fmt) \<or> is_zero fmt (0, bias fmt - 1, topfraction fmt)"
      using True is_denormal_def is_zero_def by auto
    then show ?thesis
      using "0" is_finite_def valid by auto
  next
    case False
    hence egt0:"bias fmt - 1 > 0"
      by simp
    hence "bias fmt - 1 < emax fmt"
      by (metis (no_types, lifting) Suc_diff_1 bias_def diff_less_Suc emax_def exponent.simps 
          is_valid_def less_antisym not_less_eq one_less_numeral_iff pos2 power_less_power_Suc 
          realpow_num_eq_if semiring_norm(76) valid zero_less_diff zero_less_power)
    hence "is_normal fmt (0, bias fmt - 1, topfraction fmt)"
      using egt0 is_normal_def by auto
    then show ?thesis
      by (metis "0" is_finite_def valid_one_minus_eps)
  qed
qed

text "one_minus_eps is the largest value that's less than 1"
lemma one_minus_eps_largest:
  assumes valid:"is_valid fmt a"
  and "valof fmt a < 1"
  and rsnbl:"smallest_format fmt"
shows "valof fmt a \<le> valof fmt (one_minus_eps fmt)"
proof(rule ccontr)
  assume asm0:"\<not> valof fmt a \<le> valof fmt (one_minus_eps fmt)"
  hence asm1:"valof fmt a > valof fmt (one_minus_eps fmt)"
    by simp
  obtain sa ea fa where asef:"(sa,ea,fa) = a"
    by (metis fraction.cases) 
  obtain se ee fe where esef:"(se,ee,fe) = one_minus_eps fmt"
    by (metis fraction.cases)
  hence se0:"se = 0"
    using one_minus_eps_def by auto
  show False 
  proof(cases "sa = 0")
    case sa0:True
    then show ?thesis 
    proof(cases "ea = ee")
      case expeq:True
      then show ?thesis 
      proof(cases "fa = fe")
        case fraceq:True
        then show ?thesis
          using asef asm1 esef expeq sa0 se0 by auto
      next
        case False
        then show ?thesis 
        proof(cases "fa > fe")
          case True
          then show ?thesis
            by (metis asef esef fraction.simps not_less one_minus_eps_def topfraction_largest valid)
        next
          case False
          then show ?thesis
            using pos_gt_if_frac_gt
            by (metis asef asm1 esef expeq not_less_iff_gr_or_eq sa0 se0)
        qed
      qed
    next
      case expneq:False
      then show ?thesis 
      proof(cases "ea > ee")
        case egt:True
        have "ee = bias fmt - 1"
          using esef one_minus_eps_def by auto
        hence "ea \<ge> bias fmt"
          using egt by linarith
        hence "((2^ea) / (2^bias fmt)) \<ge> real 1" (is "?Exp \<ge> real 1")
          by simp
        then obtain exp :: real where exp:"exp = ?Exp \<and> exp \<ge> 1"
          by fastforce
        have "(1 + real fa/2^fracwidth fmt) \<ge> 1" (is "?Frac \<ge> 1")
          by simp
        then obtain frac :: real where frac:"frac = ?Frac \<and> frac \<ge> 1"
          by fastforce
        have "exp * frac \<ge> 1"
          by (metis exp frac le_less_trans le_numeral_extra(1) less_eq_real_def mult.left_neutral 
              mult_cancel_left1 not_less real_mult_le_cancel_iff1) 
        moreover have "ea > 0"
          using egt by auto
        moreover have "valof fmt (sa,ea,fa) = ((2^ea) / (2^bias fmt)) * (1 + real fa/2^fracwidth fmt)"
          using calculation(2) sa0 by auto
        ultimately have "valof fmt (sa,ea,fa) > 1"
          using exp frac asef assms(2) by auto
        then show ?thesis
          using asef assms(2) by auto
      next
        case False
        hence elt:"ea < ee"
          using expneq antisym_conv3 by blast
        moreover have "is_finite fmt (se, ee, fe)"
          using esef finite_eps rsnbl by auto
        moreover have "is_finite fmt (sa, ea, fa)"
          using elt asef calculation(2) is_denormal_def is_finite_def is_normal_def is_zero_def valid by auto
        hence "valof fmt (sa,ea,fa) < valof fmt (se,ee,fe)"
          using pos_gt_if_exp_gt calculation(2) elt sa0 se0 by blast
        then show ?thesis
          using asef asm0 esef by auto
      qed
    qed
  next
    case False
    hence "sa = 1"
      using asef is_valid_def valid by auto 
    hence "valof fmt (sa,ea,fa) \<le> 0"
      using negative_lt_zero
      by (simp add: negative_lt_zero)
    then show ?thesis 
      using eps_gt_zero asef asm1 rsnbl by fastforce
  qed
qed
  
text "one_minus_eps < 1 when exponent width \<ge> 2"
lemma one_minus_eps_lt_one:
  shows "ew \<ge> 2 
      \<Longrightarrow> valof (ew, fw) (one_minus_eps (ew, fw)) < 1"
proof(induction ew)
  case 0
  then show ?case
    by simp
next
  case (Suc ew)
  then show ?case 
  proof(cases "ew < 2")
    case True \<comment> \<open>can't use IH\<close>
    hence "Suc ew = 2"
      using Suc.prems by auto
    moreover have "valof (2, fw) (one_minus_eps (2, fw)) < 1" (is "?V2 < 1")
    proof -
      have "?V2 = valof (2, fw) (0, 0, 2^fw - 1)"
        using one_minus_eps_def by (simp add: bias_def topfraction_def) 
      also have "... = real (2^fw - 1)/2^(fw)"        
        by (simp add: bias_def)
      then show ?thesis
        by (simp add: calculation)
    qed
    then show ?thesis
      by (simp add: calculation)
  next
    case False  \<comment> \<open>can use IH\<close>
    hence ewgte2:"ew \<ge> 2"
      by simp
    hence "valof (ew, fw) (one_minus_eps (ew, fw)) < 1" (is "?v < 1")
      by (simp add: Suc.IH)
    have "bias (ew, fw) \<ge> 1"
      by (metis False One_nat_def Suc_1 Suc_leI bias_def expwidth.simps not_less_eq 
          one_less_numeral_iff one_less_power semiring_norm(76) zero_less_diff)
    then obtain bew where bew:"bew = bias (ew, fw) \<and> bew \<ge> 1"
      by simp 
    let ?vs = "valof (Suc ew, fw) (one_minus_eps (Suc ew, fw))"
    show ?thesis 
    proof(cases "ew = 2")
      case True
      hence se3:"Suc ew = 3"
        by simp
      hence "bias (3, fw) = 2^(3 - 1) - 1"
        by (simp add: bias_def)
      also have "... = 3"
        by simp
      hence "valof (Suc ew, fw) (one_minus_eps (Suc ew, fw)) = (1/2) * (1 + real (2^fw - 1)/2^fw)"
        by (simp add: se3 calculation one_minus_eps_def topfraction_def)
      then show ?thesis
        by (simp add: \<open>valof (Suc ew, fw) (one_minus_eps (Suc ew, fw)) = 1 / 2 * (1 + real (2 ^ fw - 1) / 2 ^ fw)\<close>)
    next
      case False
      hence "ew > 2"
        by (simp add: ewgte2 le_neq_implies_less)
      hence "Suc ew > 3"
        by simp
      have "2^((Suc ew) - 1) \<ge> real 4"
        using ewgte2 exp_less mult_2 by fastforce
      hence "bias (Suc ew, fw) \<ge> real 3"
        by (simp add: bias_def of_nat_diff)
      then obtain bsew :: nat where bsew:"bsew = bias (Suc ew, fw) \<and> bsew \<ge> 3"
        by simp
      hence "(2 :: nat)^(bsew - 1) * 2 = 2^bsew"
        by (simp add: realpow_num_eq_if) 
      hence "(2 :: nat)^(bsew - 1) * 2 / (2^bsew :: real) = 1"
        by simp
      hence exp_half:"(2 :: nat)^(bsew - 1) / (2^bsew :: real) = 1 / 2"
        by fastforce 
      have frac_lt2:"(1 + real (2^fw - 1)/2^fw) < 2"
        by simp
      let ?valof = "valof (Suc ew, fw) (one_minus_eps (Suc ew, fw))"
      have "?valof = (2 :: nat)^(bsew - 1) / (2^bsew :: real) * (1 + real (2^fw - 1)/2^fw)"
        using bsew one_minus_eps_def topfraction_def by auto
      also have "... = (1/2) * (1 + real (2^fw - 1)/2^fw)"
        using exp_half by simp
      finally show ?thesis
        using frac_lt2
        by (metis divide_less_eq_numeral1(1) mult_cancel_right2 times_divide_eq_left)
    qed
  qed
qed
  
subsection \<open>Multiply specific values\<close>
  
(*New plan:
  Show that all denorms are < norms
Show that rounding can't increase the value above the original value.
Then denorm * (x<1) must be denorm? ... maybe...

What about showing that there are at most 2 floats that can be rounded to?
 One \<ge> product and one \<le> product
 And the since product is < lpd...
 *)  
  
(* Plan:
For the smallest 'reasonable' float format, prove that (1-\<epsilon>)*largest_denorm, after rounding, is
largest_denorm, or second largest denorm. Attempt to use induction to prove the same fact for all
other formats. *)
lemma fmul_reasonable_format:
  assumes fmt:"fmt = (2, 1)" (* expwidth fmt = 2 \<and> fracwidth fmt = 1 *)
  shows "is_denormal fmt (fmul fmt float_To_zero (one_minus_eps fmt) (largest_positive_denorm fmt))"
proof -
  have "valof fmt (largest_positive_denorm fmt) = 1 / 2" (is "?vlpd = 1/2")
  proof -
    have "valof fmt (largest_positive_denorm fmt) = valof fmt (0, 0, topfraction fmt)"
      by (simp add: largest_positive_denorm_def)
    also have "... = valof fmt (0, 0, 1)"
      by (simp add: fmt topfraction_def)
    finally show ?thesis
      by (simp add: fmt bias_def)
  qed
  have "valof fmt (one_minus_eps fmt) = 1 / 2" (is "?vome = 1/2")
  proof -
    have "valof fmt (one_minus_eps fmt) = valof fmt (0, bias fmt - 1, topfraction fmt)"
      by (simp add: one_minus_eps_def)
    also have "... = valof fmt (0, 0, 1)"
      by (simp add: fmt bias_def topfraction_def)
    finally show ?thesis
      by (simp add: fmt bias_def)
  qed
    
  hence "?vlpd * ?vome = 1/4"
    by (simp add: \<open>valof fmt (largest_positive_denorm fmt) = 1 / 2\<close>)
      
  let ?y = "1/4 :: real"
    
    (* There are 4 exponents and 2 fractions that the result can round to *)
  have rep000:"valof fmt (0, 0, 0) = 0"
    by (simp add: fmt bias_def) 

  have rep001:"valof fmt (0, 0, 1) = 1 / 2"
    by (simp add: fmt bias_def) 

  have "valof fmt (0, 1, 0) = 1"
    by (simp add: fmt bias_def) 
      
      (* Also need to prove that 1/4 not < -largest fmt, nor > largest fmt *)
  have "is_closest (valof fmt) {a. is_finite fmt a \<and> \<bar>valof fmt a\<bar> \<le> \<bar>?y\<bar>} ?y (0, 0, 0)"
  proof -
    have "\<bar>valof fmt (0, 0, 0)\<bar> \<le> \<bar>?y\<bar>"
      by simp
    moreover have "is_finite fmt (0,0,0)"
      using is_finite_def is_valid_special(5) is_zero_def by simp
    moreover have "\<bar>valof fmt (0, 0, 1)\<bar> > \<bar>?y\<bar>"
      using rep001 by force

    ultimately show ?thesis
        sorry
  qed
    (*   have "round fmt float_To_zero (1/4) = (0,0,1)"
    quickcheck[random] nitpick
      sledgehammer
      sorry *)
    
  show ?thesis sorry
qed


subsection \<open>Properties of multiplication\<close>
  
text "(1-\<epsilon>) * largest_positive_denorm is denormal"
lemma lpd_mul_ome_is_denorm:
  assumes exp_ge2:"expwidth fmt \<ge> 2"
    and rsnbl:"smallest_format fmt"
  shows "is_denormal fmt (fmul fmt float_To_zero (one_minus_eps fmt) (largest_positive_denorm fmt))"
proof -
  have "valof fmt (one_minus_eps fmt) < 1"
    using one_minus_eps_lt_one by (metis expwidth.elims exp_ge2) 
  moreover have "valof fmt (largest_positive_denorm fmt) > 0"
    by (simp add: largest_positive_denorm_gt0 rsnbl)
  ultimately have "valof fmt (one_minus_eps fmt) * valof fmt (largest_positive_denorm fmt) \<le> valof fmt (largest_positive_denorm fmt)"
    by force
  hence "valof fmt (fmul fmt float_To_zero (one_minus_eps fmt) (largest_positive_denorm fmt)) \<le> valof fmt (largest_positive_denorm fmt)"
    (* Paused. Need to prove helper lemma(s)  *)
      sorry
  show ?thesis sorry
qed

  (* What about To_nearest? 
TODO use magnitudes instead of insisting that everything is positive*)
lemma mult_lt_1_smaller:  
  assumes vndx:"is_valid fmt x \<and> (is_normal fmt x \<or> is_denormal fmt x)"
    and vndy:"is_valid fmt y \<and> (is_normal fmt y \<or> is_denormal fmt y)"
    and ylt1:"valof fmt y > 0 \<and> valof fmt y < 1"
    and xgt0:"valof fmt x > 0"
  shows "valof fmt (fmul fmt float_To_zero x y) < valof fmt x"
proof(cases "is_normal fmt x")
  case True
  obtain s e f where sef:"(s,e,f) = x"
    by (metis fraction.cases)
  have "sign x = 0"
    using sign0_if_gt_zero by (metis sef vndx xgt0)
  have "e \<ge> 1"
    using True is_normal_def sef by auto
      (* Let's get the largest possible value of x
    And the largest possible value of y
    Multiply them and check if result < x
    Then do a proof by contradiction *)
  then show ?thesis
      sorry
next
  case False
  hence "is_denormal fmt x"
    using vndx by auto
  then show ?thesis sorry
qed
  
section \<open>Polynomial evaluation\<close>
  
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
  
value "is_zero float_format (Rep_float a)"  
value "is_zero float_format (0,0,0)"  
  