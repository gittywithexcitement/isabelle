theory Denorm
  imports Main 
    "~~/src/HOL/Library/Code_Target_Nat"
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE"
    "~~/dled_components/afp/thys/IEEE_Floating_Point/IEEE_Properties"
begin

section \<open>Helpers\<close>
  
subsection \<open>Special values\<close>

definition topfraction :: "format \<Rightarrow> nat"
  where "topfraction x = 2^(fracwidth x) - 1"
    
definition one_minus_eps :: "format \<Rightarrow> representation"
  where "one_minus_eps x = (0, bias x - 1, topfraction x)"
      
lemma Val_zero:"Val Plus_zero = 0"
proof -
  have "(0,0,0) = Rep_float Plus_zero"
    using Abs_float_inverse Plus_zero_def is_valid_special(5) by fastforce
  moreover have "valof float_format (0,0,0) = 0" by simp
  ultimately show ?thesis 
    by (simp add: Val_def)
qed
  
subsection \<open>Properties of fields\<close>
  
definition reasonable_format :: "format \<Rightarrow> bool"
  where "reasonable_format fmt = (expwidth fmt \<ge> 1 \<and> fracwidth fmt \<ge> 1)"
    
lemma normalized_frac_lt2:
  assumes "is_normal fmt (s, e, f)"
    and "is_valid fmt (s, e, f)"
    and "reasonable_format fmt"
  shows "1 + real f/2^fracwidth fmt < 2"
  using assms(2) is_valid_def by auto

subsection \<open>Properties about ordering and bounding\<close>
  
subsubsection \<open>Ordering between floating point values\<close>

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

text "Negative numbers are \<le> 0"
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
  
text "Positive numbers are > 0"
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
  
lemma eps_gt_zero:
  assumes rsnbl:"reasonable_format fmt"
  shows "valof fmt (one_minus_eps fmt) > 0"
proof -
  obtain s e f where sef:"(s,e,f) = one_minus_eps fmt"
    by (simp add: one_minus_eps_def)
  hence fgt0:"f > 0"
  proof -
    have "fracwidth fmt \<ge> 1"
      using reasonable_format_def rsnbl by auto
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
    
lemma one_minus_eps_largest:
  assumes valid:"is_valid fmt a"
  and "valof fmt a < 1"
  and rsnbl:"reasonable_format fmt"
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
        case True
        have "ee = bias fmt - 1"
          using esef one_minus_eps_def by auto
        hence "ea \<ge> bias fmt"
          using True by linarith
        hence "valof fmt (sa,ea,fa) > 1"
          (* TODO here *)
          (* sledgehammer quickcheck *)
            sorry
(*         have "valof fmt (sa,ea,fa) > valof fmt (se,ee,fe)" (is "?L > ?R")
          using asef asm0 esef by auto *)
            (* hence "?L > " *)
        then show ?thesis 
          sorry
      next
        case False
        hence "ea < ee"
          using expneq antisym_conv3 by blast
            (* TODO is_finite proof for 1-epsilon *)
        moreover have "is_finite fmt (sa, ea, fa)"
          by (metis (mono_tags, lifting) False One_nat_def Suc_1 Suc_diff_Suc asef emax_def esef 
              expneq exponent.simps is_denormal_def is_finite_def is_normal_def is_valid_def 
              is_zero_def less_antisym minus_nat.diff_0 sa0 valid valid_one_minus_eps zero_less_Suc 
              zero_less_power) 
        moreover have "is_finite fmt (se, ee, fe)"
          using False Suc_diff_Suc asef emax_def esef 
              expneq exponent.simps is_denormal_def is_finite_def is_normal_def is_valid_def 
              is_zero_def less_antisym minus_nat.diff_0 sa0 valid valid_one_minus_eps zero_less_Suc 
              zero_less_power
          sledgehammer[timeout=120]
           
            sorry
        hence "valof fmt (sa,ea,fa) < valof fmt (se,ee,fe)"
          using pos_gt_if_exp_gt
          sledgehammer 
            sorry
        then show ?thesis
          (* sledgehammer quickcheck *)
            sorry
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
      using eps_gt_zero asef asm rsnbl by fastforce
  qed
qed

subsection \<open>Properties of multiplication\<close>

  (* What about To_nearest? 
What about showing that magnitude of x decreased?*)
lemma mult_lt_1_smaller:  
  assumes vndx:"is_valid fmt x \<and> (is_normal fmt x \<or> is_denormal fmt x)"
    and vndy:"is_valid fmt y \<and> (is_normal fmt y \<or> is_denormal fmt y)"
    and ylt1:"valof fmt y > 0 \<and> valof fmt y < 1"
    (* TODO get rid of this requirement, use magnitude: *)
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

  
(* lemma denorm_result:  
  assumes "is_valid fmt d \<and> is_denormal fmt d "
    and "is_valid fmt x"
    and "valof fmt x > 0 \<and> valof fmt x < 1"
  shows "is_denorm fmt (fmul float_format To_nearest d x)"
 *)
  
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
        using pos_gt_suc_frac by blast
      then show ?case 
        using Suc.IH Suc.prems ii2 by linarith
    qed
    hence "valof float_format (ys, ye, yf) > valof float_format (0, 0, 1)"
      using ys0 by auto
    hence "y > SmallPositiveDenorm"
    proof -
      have "Isdenormal SmallPositiveDenorm"
        sorry
      have "Finite SmallPositiveDenorm"
        sorry
          
    qed
    using SmallPositiveDenorm_def ysef ypos ys0 float_lt
      sorry
      
(*       Now we have both:
      x < SmallPositiveDenorm
      valof float_format (0, 0, 1) < valof float_format (0, ye, yf)
      So we can show false *)
      
    then show False 
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