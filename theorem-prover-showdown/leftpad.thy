theory leftpad
  imports Main 
  "~~/src/HOL/Library/Code_Target_Nat"
begin

section \<open>define leftpad\<close>
  
(* left pad. Takes a padding character, a string, and a total length, returns
the string padded to that length with that character. If length is less than
the length of the string, does nothing. *)

fun rightPad :: "'a => 'a list => nat => 'a list" where
  "rightPad p [] 0 = []" |
  "rightPad p [] (Suc n) = p # (rightPad p [] n)" |
  "rightPad p (x # xs) 0 = (x # xs)" |
  "rightPad p (x # xs) (Suc n) = x # (rightPad p xs n)"

fun leftPad :: "'a => 'a list => nat => 'a list" where
  "leftPad p xs n = rev (rightPad p (rev xs) n)"
  
value "leftPad 0 [1,2] 1 :: nat list"
value "leftPad 0 [1,2] 4 :: nat list"
value "leftPad 9 [1,1] 3 :: nat list"
  
(* Prove: 

You have to specify it’s the right length,

that the added characters are all the padding character,

and that the suffix is the original string. *)

section \<open>Proofs\<close>

subsection \<open>right pad\<close>

(*TODO probably delete this in favor of right_pad_prefix_is_list*)
text "rightPad is identity when list length is \<ge> padTo"
lemma right_pad_id_when_longer:
  fixes lst :: "'a list"
    and padTo :: nat
  assumes "length lst \<ge> padTo"
  shows "\<lbrakk>length lst \<ge> padTo\<rbrakk> 
      \<Longrightarrow> rightPad p lst padTo = lst"
proof(induction lst arbitrary: padTo)
  case Nil
  then show ?case by simp
next
  case (Cons l ls)
  then show ?case 
  proof(induction padTo)
    case 0
    then show ?case by simp
  next
    case (Suc padT)
    then show ?case by (simp add: Suc.IH)
  qed
qed

lemma rightpad_empty_is_replicate:"\<lbrakk>padTo = n\<rbrakk> \<Longrightarrow> rightPad p [] padTo = replicate n p"
proof(induction padTo arbitrary: n)
  case 0
  then show ?case 
    by simp 
next
  case (Suc padTo)
  then show ?case 
    by auto
qed

text "additional characters are padding"
lemma right_pad_adds_padding_character:
  fixes lst :: "'a list"
    and p :: "'a"
    and padTo :: nat
  assumes "length lst < padTo"
    and "length lst + n = padTo"
  shows "\<lbrakk>length lst < padTo; length lst + n = padTo\<rbrakk> 
      \<Longrightarrow> drop (length lst) (rightPad p lst padTo) = replicate n p"
proof(induction lst arbitrary: padTo)
  case Nil
  then show ?case 
  proof(induction padTo)
    case 0
    then show ?case by simp
  next
    case (Suc padTo)
    then show ?case 
      by (simp add: rightpad_empty_is_replicate)
  qed
next
  case (Cons l ls)
  then show ?case 
  proof(induction padTo)
    case 0
    then show ?case by simp
  next
    case (Suc padT)
    then show ?case by simp
  qed
qed

text "prefix of result is the list"
lemma right_pad_prefix_is_list:
  fixes lst :: "'a list"
    and p :: "'a"
    and padTo :: nat
  shows "take (length lst) (rightPad p lst padTo) = lst"
proof(induction lst arbitrary: padTo)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a lst)
  then show ?case 
  proof(induction padTo)
    case 0
    then show ?case 
      by simp
  next
    case (Suc padTo)
    then show ?case 
      by simp
  qed
qed

text "length is correct"
lemma right_pad_length_is_correct:
  shows "length (rightPad p lst padTo) = max (length lst) padTo"
proof(induction lst arbitrary: padTo)
  case Nil
  then show ?case 
    by (simp add: rightpad_empty_is_replicate)
next
  case (Cons a lst)
  then show ?case 
  proof(induction padTo)
    case 0
    then show ?case 
      by simp
  next
    case (Suc padTo)
    then show ?case 
      by simp
  qed
qed

subsection \<open>left pad\<close> 

(*TODO is this useful?*)
lemma leftpad_empty_is_rightpad:"leftPad p [] padTo = rightPad p [] padTo"
  by (simp add: rightpad_empty_is_replicate)

(*TODO is this useful?*)
lemma same_length:"length (leftPad p lst padTo) = length (rightPad p lst padTo)"
  by (simp add: right_pad_length_is_correct)

text "length is correct"
lemma left_pad_length_is_correct:
  shows "length (leftPad p lst padTo) = max (length lst) padTo"
  by (simp add: right_pad_length_is_correct)

text "suffix of result is the list"
lemma left_pad_suffix_is_list:
  fixes lst :: "'a list"
    and p :: "'a"
    and padTo :: nat
  assumes "length lst < padTo"
    and "length lst + n = padTo"
  shows "\<lbrakk>length lst + n = padTo\<rbrakk> \<Longrightarrow> drop n (leftPad p lst padTo) = lst"
proof(induction lst)
  case Nil
  then show ?case 
    by (simp add: rightpad_empty_is_replicate) 
next
  case (Cons l ls)
  then show ?case 
  proof(induction padTo)
    case 0
    then show ?case 
      by simp 
  next
    case (Suc padTo\<^sub>p)
    then show ?case
      apply auto
      by (metis (no_types, lifting) Suc.prems(2) add_diff_cancel_left' le_add1 length_rev max_def rev.simps(2) rev_rev_ident rev_take right_pad_length_is_correct right_pad_prefix_is_list) 
  qed    
qed
