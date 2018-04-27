theory leftpad
  imports Main 
  "~~/src/HOL/Library/Code_Target_Nat"
begin

section \<open>define leftpad\<close>
  
(* Leftpad. Takes a padding character, a string, and a total length, returns
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

text "rightPad is identity when list length is GTE arg"
lemma rightPad_list_is_longer:
  fixes lst :: "'a list"
    and padTo :: nat
  assumes "length lst \<ge> padTo"
  shows "\<lbrakk>length lst \<ge> padTo\<rbrakk> 
      \<Longrightarrow> rightPad p lst padTo = lst"
proof(induction lst ) (* arbitrary: padTo *)
  case Nil
  then show ?case by simp
next
  case (Cons a lst)
  then show ?case 
  proof(induction padTo)
    case 0
    then show ?case by simp
  next
    case (Suc padTo)
    then show ?case 
      sorry
  qed
qed
