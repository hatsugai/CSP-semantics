(*
  Formal proof of the equivalence between a denotational semantics
  and an operational semantics on traces model of CSP
  by Isabelle/HOL 2014

  (C) 2020 Hisabumi Hatsugai
*)

theory "equiv-op-deno-traces" imports Main begin

lemma list_rev_cases: "ALL xs. xs = [] | (EX y ys. xs = ys @ [y])"
apply(rule allI)
apply(induct_tac xs)
apply(auto)
done

lemma rev_rev_list: "(ALL x. P (rev x)) --> P x"
apply(rule impI)
apply(drule_tac x="rev x" in spec)
apply(simp)
done

lemma rev_list_induct0: "P [] & (ALL a x. P x --> P (x @ [a])) --> P x"
apply(rule rev_rev_list[rule_format])
apply(induct_tac x)
apply(auto)
done

lemma rev_list_induct: "[| P []; !!a x. P x ==> P (x @ [a]) |] ==> P x"
apply(rule rev_list_induct0[rule_format])
apply(auto)
done

fun forall :: "('a => bool) => 'a list => bool" where
  "forall f [] = True"
| "forall f (x#xs) = ((f x) & (forall f xs))"

fun forall2 :: "('a => 'b => bool) => 'a list => 'b list => bool" where
  "forall2 f [] ys = (ys = [])"
| "forall2 f (x#xs) [] = False"
| "forall2 f (x#xs) (y#ys) = ((f x y) & (forall2 f xs ys))"

lemma forall_app [simp]: "ALL ys. forall f (xs @ ys) = ((forall f xs) & (forall f ys))"
apply(induct_tac xs)
apply(clarsimp)
apply(clarsimp)
done

lemma forall_scanD_0:
  "forall f xs --> (ALL i<length xs. f(xs!i))"
apply(induct_tac xs)
apply(clarsimp)
apply(clarsimp)
by (metis One_nat_def diff_Suc_Suc diff_zero gr0_conv_Suc less_Suc_eq_0_disj nat.distinct(1) nth_non_equal_first_eq)

lemma forall_scanD:
  "forall f xs ==> (ALL i<length xs. f(xs!i))"
apply(insert forall_scanD_0)
apply(auto)
done

lemma forall_scanI_0:
  "(ALL i<length xs. f(xs!i)) --> forall f xs"
apply(induct_tac xs)
apply(clarsimp)
apply(clarsimp)
by (metis Suc_less_eq nth_Cons_0 nth_Cons_Suc zero_less_Suc)

lemma forall_scanI:
  "[| ALL i<n. f(xs!i); n = length xs |] ==> forall f xs"
apply(insert forall_scanI_0)
apply(auto)
done

lemma forall_mono_0:
  "(forall f xs) -->
   (ALL x. f x --> g x) -->
   (forall g xs)"
apply(induct_tac xs)
apply(clarsimp)
apply(clarsimp)
done

lemma forall_mono:
  "[| forall f xs; ALL x. f x --> g x |] ==> forall g xs"
apply(insert forall_mono_0)
apply(auto)
done

(***  syntax  *************************************************************)

datatype 
 ('p,'a) proc
    = STOP

    | Act_prefix     "'a" "('p,'a) proc"      ("(1_ /-> _)" [150,80] 80)

    | Ext_pre_choice "'a set" "'a => ('p,'a) proc"
                                               ("(1? :_ /-> _)" [900,80] 80)
    | Ext_choice     "('p,'a) proc" "('p,'a) proc"  
                                               ("(1_ /[+] _)" [72,73] 72)
    | Int_choice     "('p,'a) proc" "('p,'a) proc"  
                                               ("(1_ /|~| _)" [64,65] 64)
    | Rep_int_choice "nat set" "nat => ('p,'a) proc"
                                               ("(1!! :_ .. /_)" [900,68] 68) 
    | IF             "bool" "('p,'a) proc" "('p,'a) proc"
                                 ("(0IF _ /THEN _ /ELSE _)" [900,88,88] 88)
    | Parallel       "('p,'a) proc" "'a set" "('p,'a) proc"  
                                               ("(1_ /|[_]| _)" [76,0,77] 76)
    | Hiding         "('p,'a) proc" "'a set"   ("(1_ /-- _)" [84,85] 84)

    | Renaming       "('p,'a) proc" "('a * 'a) set"
                                               ("(1_ /[[_]])" [84,0] 84)
    | Proc_name      "'p"                      ("$_" [900] 90)


(***  trace domain  *******************************************************)

definition prefix :: "'a list => 'a list => bool" where
"prefix x y == (EX z. y = x @ z)"

definition prefix_closed :: "'a list set => bool" where
"prefix_closed s == ALL x y. x : s & prefix y x --> y : s"

definition HC_T1 :: "'a list set => bool" where
"HC_T1 s == (s ~= {} & prefix_closed s)"

definition "domT  = {s::('a list set). HC_T1 s}"
typedef 'a domT = "domT :: 'a list set set"
apply (simp add: domT_def HC_T1_def)
apply (rule_tac x ="{[]}" in exI)
apply(simp add: prefix_closed_def prefix_def)
done

lemma HC_T1_Rep_domT [simp]: "HC_T1 (Rep_domT x)"
apply(subgoal_tac "Rep_domT x : domT")
defer
apply(rule Rep_domT)
apply(simp add: domT_def)
done

lemma HC_T1_Un: "[| HC_T1 p; HC_T1 q |] ==> HC_T1 (p Un q)"
apply(unfold HC_T1_def prefix_closed_def)
by (metis Un_iff all_not_in_conv)

lemma prefix_nil [simp]: "prefix [] s"
apply(simp add: prefix_def)
done

lemma HC_T1_Int_lemma: "[| HC_T1 p; HC_T1 q |] ==> [] : p Int q"
apply(unfold HC_T1_def)
by (metis Int_iff all_not_in_conv prefix_closed_def prefix_nil)

lemma HC_T1_Int: "[| HC_T1 p; HC_T1 q |] ==> HC_T1 (p Int q)"
apply(unfold HC_T1_def prefix_closed_def)
by (metis (mono_tags) Int_iff all_not_in_conv prefix_nil)

lemma Rep_domT_Int0: "Rep_domT y Int Rep_domT z : domT"
apply(subst domT_def)
by (metis (full_types) HC_T1_Int HC_T1_Rep_domT mem_Collect_eq)

lemma Rep_domT_Int:
"s : Rep_domT (Abs_domT (Rep_domT p Int Rep_domT q))
==> s : Rep_domT p"
apply(subgoal_tac "EX x. Rep_domT p Int Rep_domT q = x & x : domT")
apply(erule exE)
apply(erule conjE)
apply(simp add: Rep_domT_inverse)
apply(simp add: Abs_domT_inverse)
apply(blast)
by (metis (full_types) HC_T1_Int Rep_domT domT_def mem_Collect_eq)

lemma Rep_domT_Un0: "Rep_domT y Un Rep_domT z : domT"
apply(subst domT_def)
by (metis (full_types) HC_T1_Rep_domT HC_T1_Un mem_Collect_eq)

lemma Rep_domT_Un:
 "s : Rep_domT p ==> s : Rep_domT (Abs_domT (Rep_domT p Un Rep_domT q))"
apply(subgoal_tac "EX x. Rep_domT p Un Rep_domT q = x & x : domT")
apply(erule exE)
apply(erule conjE)
apply(subst Abs_domT_inverse)
apply(clarsimp)
apply(blast)
apply(clarsimp)
apply(subst domT_def)
apply(clarsimp)
apply(rule HC_T1_Un)
apply(simp)
apply(simp)
done

lemma domT_Rep_nil [simp]: "[] : Rep_domT p"
apply(subgoal_tac "Rep_domT p : domT")
defer
apply(rule Rep_domT)
apply(unfold domT_def)
apply(clarify)
apply(unfold HC_T1_def)
apply(clarify)
apply(unfold prefix_closed_def)
apply(subgoal_tac "EX s. s : Rep_domT p")
apply(erule exE)
apply(drule_tac x="s" in spec)
apply(drule_tac x="[]" in spec)
apply(clarsimp)
apply(blast)
done

lemma domT_Rep_prefix: "[| x : Rep_domT p; prefix y x |] ==> y : Rep_domT p"
apply(subgoal_tac "HC_T1 (Rep_domT p)")
apply (metis HC_T1_def prefix_closed_def)
by (metis HC_T1_Rep_domT)

lemma domT_Rep_Inter: "Inter {Rep_domT p |p. p : A} : domT"
apply(subst domT_def)
apply(clarsimp)
apply(unfold HC_T1_def)
apply(rule conjI)
apply(case_tac "A={}")
apply(clarsimp)
apply(subgoal_tac "ALL p. [] : Rep_domT p")
apply(subgoal_tac "[] : Inter {Rep_domT p |p. p : A}")
apply(blast)
apply(clarsimp)
apply(clarsimp)
(**)
apply(unfold prefix_closed_def)
apply(clarify)
apply(erule contrapos_pp)
apply(subst Inter_iff)
apply(erule contrapos_nn)
apply(clarsimp)
apply(drule_tac x="Rep_domT p" in spec)
apply(drule mp)
apply metis
apply(erule domT_Rep_prefix)
apply(clarsimp)
done

lemma domT_Rep_Union: "q : A ==> Union {Rep_domT p |p. p : A} : domT"
apply(subst domT_def)
apply(clarsimp)
apply(unfold HC_T1_def)
apply(rule conjI)
apply(subst ex_in_conv[symmetric])
apply(rule_tac x="[]" in exI)
apply (metis (lifting, full_types) UnionI domT_Rep_nil mem_Collect_eq)
(**)
apply(unfold prefix_closed_def)
apply(clarsimp)
apply(rule_tac x="Rep_domT p" in exI)
apply(rule conjI)
apply(rule_tac x="p" in exI)
apply(clarsimp)
by (metis domT_Rep_prefix)

lemma domT_STOP [simp]: "{[]} : domT"
apply(unfold domT_def)
apply(clarsimp)
apply(unfold HC_T1_def prefix_closed_def)
by (metis (full_types) append_is_Nil_conv insert_not_empty prefix_def singleton_iff)

instantiation domT :: (type) complete_lattice
begin

(*
class ord
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

class preorder = ord +

class order = preorder +

class inf =
  fixes inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)

class sup = 
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)

class semilattice_inf =  order + inf +

class semilattice_sup = order + sup +

class lattice = semilattice_inf + semilattice_sup

class bot = order +
  fixes bot :: 'a ("\<bottom>")

class top = order +
  fixes top :: 'a ("\<top>")

class bounded_lattice_bot = lattice + bot

class bounded_lattice_top = lattice + top

class bounded_lattice = bounded_lattice_bot + bounded_lattice_top

class Inf =
  fixes Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900)

class Sup =
  fixes Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900)

class complete_lattice = bounded_lattice + Inf + Sup +
*)

definition
domT_less_eq_def: "p <= q == (Rep_domT p <= Rep_domT q)"
definition
domT_less_def: "p < q == (Rep_domT p < Rep_domT q)"
definition
domT_inf_def: "inf p q == Abs_domT (Rep_domT p Int Rep_domT q)"
definition
domT_sup_def: "sup p q == Abs_domT (Rep_domT p Un Rep_domT q)"
definition
domT_bot_def: "bot == Abs_domT {[]}"
definition
domT_top_def: "top == Abs_domT UNIV"
definition
domT_Inf_def: "Inf s  = Abs_domT (Inter {Rep_domT p | p. p : s})"
definition
domT_Sup_def: "Sup s  = (if s={} then Abs_domT {[]} else Abs_domT (Union {Rep_domT p | p. p : s}))"

instance
apply(intro_classes)
apply(unfold domT_less_eq_def domT_less_def domT_inf_def domT_sup_def domT_bot_def domT_top_def domT_Inf_def domT_Sup_def)
apply(auto)
(* 12 *)
apply(simp add: Rep_domT_inject)
(* 11 *)
apply(erule Rep_domT_Int)
(* 10 *)
apply(erule contrapos_pp)
apply(subst Int_commute)
apply(erule contrapos_nn)
apply(erule Rep_domT_Int)
(* 9 *)
apply(subst Abs_domT_inverse)
apply(unfold domT_def)
apply(clarsimp)
apply(rule HC_T1_Int)
apply(simp)
apply(simp)
apply(blast)
(* 8 *)
apply(erule Rep_domT_Un)
(* 7 *)
apply(subst Un_commute)
apply(erule Rep_domT_Un)
(* 6 *)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(subst Abs_domT_inverse)
apply(rule Rep_domT_Un0)
apply(erule contrapos_nn)
apply (metis Un_iff set_mp)
(* 5 *)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(subst Abs_domT_inverse)
apply(rule domT_Rep_Inter)
apply(subst Inter_iff)
apply(erule contrapos_nn)
apply(clarsimp)
apply(drule_tac x="Rep_domT x" in spec)
apply(drule mp)
apply(rule_tac x="x" in exI)
apply(clarsimp)
apply(clarsimp)
(* 4 *)
apply(subst Abs_domT_inverse)
apply(rule domT_Rep_Inter)
apply(subst Inter_iff)
apply(clarsimp)
apply(blast)
(* 3 *)
apply(erule contrapos_np)
apply(subst Abs_domT_inverse)
apply(erule domT_Rep_Union)
apply(subst Union_iff)
apply(clarsimp)
apply metis
(* 2 *)
apply (metis (mono_tags) Abs_domT_inverse domT_Rep_nil domT_STOP empty_iff insert_iff)
(* 1 *)
apply(rotate_tac -3)
apply(erule contrapos_pp)
apply(subst Abs_domT_inverse)
apply(erule domT_Rep_Union)
apply(subst Union_iff)
apply(erule contrapos_nn)
apply(clarsimp)
by (metis in_mono)

end

fun ceal :: "'a set => 'a list => 'a list" where
  "ceal X [] = []"
| "ceal X (a#t) = (if a : X then ceal X t else a#(ceal X t))"

lemma ceal_prefix [rule_format]:
  "ALL y z. y @ z = ceal X s --> (EX s1 s2. s1 @ s2 = s & y = ceal X s1)"
apply(induct_tac s)
apply(clarsimp)
apply(clarsimp)
apply(safe)
apply(drule_tac x="y" in spec)
apply(drule mp)
apply(rule_tac x="z" in exI)
apply(simp)
apply(clarsimp)
apply(rule_tac x="a#s1" in exI)
apply(clarsimp)
(* a ~: X *)
apply(case_tac y)
apply(clarsimp)
apply (metis ceal.simps(1) eq_Nil_appendI)
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(drule mp)
apply metis
apply(clarsimp)
apply(rule_tac x="a#s1" in exI)
apply(clarsimp)
done

fun sync :: "'a set => 'a list => 'a list => 'a list set" where
  "sync X [] [] = {[]}"
| "sync X [] (a#t) = (if a : X then {} else {a#s | s. s : sync X [] t})"
| "sync X s [] = sync X [] s"
| "sync X (a#s) (b#t) = (if a : X then
                           if b : X then
                             if a = b then
                               {a#u | u. u : sync X s t}
                             else
                               {}
                           else
                             {b#u | u. u : sync X (a#s) t}
                         else
                           if b : X then
                             {a#u | u. u : sync X s (b#t)}
                           else
                             {a#u | u. u : sync X s (b#t)} Un {b#u | u. u : sync X (a#s) t})"

lemma sync_nil[rule_format]: "ALL s. s : sync X [] t --> s = t & set s Int X = {}"
apply(induct_tac t)
apply(clarsimp)
apply(clarsimp)
done

lemma sync_prefix_0[rule_format]:
 "ALL y z. y @ z : sync X [] t --> (EX t1. (EX t2. t1 @ t2 = t) & y : sync X [] t1)"
apply(induct_tac t)
apply(clarsimp)
apply(clarsimp)
apply(frule sync_nil)
apply(clarsimp)
apply(case_tac y)
apply(clarsimp)
apply(drule_tac x="[]" in spec)
apply(drule mp)
apply (metis append_Nil)
apply(clarsimp)
apply (metis eq_Nil_appendI sync_nil)
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(drule mp)
apply metis
apply(clarsimp)
apply(rule_tac x="a#t1" in exI)
apply(clarsimp)
by metis

lemma sync_sym0 [rule_format]:
  "(ALL t. sync X s t = sync X t s) --> sync X (a # s) t = sync X t (a # s)"
apply(induct_tac t)
apply(auto)
done

lemma sync_sym [rule_format]: "ALL s t. sync X s t = sync X t s"
apply(rule allI)
apply(induct_tac s)
apply(clarsimp)
apply (metis neq_Nil_conv sync.simps(3))
apply(clarsimp)
apply(rename_tac a s t)
apply(rule sync_sym0)
apply(auto)
done

lemma sync_prefix_1[rule_format]:
"ALL a y z.
(ALL y z t. y @ z : sync X s t --> (EX s1. (EX s2. s1 @ s2 = s) & (EX t1. (EX t2. t1 @ t2 = t) & y : sync X s1 t1))) --> y @ z : sync X (a # s) t -->
       (EX s1. (EX s2. s1 @ s2 = a # s) & (EX t1. (EX t2. t1 @ t2 = t) & y : sync X s1 t1))"
apply(induct_tac t)
apply(clarsimp)
apply(case_tac y)
apply(clarsimp)
apply(drule_tac x="[]" in spec)
apply(clarsimp)
apply(frule sync_nil)
apply(clarsimp)
apply(drule_tac x="s" in spec)
apply(drule_tac x="[]" in spec)
apply(clarsimp)
apply(drule mp)
apply (metis (full_types) neq_Nil_conv sync.simps(3))
apply (metis append_Nil lists.Nil lists_empty sync.simps(1))
apply(clarsimp)
apply(drule_tac x="list" in spec)
apply(drule_tac x="z" in spec)
apply(drule_tac x="[]" in spec)
apply(clarsimp)
apply(drule mp)
apply (metis (full_types) neq_Nil_conv sync.simps(3))
apply(clarsimp)
apply(subgoal_tac "list : sync X [] s1")
apply(rotate_tac -1)
apply(frule sync_nil)
apply(clarsimp)
apply(rule_tac x="a#s1" in exI)
apply(clarsimp)
apply (metis (full_types) neq_Nil_conv sync.simps(3))
(**)
apply(clarsimp)
apply(safe)
apply(case_tac y)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(rotate_tac -1)
apply(drule_tac x="z" in spec)
apply(rotate_tac -1)
apply(drule_tac x="list" in spec)
apply(drule mp)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="a#s1" in exI)
apply(clarsimp)
apply(rule_tac x="a#t1" in exI)
apply(clarsimp)
(**)
apply(case_tac y)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(rotate_tac -1)
apply(drule_tac x="z" in spec)
apply(rotate_tac -1)
apply(drule_tac x="a#list" in spec)
apply(drule mp)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="a#s1" in exI)
apply(clarsimp)
apply(rule_tac x="t1" in exI)
apply(rule conjI)
apply metis
apply(case_tac t1)
apply(clarsimp)
apply (metis (full_types) neq_Nil_conv sync.simps(3))
apply(clarsimp)
(* 5 *)
apply(case_tac y)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="a" in spec)
apply(rotate_tac -1)
apply(drule_tac x="lista" in spec)
apply(drule mp)
apply(rule_tac x="z" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="s1" in exI)
apply(rule conjI)
apply(blast)
apply(rule_tac x="a#t1" in exI)
apply(rule conjI)
apply(rule_tac x="t2" in exI)
apply(clarsimp)
apply(case_tac s1)
apply(clarsimp)
apply(clarsimp)
(* 4 *)
apply(case_tac y)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(rotate_tac -1)
apply(drule_tac x="z" in spec)
apply(rotate_tac -1)
apply(drule_tac x="a#list" in spec)
apply(drule mp)
apply(clarsimp)
apply(clarsimp)
apply(case_tac t1)
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(subst sync_sym)
apply(rotate_tac -1)
apply(erule contrapos_nn)
apply(frule sync_nil)
apply(clarsimp)
apply(rule_tac x="aa#s1" in exI)
apply(rule conjI)
apply(rule_tac x="s2" in exI)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="aa#s1" in exI)
apply(rule conjI)
apply(rule_tac x="s2" in exI)
apply(clarsimp)
apply(rule_tac x="a#listb" in exI)
apply(clarsimp)
(* 3 *)
apply(case_tac y)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="aa" in spec)
apply(rotate_tac -1)
apply(drule_tac x="lista" in spec)
apply(drule mp)
apply(rule_tac x="z" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="s1" in exI)
apply(rule conjI)
apply(blast)
apply(rule_tac x="a#t1" in exI)
apply(rule conjI)
apply(rule_tac x="t2" in exI)
apply(clarsimp)
apply(case_tac s1)
apply(clarsimp)
apply(clarsimp)
(* 2 *)
apply(case_tac y)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(rotate_tac -1)
apply(drule_tac x="z" in spec)
apply(rotate_tac -1)
apply(drule_tac x="a#list" in spec)
apply(drule mp)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="aa#s1" in exI)
apply(rule conjI)
apply(rule_tac x="s2" in exI)
apply(clarsimp)
apply(rule_tac x="t1" in exI)
apply(rule conjI)
apply(rule_tac x="t2" in exI)
apply(clarsimp)
apply(case_tac t1)
apply(clarsimp)
apply (metis sync_sym)
apply(clarsimp)
(* 1 *)
apply(case_tac y)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="aa" in spec)
apply(rotate_tac -1)
apply(drule_tac x="lista" in spec)
apply(drule mp)
apply(rule_tac x="z" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="s1" in exI)
apply(rule conjI)
apply(blast)
apply(rule_tac x="a#t1" in exI)
apply(rule conjI)
apply(rule_tac x="t2" in exI)
apply(clarsimp)
apply(case_tac s1)
apply(clarsimp)
apply(clarsimp)
done

lemma sync_prefix: "ALL y z t. y @ z : sync X s t --> (EX s1 s2 t1 t2. s1 @ s2 = s & t1 @ t2 = t & y : sync X s1 t1)"
apply(induct_tac s)
apply(clarsimp)
apply(drule sync_prefix_0)
apply(clarsimp)
apply(rename_tac s)
apply(clarsimp)
apply(rule sync_prefix_1)
apply(clarsimp)
apply(assumption)
done

lemma sync_prefixD:
  "[| prefix u w; w : sync X s t |] ==> EX s1 t1. prefix s1 s & prefix t1 t & u : sync X s1 t1"
apply(unfold prefix_def)
apply(clarsimp)
apply(drule sync_prefix[rule_format])
apply(clarsimp)
by metis

definition rename_tr :: "('a * 'a) set => 'a list => 'a list => bool" where
  "rename_tr R s t = (length s = length t & forall2 (%a b. (a, b) : R) s t)"

lemma rename_tr_nil [intro, simp]:
  "rename_tr R [] []"
apply(unfold rename_tr_def)
apply(clarsimp)
done

lemma rename_tr_nil1 [dest]:
  "rename_tr R s [] ==> s = []"
apply(unfold rename_tr_def)
apply(clarsimp)
done

lemma rename_tr_nil2 [dest]:
  "rename_tr R [] t ==> t = []"
apply(unfold rename_tr_def)
apply(clarsimp)
done

lemma rename_tr_car [simp]:
  "rename_tr R (a#s) (b#t) = ((a,b):R & rename_tr R s t)"
apply(unfold rename_tr_def)
apply(clarsimp)
apply(rule iffI)
apply(clarsimp)
apply(clarsimp)
done

primrec traces_r :: "('p, 'a) proc => ('p => 'a domT) => 'a list set" where
  "traces_r STOP M = {[]}"
| "traces_r (a -> P) M = {t. t = [] | (EX s. t = a#s & s : traces_r P M)}"
| "traces_r (? :A -> Pf) M =
                  {t. t = [] |
                      (EX a s. t = a#s & a : A & s : traces_r (Pf a) M)}"
| "traces_r (P [+] Q) M = (traces_r P M) Un (traces_r Q M)"
| "traces_r (P |~| Q) M = (traces_r P M) Un (traces_r Q M)"
| "traces_r (!! :A .. Pf) M = {[]} Un Union {(traces_r (Pf n) M) | n. n : A}"
| "traces_r (IF b THEN P ELSE Q) M = (if b then traces_r P M else traces_r Q M)"
| "traces_r (P |[X]| Q) M =
             {u. EX s t. u : sync X s t &
                         s : (traces_r P M) &
                         t : (traces_r Q M)}"
| "traces_r (P -- X) M = {t. EX s. t = ceal X s & s : traces_r P M}"
| "traces_r (P[[R]]) M = {t. EX s. rename_tr R s t & s : traces_r P M}"
| "traces_r ($p) M = Rep_domT (M p)"

lemma traces_r_nil [intro!]: "[] : traces_r P M"
apply(induct_tac P)
apply(auto)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="[]" in exI)
apply(simp)
apply(rule_tac x="[]" in exI)
apply(simp)
done

lemma traces_r_not_empty [intro!]: "traces_r P M ~= {}"
by auto

lemma HC_T1_D1: "HC_T1 P ==> P ~= {}"
apply(simp add: HC_T1_def)
done

lemma HC_T1_D2: "HC_T1 P ==> prefix_closed P"
apply(simp add: HC_T1_def)
done

lemma prefix_nil2 [dest!]: "prefix s [] ==> s = []"
by (simp add: prefix_def)

lemma prefix_Cons [dest]: "prefix s (a#t) ==> s = [] | (EX s1. s = a#s1 & prefix s1 t)"
apply(simp add: prefix_def)
by (metis append_eq_Cons_conv)

lemma prefix_closedE [elim]:
  "[| prefix t s; s : P; prefix_closed P |] ==> t : P"
by (simp add: prefix_closed_def)

lemma HC_T1_prefix_closed2 [elim]:
  "[| prefix t s; s : P; HC_T1 P |] ==> t : P"
apply(drule HC_T1_D2)
by (auto)

lemma traces_r_STOP_prefix_closed [intro!]:
  "prefix_closed (traces_r STOP M)"
by (auto simp add: prefix_closed_def)

lemma traces_r_prefix_closed_prefix [intro!]:
  "prefix_closed (traces_r P M) ==> prefix_closed (traces_r (a -> P) M)"
apply(subst prefix_closed_def)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(clarsimp)
apply(drule prefix_Cons)
apply(clarsimp)
apply(drule prefix_closedE)
apply(assumption)
apply(assumption)
apply(simp)
done

lemma traces_r_prefix_choice_prefix_closed [intro!]:
  "ALL x. x : A --> prefix_closed (traces_r (Pf x) M)
 ==> prefix_closed (traces_r (? :A -> Pf) M)"
apply(unfold prefix_closed_def)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(clarsimp)
apply(drule prefix_Cons)
apply(clarsimp)
done

lemma traces_r_ext_choice_prefix_closed [intro!]:
  "[| prefix_closed (traces_r P M);
      prefix_closed (traces_r Q M) |]
  ==> prefix_closed (traces_r (P [+] Q) M)"
apply(subst prefix_closed_def)
apply(clarsimp)
apply(erule disjE)
apply(erule prefix_closedE)
apply(assumption)
apply(assumption)
apply(erule contrapos_np)
apply(erule prefix_closedE)
apply(assumption)
apply(assumption)
done

lemma traces_r_int_choice_prefix_closed [intro!]:
  "[| prefix_closed (traces_r P M);
      prefix_closed (traces_r Q M) |]
  ==> prefix_closed (traces_r (P |~| Q) M)"
apply(subst prefix_closed_def)
apply(clarsimp)
apply(erule disjE)
apply(erule prefix_closedE)
apply(assumption)
apply(assumption)
apply(erule contrapos_np)
apply(erule prefix_closedE)
apply(assumption)
apply(assumption)
done

lemma traces_r_rep_int_choice_prefix_closed [intro!]:
  "ALL x. prefix_closed (traces_r (Pf x) M)
 ==> prefix_closed (traces_r (!! :A .. Pf) M)"
apply(unfold prefix_closed_def)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="n" in spec)
apply(drule_tac x="x" in spec)
apply(drule_tac x="y" in spec)
apply(clarsimp)
by metis

lemma traces_r_if_prefix_closed [intro!]:
  "[| prefix_closed (traces_r P M);
      prefix_closed (traces_r Q M) |]
  ==> prefix_closed (traces_r (IF b THEN P ELSE Q) M)"
by simp

lemma traces_r_par_prefix_closed [intro!]:
  "[| prefix_closed (traces_r P M);
      prefix_closed (traces_r Q M) |]
  ==> prefix_closed (traces_r (P |[X]| Q) M)"
apply(subst prefix_closed_def)
apply(clarsimp)
apply(drule sync_prefixD)
apply(assumption)
apply(clarsimp)
by (metis prefix_closed_def)

lemma traces_r_hide_prefix_closed [intro!]:
  "prefix_closed (traces_r P M)
  ==> prefix_closed (traces_r (P -- X) M)"
apply(subst prefix_closed_def)
apply(clarsimp)
apply(unfold prefix_def)
apply(clarsimp)
apply(drule sym[THEN ceal_prefix])
apply(clarsimp)
apply(rule_tac x="s1" in exI)
apply(clarsimp)
apply(unfold prefix_closed_def)
by (metis prefix_def)

lemma rename_tr_prefix [rule_format]:
  "ALL t1 t2. rename_tr R s (t1 @ t2) --> (EX s1 s2. s1@s2=s & rename_tr R s1 t1)"
apply(induct_tac s)
apply(clarsimp)
apply(drule rename_tr_nil2)
apply(clarsimp)
apply(clarsimp)
apply(case_tac t1)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(drule mp)
apply(rule_tac x="t2" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="a#s1" in exI)
apply(clarsimp)
done

lemma traces_r_rename_prefix_closed [intro!]:
  "prefix_closed (traces_r proc M) ==> prefix_closed (traces_r (proc [[R]]) M)"
apply(subst prefix_closed_def)
apply(clarsimp)
apply(unfold prefix_def)
apply(clarsimp)
apply(drule rename_tr_prefix)
apply(clarsimp)
apply(rule_tac x="s1" in exI)
apply(clarsimp)
apply(unfold prefix_closed_def)
by (metis prefix_def)

lemma traces_r_pn_prefix_closed [intro!]:
  "prefix_closed (traces_r ($p) M)"
apply(subst prefix_closed_def)
apply(clarsimp)
by (metis domT_Rep_prefix)

lemma traces_r_prefix_closed [intro!]: "prefix_closed (traces_r P M)"
apply(induct_tac P)
apply(rule traces_r_STOP_prefix_closed)
apply(erule traces_r_prefix_closed_prefix)
apply(rule traces_r_prefix_choice_prefix_closed)
apply(clarsimp)
apply(erule traces_r_ext_choice_prefix_closed)
apply(assumption)
apply(erule traces_r_int_choice_prefix_closed)
apply(assumption)
apply(rule traces_r_rep_int_choice_prefix_closed)
apply(clarsimp)
apply(erule traces_r_if_prefix_closed)
apply(assumption)
apply(erule traces_r_par_prefix_closed)
apply(assumption)
apply(erule traces_r_hide_prefix_closed)
apply(erule traces_r_rename_prefix_closed)
apply(rule traces_r_pn_prefix_closed)
done

lemma traces_r_HC_T1: "HC_T1 (traces_r P M)"
by (simp add: HC_T1_def traces_r_not_empty traces_r_prefix_closed)

lemma traces_r_domT [intro!]:
  "traces_r P M : domT"
apply(simp add: domT_def traces_r_HC_T1)
done

definition traces :: "('p, 'a) proc => ('p => 'a domT) => 'a domT" where
  "traces p M = Abs_domT (traces_r p M)"

definition F :: "('p => ('p, 'a) proc) => ('p => 'a domT) => ('p => 'a domT)" where
"F = (%D. %M. %p. traces (D p) M)"

lemma domT_Abs_mono: "[| x <= y; x : domT; y : domT |] ==> Abs_domT x <= Abs_domT y"
by (metis Abs_domT_inverse domT_less_eq_def)

lemma mono_STOP: "mono (traces STOP)"
apply(unfold mono_def traces_def)
by (metis bot_least domT_bot_def traces_r.simps(1))

lemma mono_prefix: "mono (traces P) ==> mono (traces (a -> P))"
apply(unfold mono_def traces_def)
apply(clarsimp)
apply(rule domT_Abs_mono)
apply(clarsimp)
apply(drule_tac x="x" in spec)
apply(drule_tac x="y" in spec)
apply(clarsimp)
apply(unfold domT_less_eq_def)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(subst Abs_domT_inverse)
apply(rule traces_r_domT)
apply(subst Abs_domT_inverse)
apply(rule traces_r_domT)
apply(erule contrapos_nn)
apply (metis in_mono)
apply(unfold domT_def)
apply(clarsimp)
apply(subgoal_tac "HC_T1 (traces_r (a -> P) x)")
apply(clarsimp)
apply(rule traces_r_HC_T1)
apply(clarsimp)
apply(subgoal_tac "HC_T1 (traces_r (a -> P) y)")
apply(clarsimp)
apply(rule traces_r_HC_T1)
done

lemma mono_prefix_choice: "(ALL x. mono (traces (Pf x))) ==> mono (traces (? :X -> Pf))"
apply(unfold mono_def traces_def)
apply(clarsimp)
apply(rule domT_Abs_mono)
apply(clarsimp)
apply (metis Abs_domT_inverse domT_def domT_less_eq_def in_mono traces_r_domT)
apply(subgoal_tac "traces_r (? :X -> Pf) x : domT")
apply(clarsimp)
apply(rule traces_r_domT)
apply(subgoal_tac "traces_r (? :X -> Pf) y : domT")
apply(clarsimp)
apply(rule traces_r_domT)
done

lemma mono_ext_choice: "[| mono (traces P); mono (traces Q) |]
 ==> mono (traces (P [+] Q))"
apply(unfold mono_def traces_def)
apply(clarsimp)
apply(rule domT_Abs_mono)
apply(clarsimp)
apply(drule_tac x="x" in spec)
apply(drule_tac x="x" in spec)
apply(drule_tac x="y" in spec)
apply(drule_tac x="y" in spec)
apply(clarsimp)
apply (metis Abs_domT_inverse domT_less_eq_def le_supI1 le_supI2 traces_r_domT)
apply(subgoal_tac "traces_r P x : domT & traces_r Q x : domT")
apply(clarsimp)
apply (metis traces_r.simps(4) traces_r_domT)
apply(blast)
apply(subgoal_tac "traces_r P y : domT & traces_r Q y : domT")
apply(clarsimp)
apply (metis traces_r.simps(4) traces_r_domT)
apply(blast)
done

lemma mono_int_choice: "[| mono (traces P); mono (traces Q) |]
 ==> mono (traces (P |~| Q))"
apply(unfold mono_def traces_def)
apply(clarsimp)
apply(rule domT_Abs_mono)
apply(clarsimp)
apply(drule_tac x="x" in spec)
apply(drule_tac x="x" in spec)
apply(drule_tac x="y" in spec)
apply(drule_tac x="y" in spec)
apply(clarsimp)
apply (metis Abs_domT_inverse domT_less_eq_def le_supI1 le_supI2 traces_r_domT)
apply(subgoal_tac "traces_r P x : domT & traces_r Q x : domT")
apply(clarsimp)
apply (metis traces_r.simps(4) traces_r_domT)
apply(blast)
apply(subgoal_tac "traces_r P y : domT & traces_r Q y : domT")
apply(clarsimp)
apply (metis traces_r.simps(4) traces_r_domT)
apply(blast)
done

lemma mono_rep_int_choice:
  "(ALL x. mono (traces (Pf x))) ==> mono (traces (!! :A .. Pf))"
apply(unfold mono_def traces_def)
apply(clarsimp)
apply(rule domT_Abs_mono)
apply(clarsimp)
apply (metis Abs_domT_inverse domT_def domT_less_eq_def in_mono traces_r_domT)
apply(subgoal_tac "traces_r (!! :A .. Pf) x : domT")
apply(clarsimp)
apply(rule traces_r_domT)
apply(subgoal_tac "traces_r (!! :A .. Pf) y : domT")
apply(clarsimp)
apply(rule traces_r_domT)
done

lemma mono_if: "[| mono (traces P); mono (traces Q) |]
 ==> mono (traces (IF b THEN P ELSE Q))"
apply(unfold mono_def traces_def)
apply(clarsimp)
done

lemma mono_par: "[| mono (traces P); mono (traces Q) |]
 ==> mono (traces (P |[X]| Q))"
apply(unfold mono_def traces_def)
apply(clarsimp)
apply(rule domT_Abs_mono)
apply(clarsimp)
apply(drule_tac x="x" in spec)
apply(drule_tac x="x" in spec)
apply(drule_tac x="y" in spec)
apply(drule_tac x="y" in spec)
apply(clarsimp)
apply (metis Abs_domT_inverse domT_def domT_less_eq_def in_mono traces_r_domT)
apply(subgoal_tac "traces_r (P |[X]| Q) x : domT")
apply(clarsimp)
apply(rule traces_r_domT)
apply(subgoal_tac "traces_r (P |[X]| Q) y : domT")
apply(clarsimp)
apply(rule traces_r_domT)
done

lemma mono_hide: "mono (traces P) ==> mono (traces (P -- X))"
apply(unfold mono_def traces_def)
apply(clarsimp)
apply(rule domT_Abs_mono)
apply(clarsimp)
apply (metis Abs_domT_cases Abs_domT_inverse domT_less_eq_def in_mono traces_r_domT)
apply(subgoal_tac "traces_r (P -- X) x : domT")
apply(clarsimp)
apply(rule traces_r_domT)
apply(subgoal_tac "traces_r (P -- X) y : domT")
apply(clarsimp)
apply(rule traces_r_domT)
done

lemma mono_rename: "mono (traces P) ==> mono (traces (P[[R]]))"
apply(unfold mono_def traces_def)
apply(clarsimp)
apply(rule domT_Abs_mono)
apply(clarsimp)
apply (metis Abs_domT_cases Abs_domT_inverse domT_less_eq_def in_mono traces_r_domT)
apply(subgoal_tac "traces_r (P[[R]]) x : domT")
apply(clarsimp)
apply(rule traces_r_domT)
apply(subgoal_tac "traces_r (P[[R]]) y : domT")
apply(clarsimp)
apply(rule traces_r_domT)
done

lemma mono_pn: "mono (traces ($p))"
apply(unfold mono_def traces_def)
apply(clarsimp)
by (metis Rep_domT_inverse le_fun_def)

lemma mono_traces: "ALL p. mono (traces p)"
apply(rule allI)
apply(induct_tac p)
apply(rule mono_STOP)
apply(erule mono_prefix)
apply(erule mono_prefix_choice[rule_format])
apply(erule mono_ext_choice)
apply(assumption)
apply(erule mono_int_choice)
apply(assumption)
apply(rule mono_rep_int_choice)
apply(clarsimp)
apply(erule mono_if)
apply(assumption)
apply(erule mono_par)
apply(assumption)
apply(erule mono_hide)
apply(erule mono_rename)
apply(rule mono_pn)
done

lemma mono_csp: "mono (F D)"
apply(unfold mono_def)
apply(unfold F_def)
apply(unfold le_fun_def)
apply(clarsimp)
apply(insert mono_traces)
apply(drule_tac x="D xa" in spec)
apply(unfold mono_def)
apply(rotate_tac -1)
apply(drule_tac x="x" in spec)
apply(rotate_tac -1)
apply(drule_tac x="y" in spec)
apply(drule mp)
apply (metis le_fun_def)
by metis

definition deno_sem :: "('p => ('p, 'a) proc) => ('p => 'a domT)" where
"deno_sem D = lfp (F D)"


(*********************  OPERATIONAL SEMANTICS  ***********************)


datatype 'a event = Tau | Ev 'a

inductive_set
  ptrans :: "('p => ('p, 'a) proc) => (('p, 'a) proc * 'a event * ('p, 'a) proc) set"
  for D :: "'p => ('p, 'a) proc"
  where
ptrans_prefix: "(a -> P, (Ev a, P)) : ptrans D" |
ptrans_prefix_choice: "a : A ==> (? :A -> Pf, (Ev a, Pf a))  : ptrans D" |
ptrans_ext_choice1: "(P, (Ev e, P')) : ptrans D
                      ==> (P [+] Q, (Ev e, P')) : ptrans D" |
ptrans_ext_choice2: "(Q, (Ev e, Q')) : ptrans D
                      ==> (P [+] Q, (Ev e, Q')) : ptrans D" |
ptrans_ext_choice3: "(P, (Tau, P')) : ptrans D
                      ==> (P [+] Q, (Tau, P' [+] Q)) : ptrans D" |
ptrans_ext_choice4: "(Q, (Tau, Q')) : ptrans D
                      ==> (P [+] Q, (Tau, P [+] Q')) : ptrans D" |
ptrans_int_choce1 [intro!]:
  "(P |~| Q, Tau, P) : ptrans D" |
ptrans_int_choce2 [intro!]:
  "(P |~| Q, Tau, Q) : ptrans D" |
ptrans_rep_int_choce:
  "x:A ==> (!! :A .. Pf, Tau, Pf x) : ptrans D" |
ptrans_par1: "[| (P, (Ev e, P')) : ptrans D; e ~: X |]
                  ==> (P |[X]| Q, (Ev e, P' |[X]| Q)) : ptrans D" |
ptrans_par2: "[| (Q, (Ev e, Q')) : ptrans D; e ~: X |]
                  ==> (P |[X]| Q, (Ev e, P |[X]| Q')) : ptrans D" |
ptrans_par3: "[| (P, (Ev e, P')) : ptrans D;
                (Q, (Ev e, Q')) : ptrans D; e : X |]
                  ==> (P |[X]| Q, (Ev e, P' |[X]| Q')) : ptrans D" |
ptrans_par4: "[| (P, (Tau, P')) : ptrans D |]
                  ==> (P |[X]| Q, (Tau, P' |[X]| Q)) : ptrans D" |
ptrans_par5: "[| (Q, (Tau, Q')) : ptrans D |]
                  ==> (P |[X]| Q, (Tau, P |[X]| Q')) : ptrans D" |
ptrans_hide1: "[| (P, (Ev e, P')) : ptrans D; e ~: X |]
                  ==> (P -- X, (Ev e, P' -- X)) : ptrans D" |
ptrans_hide2: "[| (P, (Ev e, P')) : ptrans D; e : X |]
                  ==> (P -- X, (Tau, P' -- X)) : ptrans D" |
ptrans_hide3: "[| (P, (Tau, P')) : ptrans D |]
                  ==> (P -- X, (Tau, P' -- X)) : ptrans D" |
ptrans_rename1: "[| (P, Ev a, P') : ptrans D; (a, b) : R |]
                 ==> (P[[R]], Ev b, P'[[R]]) : ptrans D" |
ptrans_rename2: "(P, Tau, P') : ptrans D
                 ==> (P[[R]], Tau, P'[[R]]) : ptrans D" |
ptrans_if1: "b ==> (IF b THEN P ELSE Q, Tau, P) : ptrans D" |
ptrans_if2: "~b ==> (IF b THEN P ELSE Q, Tau, Q) : ptrans D" |
ptrans_pn: "(D p, u, Q) : ptrans D
   ==> ($p, Tau, D p) : ptrans D"

inductive_cases ptrans_cases_STOP: "(STOP, u, P') : ptrans D"
inductive_cases ptrans_cases_prefix: "(a -> P, u, P') : ptrans D"
inductive_cases ptrans_cases_prefix_choice:
  "(? :A -> Pf, u, P') : ptrans D"
inductive_cases ptrans_cases_ext_choice:
  "(P [+] Q, u, P') : ptrans D"
inductive_cases ptrans_cases_int_choice:
  "(P |~| Q, u, P') : ptrans D"
inductive_cases ptrans_cases_rep_int_choice:
  "(!! :A .. Pf, u, P') : ptrans D"
inductive_cases ptrans_cases_par:
  "(P |[X]| Q, u, P') : ptrans D"
inductive_cases ptrans_cases_hide:
  "(P -- X, u, P') : ptrans D"
inductive_cases ptrans_cases_rename:
  "(P[[R]], u, P') : ptrans D"
inductive_cases ptrans_cases_if:
  "(IF b THEN P ELSE Q, u, P') : ptrans D"
inductive_cases ptrans_cases_pn:
  "($p, u, P') : ptrans D"

primrec ptel :: "nat => ('p, 'a) proc => ('p * nat, 'a) proc" where
  "ptel m STOP = STOP" |
  "ptel m (a->P) = a->(ptel m P)" |
  "ptel m (?:A->Pf) = (?:A->(%a. ptel m (Pf a)))" |
  "ptel m (P[+]Q) = (ptel m P)[+](ptel m Q)" |
  "ptel m (P|~|Q) = (ptel m P)|~|(ptel m Q)" |
  "ptel m (!!:A..Pf) = (!!:A..(%a. ptel m (Pf a)))" |
  "ptel m (P|[X]|Q) = (ptel m P) |[X]| (ptel m Q)" |
  "ptel m (P--X) = (ptel m P)--X" |
  "ptel m (P[[R]]) = (ptel m P)[[R]]" |
  "ptel m (IF b THEN P ELSE Q) = (IF b THEN (ptel m P) ELSE (ptel m Q))" |
  "ptel m ($p) = $(p, m)"

primrec rmtel :: "('p * nat, 'a) proc => ('p, 'a) proc" where
  "rmtel STOP = STOP" |
  "rmtel (a->P) = a->(rmtel P)" |
  "rmtel (?:A->Pf) = (?:A->(%a. rmtel (Pf a)))" |
  "rmtel (P[+]Q) = (rmtel P)[+](rmtel Q)" |
  "rmtel (P|~|Q) = (rmtel P)|~|(rmtel Q)" |
  "rmtel (!!:A..Pf) = (!!:A..(%a. rmtel (Pf a)))" |
  "rmtel (P|[X]|Q) = (rmtel P) |[X]| (rmtel Q)" |
  "rmtel (P--X) = (rmtel P)--X" |
  "rmtel (P[[R]]) = (rmtel P)[[R]]" |
  "rmtel (IF b THEN P ELSE Q) = (IF b THEN (rmtel P) ELSE (rmtel Q))" |
  "rmtel ($pm) = ($(fst pm))"

lemma rmtel_ptel [intro, simp]: "rmtel (ptel m P) = P"
apply(induct_tac P)
apply(auto)
done

primrec ptelset :: "('p * nat, 'a) proc => nat set" where
  "ptelset STOP = {}" |
  "ptelset (a->P) = ptelset P" |
  "ptelset (?:A->Pf) = Union {x. EX a. x = ptelset (Pf a)}" |
  "ptelset (P[+]Q) = (ptelset P) Un (ptelset Q)" |
  "ptelset (P|~|Q) = (ptelset P) Un (ptelset Q)" |
  "ptelset (!!:A..Pf) = Union {x. EX a. x = ptelset (Pf a)}" |
  "ptelset (P|[X]|Q) = (ptelset P) Un (ptelset Q)" |
  "ptelset (P--X) = (ptelset P)" |
  "ptelset (P[[R]]) = (ptelset P)" |
  "ptelset (IF b THEN P ELSE Q) = (ptelset P) Un (ptelset Q)" |
  "ptelset ($pm) = {snd pm}"

lemma ptelset_ptel [intro]: "ptelset (ptel m P) <= {m}"
apply(induct_tac P)
apply(auto)
done

definition pbound :: "('p * nat, 'a) proc => bool" where
  "pbound P = finite (ptelset P)"

definition G :: "('p => ('p, 'a) proc) => (('p * nat) => ('p * nat, 'a) proc)" where
  "G D = (%(p, n). if n=0 then STOP else ptel (n - 1) (D p))"

inductive_set
  comps :: "('p => ('p, 'a) proc) => (('p, 'a) proc * 'a event * ('p, 'a) proc) list set"
  for D :: "'p => ('p, 'a) proc"
  where
comps_base [simp, intro!]: "[] : comps D" |
comps_step1 [intro!]: "[| (P, u, P') : ptrans D |]
                 ==> [(P, u, P')] : comps D" |
comps_step2: "[| (P, u, P')#cs : comps D; (P'', u', P) : ptrans D |]
                 ==> (P'', u', P)#(P, u, P')#cs : comps D"

fun comp_to_trace :: "('q * 'a event * 'q) list => 'a list" where
  "comp_to_trace [] = []"
| "comp_to_trace ((P, Tau, P')#cs) = comp_to_trace cs"
| "comp_to_trace ((P, Ev e, P')#cs) = e # (comp_to_trace cs)"

definition otraces_r :: "('p => ('p, 'a) proc) => ('p, 'a) proc => 'a list set" where
  "otraces_r D P =
         {tr. tr = [] | (EX P' u cs. tr = comp_to_trace ((P, u, P')#cs) &
                                     (P, u, P')#cs : comps D)}"

definition otraces :: "('p => ('p, 'a) proc) => ('p, 'a) proc => 'a domT" where
  "otraces D P = Abs_domT (otraces_r D P)"

lemma div_no_trans0 [rule_format]:
  "(P, u, Q) : ptrans D ==> ALL p. P = D p | P = $p --> D p ~= $p"
apply(erule ptrans.induct)
apply(auto)
done

lemma div_no_trans: "(D p, u, Q) : ptrans D ==> D p ~= $p"
apply(drule_tac p="p" in div_no_trans0)
apply(auto)
done

lemma pn_trans:
  "($p, u, Q) : ptrans D ==> D p ~= $p"
apply(erule ptrans_cases_pn)
apply(erule div_no_trans)
done

lemma comps_car:
  "(P, u, P')#cs : comps D
    ==> (P, u, P') : ptrans D"
apply(erule comps.cases)
apply(auto)
done

lemma traces_r_div:
  "D p = $p ==> otraces_r D ($p) = {[]}"
apply(unfold otraces_r_def)
apply(rule subset_antisym)
apply(auto)
apply(drule comps_car)
apply(drule pn_trans)
apply(clarsimp)
done

lemma [intro!]: "[] : otraces_r D P"
apply(unfold otraces_r_def)
apply(auto)
done

lemma Abs_domT_D : "[| Abs_domT A <= Abs_domT B; A : domT; B : domT |] ==> A <= B"
apply(erule contrapos_pp)
apply(subst domT_less_eq_def)
apply(subst Abs_domT_inverse)
apply(assumption)
apply(subst Abs_domT_inverse)
apply(assumption)
apply(assumption)
done

lemma Abs_domT_I : "[| A <= B; A : domT; B : domT |] ==> Abs_domT A <= Abs_domT B"
by (metis domT_Abs_mono)

lemma comps_cdr:
  "x#cs : comps D ==> cs : comps D"
apply(erule comps.cases)
apply(auto)
done

lemma comps_connect:
  "(P, u, Q) # (Q', u', R) # cs : comps D
  ==> Q = Q'"
apply(erule comps.cases)
apply(auto)
done

lemma comps_app [rule_format]:
  "ALL cs1. cs0 @ cs1 : comps D
     --> cs0 : comps D & cs1 : comps D"
apply(induct_tac cs0)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(frule comps_car)
apply(case_tac list)
apply(clarsimp)
apply(clarsimp)
apply(drule comps_connect)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(assumption)
done

lemma comps_app_D1:
  "xs @ ys : comps D ==> xs : comps D"
apply(drule comps_app)
apply(auto)
done

lemma comps_app_D2:
  "xs @ ys : comps D ==> ys : comps D"
apply(drule comps_app)
apply(auto)
done

lemma comps_ex_head:
 "[| (P, u, P')#cs : comps D;
          (Q, u', P') : ptrans D |]
  ==> (Q, u', P')#cs : comps D"
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(rule comps_step2)
apply(erule comps_cdr)
apply(assumption)
done

lemma comps_prefix0:
  "ALL D cs n. cs : comps D
     --> n <= length cs --> take n cs : comps D"
apply(rule allI)
apply(rule allI)
apply(induct_tac cs)
apply(auto)
apply (metis comps_cdr)
by (metis append_take_drop_id comps_app)

lemma otrace_prefix [rule_format]:
  "cs : comps D ==>
  ALL s t. prefix s t -->
  t = comp_to_trace cs  -->
  (EX cs0 cs1. cs0 @ cs1 = cs & s = comp_to_trace cs0)"
apply(erule comps.induct)
apply(auto)
apply(case_tac u)
apply(clarsimp)
apply (metis append_Nil comp_to_trace.simps(1))
apply(clarsimp)
apply(case_tac s)
apply(clarsimp)
apply (metis append_Nil comp_to_trace.simps(1))
apply(clarsimp)
apply(unfold prefix_def)
apply(clarsimp)
apply (metis append_Nil2 comp_to_trace.simps(1) comp_to_trace.simps(3))
apply(clarsimp)
apply(case_tac u')
apply(clarsimp)
apply(drule_tac x="s" in spec)
apply(clarsimp)
apply(rule_tac x="(P'', Tau, P)#cs0" in exI)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(case_tac s)
apply(clarsimp)
apply (metis append_Nil comp_to_trace.simps(1))
apply(clarsimp)
apply(drule_tac x="list" in spec)
apply(clarsimp)
apply(rule_tac x="(P'', Ev aa, P)#cs0" in exI)
apply(clarsimp)
apply(metis)
done

lemma otraces_prefix_closed: "prefix_closed (otraces_r D proc)"
apply(unfold prefix_closed_def otraces_r_def)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac 1)
apply(erule contrapos_pp)
apply(simp)
apply(frule otrace_prefix)
apply(assumption)
apply(simp)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="P'" in exI)
apply(rule_tac x="u" in exI)
apply(rule_tac x="list" in exI)
apply(clarsimp)
by (metis append_Cons comps_app)

lemma otraces_domT: "otraces_r D p : domT"
apply(simp add: domT_def HC_T1_def)
apply(rule conjI)
apply(simp add: otraces_r_def)
apply metis
apply(rule otraces_prefix_closed)
done

(*****************  comp_conn  **************************)

fun comp_conn_p :: "('p => ('p, 'a) proc)
  => (('p, 'a) proc * 'a event * ('p, 'a) proc) list
  => (('p, 'a) proc * 'a event * ('p, 'a) proc) list => bool" where
  "comp_conn_p D [] [] = True"
| "comp_conn_p D [] ((Q, u, Q')#qs) = True"
| "comp_conn_p D ((P, u, P')#ps) [] = True"
| "comp_conn_p D ((P, u, P')#ps) ((Q, u', Q')#qs) = (P' = Q)"

definition comp_conn :: "('p => ('p, 'a) proc)
  => (('p, 'a) proc * 'a event * ('p, 'a) proc) list
  => (('p, 'a) proc * 'a event * ('p, 'a) proc) list => bool" where
  "comp_conn D ps qs = comp_conn_p D (rev ps) qs"

lemma [simp, intro!]: "comp_conn_p D [] qs"
apply(case_tac qs)
apply(auto)
done

lemma [simp, intro!]: "comp_conn_p D ps []"
apply(case_tac ps)
apply(auto)
done

lemma [simp, intro!]: "comp_conn D [] qs"
apply(unfold comp_conn_def)
apply(simp)
done

lemma [simp, intro!]: "comp_conn D ps []"
apply(unfold comp_conn_def)
apply(simp)
done

lemma comp_conn_p_add_tail [rule_format]:
  "ALL ps qs x. comp_conn_p D ps qs --> ps ~= [] --> comp_conn_p D (ps@[x]) qs"
apply(rule allI)
apply(induct_tac ps)
apply(clarsimp)
apply(clarsimp)
apply(case_tac qs)
apply(clarsimp)
apply(clarsimp)
done

lemma comp_conn_p_remove_tail [rule_format]:
  "ALL ps qs x. comp_conn_p D (ps@[x]) qs --> comp_conn_p D ps qs"
apply(rule allI)
apply(induct_tac ps)
apply(clarsimp)
apply(clarsimp)
apply(case_tac qs)
apply(clarsimp)
apply(clarsimp)
done

lemma comp_conn_Cons:
  "comp_conn D (p#ps) qs ==> comp_conn D ps qs"
apply(unfold comp_conn_def)
apply(rule comp_conn_p_remove_tail)
apply(clarsimp)
apply(assumption)
done

lemma comp_conn_add_head:
  "[| comp_conn D ps qs; ps ~= [] |] ==> comp_conn D (x#ps) qs"
apply(unfold comp_conn_def)
apply(subgoal_tac "comp_conn_p D ((rev ps) @ [x]) qs")
apply(clarsimp)
apply(rule comp_conn_p_add_tail)
apply(clarsimp)
apply(clarsimp)
done

lemma comp_conn_conn:
  "comp_conn D [(P, u, P')] ((Q, v, Q')#qs)
    ==> P' = Q"
apply(unfold comp_conn_def)
apply(clarsimp)
done

lemma comps_app_conn [rule_format]:
  "ALL ys. xs @ ys : comps D --> comp_conn D xs ys"
apply(induct_tac xs)
apply(unfold comp_conn_def)
apply(clarsimp)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(case_tac ys)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_cdr)
apply(drule_tac x="ys" in spec)
apply(clarsimp)
apply(drule_tac x="(a, aa, ab)" in comp_conn_p_add_tail)
apply(clarsimp)
apply(clarsimp)
done

lemma comps_conn_app [rule_format]:
  "ALL ps qs.
    ps : comps D -->
    qs : comps D -->
    comp_conn D ps qs -->
    ps @ qs : comps D"
apply(rule allI)
apply(induct_tac ps)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(clarsimp)
apply(drule_tac x="qs" in spec)
apply(clarsimp)
apply(frule comp_conn_Cons)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(case_tac qs)
apply(clarsimp)
apply(clarsimp)
apply(drule comp_conn_conn)
apply(clarsimp)
apply(erule comps_step2)
apply(erule comps_car)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(drule comps_car)
apply(erule comps_step2)
apply(assumption)
done

lemma comp_conn_Cons2: "comp_conn D ps (q#qs) ==> comp_conn D ps [q]"
apply(unfold comp_conn_def)
apply(case_tac "rev ps")
apply(clarsimp)
apply(clarsimp)
apply(case_tac q)
apply(clarsimp)
done

lemma comp_conn_map [rule_format]:
  "ALL Q Q' Q'' v w f.
  comp_conn D cs [(Q, v, Q')] -->
  comp_conn D (map (%(P, u, P'). (f P, u, f P')) cs) ((f Q, w, Q'')#cs')"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comp_conn_Cons)
apply(drule_tac x="Q" in spec)
apply(drule mp)
apply(rule_tac x="Q'" in exI)
apply(rule_tac x="v" in exI)
apply(assumption)
apply(drule_tac x="Q''" in spec)
apply(drule_tac x="w" in spec)
apply(drule_tac x="f" in spec)
apply(case_tac list)
apply(clarsimp)
apply(unfold comp_conn_def)
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac -1)
apply(drule_tac x="(f a, aa, f b)" in comp_conn_p_add_tail)
apply(clarsimp)
apply(clarsimp)
done

lemma comp_connI:
  "P' = Q ==> comp_conn D [(P, u, P')] ((Q, v, Q')#cs)"
apply(unfold comp_conn_def)
apply(auto)
done

lemma comp_conn_map0 [rule_format]:
  "comp_conn D ps qs -->
   comp_conn D (map (%(p, u, q). (f p, u, f q)) ps)
             (map (%(p, u, q). (f p, u, f q)) qs)"
apply(induct_tac ps)
apply(clarsimp)
apply(clarsimp)
apply(frule comp_conn_Cons)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(case_tac qs)
apply(clarsimp)
apply(clarsimp)
apply(frule comp_conn_conn)
apply(clarsimp)
apply(rule comp_connI)
apply(clarsimp)
apply(clarsimp)
apply(erule comp_conn_add_head)
apply(clarsimp)
done

lemma [intro]: "x#cs : comps D ==> comp_conn D [x] cs"
by (metis append_Cons append_Nil comps_app_conn)

(***********************************************************************)

lemma traces_otraces_1_STOP:
  "traces STOP (%p. otraces D ($p)) <= otraces D STOP"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(unfold otraces_r_def)
apply(clarsimp)
done

lemma comp_to_trace_app[simp, rule_format]:
  "ALL y. comp_to_trace (x @ y) = comp_to_trace x @ comp_to_trace y"
apply(induct_tac x)
apply(auto)
apply(case_tac aa)
apply(clarsimp)
apply(clarsimp)
done

lemma traces_otraces_1_prefix:
  "traces proc (%p. otraces D ($p)) <= otraces D proc
     ==> traces (a -> proc) (%p. otraces D ($p)) <= otraces D (a -> proc)"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
(**)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(clarsimp)
apply(drule subsetD)
apply(assumption)
apply(unfold otraces_r_def)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="proc" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule ptrans_prefix)
(**)
apply(clarsimp)
apply(rule_tac x="proc" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="(proc, u, P')#cs" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(rule ptrans_prefix)
done

lemma traces_otraces_1_prefix_choice:
  "ALL a:A. traces (Pf a) (%p. otraces D ($p)) <= otraces D (Pf a)
       ==> traces (? :A -> Pf) (%p. otraces D ($p)) <= otraces D (? :A -> Pf)"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
(**)
apply(rule subsetI)
apply(subst otraces_r_def)
apply(clarsimp)
apply(drule_tac x="a" in bspec)
apply(assumption)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(erule contrapos_pp)
apply(simp)
apply(drule subsetD)
apply(assumption)
apply(unfold otraces_r_def)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="Pf a" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply (metis (no_types, hide_lams) ptrans.ptrans_prefix_choice)
(**)
apply(clarsimp)
apply(rule_tac x="Pf a" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="(Pf a, u, P')#cs" in exI)
apply(clarsimp)
by (metis (no_types, hide_lams) comps.comps_step2 ptrans.ptrans_prefix_choice)

lemma non_nil_comp_to_trace:
  "a#tr = comp_to_trace cs
 --> (EX cs0 cs1 P Q. cs = cs0 @ [(P, Ev a, Q)] @ cs1 &
                      (ALL i. i < length cs0 --> fst (snd (cs0!i)) = Tau) &
                      tr = comp_to_trace cs1)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac aaa)
apply(clarsimp)
apply(rule_tac x="(aa, Tau, b)#cs0" in exI)
apply(rule_tac x="cs1" in exI)
apply(rule conjI)
apply(rule_tac x="P" in exI)
apply(rule_tac x="Q" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis One_nat_def diff_Suc_Suc diff_zero fst_conv gr0_conv_Suc less_Suc_eq_0_disj nth.simps nth_Cons_pos nth_non_equal_first_eq old.nat.distinct(2) snd_conv)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="list" in exI)
apply(rule conjI)
apply(rule_tac x="aa" in exI)
apply(rule_tac x="b" in exI)
apply(clarsimp)
apply(clarsimp)
done

lemma non_nil_comp_to_trace_forall:
  "a#tr = comp_to_trace cs
 ==> (EX cs0 cs1 P Q. cs = cs0 @ [(P, Ev a, Q)] @ cs1 &
                      (forall (%(P, u, Q). u=Tau) cs0) &
                      comp_to_trace cs1 = tr)"
apply(drule non_nil_comp_to_trace[rule_format])
apply(clarsimp)
apply(rule_tac x="cs0" in exI)
apply(rule_tac x="cs1" in exI)
apply(safe)
apply(rule_tac x="P" in exI)
apply(rule_tac x="Q" in exI)
apply(simp)
apply(rule_tac n="length cs0" in forall_scanI)
apply(clarsimp)
apply (metis fst_conv snd_conv)
apply(simp)
done

lemma comp_to_trace_tau:
  "(ALL i< length cs. fst (snd (cs ! i)) = Tau) --> comp_to_trace cs = []"
apply(induct_tac cs)
apply(auto)
done

lemma comupations_ext_choce_tau_seq:
  "ALL cs P Q2 a Q3 cs1 D.
cs @ (Q2, Ev a, Q3) # cs1 : comps D -->
  (ALL i< length cs. fst (snd (cs ! i)) = Tau) -->
  map (%(p, u, q). (P [+] p, Tau, P [+] q)) cs @
  (P [+] Q2, Ev a, Q3) # cs1
  : comps D"
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(induct_tac cs)
apply(clarsimp)
apply(erule comps.cases)
apply(clarsimp)
apply(clarsimp)
apply (metis ptrans.ptrans_ext_choice2)
apply(clarsimp)
apply(erule comps_step2)
apply (metis ptrans.ptrans_ext_choice2)
(**)
apply(clarsimp)
apply(frule comps_cdr)
apply(clarsimp)
apply(drule mp)
apply(clarsimp)
apply (metis Suc_less_eq nth_Cons_Suc)
apply(case_tac list)
apply(clarsimp)
apply(rotate_tac -1)
apply(frule comps_connect)
apply(clarsimp)
apply (metis comps.comps_step2 comps_car ptrans.ptrans_ext_choice4)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(erule comps_step2)
apply(drule comps_car)
by (metis fst_conv nth_Cons_0 ptrans.ptrans_ext_choice4 snd_conv zero_less_Suc)

lemma comps_ext_choce_tau_seq2:
  "ALL cs P Q2 a Q3 cs1 D.
cs @ (Q2, Ev a, Q3) # cs1 : comps D -->
  (ALL i< length cs. fst (snd (cs ! i)) = Tau) -->
  map (%(p, u, q). (p [+] P, Tau, q [+] P)) cs @
  (Q2 [+] P, Ev a, Q3) # cs1
  : comps D"
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(induct_tac cs)
apply(clarsimp)
apply(erule comps.cases)
apply(clarsimp)
apply(clarsimp)
apply (metis ptrans.ptrans_ext_choice1)
apply(clarsimp)
apply(erule comps_step2)
apply (metis ptrans.ptrans_ext_choice1)
(**)
apply(clarsimp)
apply(frule comps_cdr)
apply(case_tac list)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_cdr)
apply(rule comps_step2)
apply(simp)
apply (metis comps_car ptrans.ptrans_ext_choice3)
apply(clarsimp)
apply(drule mp)
apply(clarsimp)
apply (metis Suc_less_eq nth_Cons_Suc)
apply(frule comps_connect)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(drule comps_car)
by (metis fst_conv nth_Cons_0 ptrans.ptrans_ext_choice3 snd_conv zero_less_Suc)

lemma comps_tau_seq [rule_format]:
  "cs : comps D ==>
  (forall (%(p, u, q). u=Tau) cs) -->
  (ALL p q. (p, Tau, q) : ptrans D --> (f p, Tau, f q) : ptrans D) -->
  (map (%(p, u, q). (f p, u, f q)) cs) : comps D"
apply(erule comps.induct)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
by metis

lemma comp_to_trace_map_tau [rule_format]:
  "forall (%(p, u, q). u=Tau) cs -->
   (ALL p q. (p, Tau, q) : ptrans D --> (f p, Tau, f q) : ptrans D)
  --> comp_to_trace (map (%(p, u, q). (f p, u, f q)) cs) = []"
apply(induct_tac cs)
apply(auto)
done

lemma comp_to_trace_map_tau1:
  "forall (%(p, u, q). u=Tau) cs
  ==> comp_to_trace (map (%(p, u, q). (P [+] p, u, P [+] q)) cs) = []"
apply(erule comp_to_trace_map_tau)
by (metis ptrans.ptrans_ext_choice4)

lemma comp_to_trace_map_tau2:
  "forall (%(p, u, q). u=Tau) cs
  ==> comp_to_trace (map (%(p, u, q). (p [+] P, u, q [+] P)) cs) = []"
apply(erule comp_to_trace_map_tau)
by (metis ptrans.ptrans_ext_choice3)

lemma comps_car_app_D1:
  "(P, u, P') # cs @ (Q, v, Q') # cs' : comps D
  ==> (P, u, P') # cs : comps D"
apply(subgoal_tac "((P, u, P') # cs) @ ((Q, v, Q') # cs') : comps D")
apply(drule comps_app_D1)
apply(auto)
done

lemma comps_car_app_D2:
  "(P, u, P') # cs @ (Q, v, Q') # cs' : comps D
  ==> (Q, v, Q') # cs' : comps D"
apply(subgoal_tac "((P, u, P') # cs) @ ((Q, v, Q') # cs') : comps D")
apply(drule comps_app_D2)
apply(auto)
done

lemma comps_car_car_cdr:
  "(P, u, P') # cs @ (Q, v, Q') # cs' : comps D
  ==> (P, u, P') # cs @ [(Q, v, Q')] : comps D"
by (metis (erased, hide_lams) append_Cons append_Nil append_assoc comps_app_D1)

lemma otraces_r_ext_choice:
  "s : otraces_r D Q --> s : otraces_r D (P [+] Q)"
apply(unfold otraces_r_def)
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(simp)
apply(case_tac "comp_to_trace ((Q, u, P') # cs)")
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac 2)
apply(drule sym)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="Qa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="cs1" in exI)
apply(clarsimp)
apply (metis comps_car comps_ex_head ptrans.ptrans_ext_choice2)
(**)
apply(clarsimp)
apply(rule_tac x="P [+] b" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p, u, q). (P [+] p, u, P [+] q)) list)@(P [+] Pa, Ev a, Qa)#cs1" in exI)
apply(rule conjI)
apply(clarsimp)
apply(erule comp_to_trace_map_tau1)
apply(subgoal_tac
  "(map (%(p, u, q). (P [+] p, u, P [+] q)) ((Q,Tau,b)#list)) @
           (P [+] Pa, Ev a, Qa) # cs1
           : comps D")
apply(clarsimp)
apply(rule comps_conn_app)
apply(rule_tac f="(%x. P [+] x)" in comps_tau_seq)
apply(erule comps_car_app_D1)
apply(clarsimp)
apply(erule ptrans_ext_choice4)
apply(frule comps_car_app_D2)
apply(frule_tac P="Pa" in comps_car)
apply(erule comps_ex_head)
apply (metis ptrans.ptrans_ext_choice2)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(clarsimp)
apply(drule comps_car_car_cdr)
apply(assumption)
done

lemma otraces_r_ext_choice2:
  "s : otraces_r D P --> s : otraces_r D (P [+] Q)"
apply(unfold otraces_r_def)
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(simp)
apply(case_tac "comp_to_trace ((P, u, P') # cs)")
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac 2)
apply(drule sym)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="Qa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="cs1" in exI)
apply(clarsimp)
apply (metis comps_car comps_ex_head ptrans.ptrans_ext_choice1)
(**)
apply(clarsimp)
apply(rule_tac x="b [+] Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p, u, q). (p [+] Q, u, q [+] Q)) list)@(Pa [+] Q, Ev a, Qa)#cs1" in exI)
apply(rule conjI)
apply(clarsimp)
apply(erule comp_to_trace_map_tau2)
apply(subgoal_tac
  "(map (%(p, u, q). (p [+] Q, u, q [+] Q)) ((P,Tau,b)#list)) @
           (Pa [+] Q, Ev a, Qa) # cs1
           : comps D")
apply(clarsimp)
apply(rule comps_conn_app)
apply(rule_tac f="(%x. x [+] Q)" in comps_tau_seq)
apply(erule comps_car_app_D1)
apply(clarsimp)
apply(erule ptrans_ext_choice3)
apply(frule comps_car_app_D2)
apply(frule_tac P="Pa" in comps_car)
apply(erule comps_ex_head)
apply (metis ptrans.ptrans_ext_choice1)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(clarsimp)
apply(drule comps_car_car_cdr)
apply(assumption)
done

lemma comp_to_trace_eq_ev_seq:
  "ALL cs1.
  length cs0 = length cs1 -->
  (ALL i<length cs0. fst (snd (cs0!i)) = fst (snd (cs1!i))) -->
  comp_to_trace cs0 = comp_to_trace cs1"
apply(induct_tac cs0)
apply(auto)
apply(case_tac cs1)
apply(clarsimp)
apply(clarsimp)
apply(subgoal_tac "aa=ac")
apply(clarsimp)
apply(case_tac ac)
apply(clarsimp)
apply (metis Suc_less_eq nth_Cons_Suc)
apply(clarsimp)
apply (metis Suc_less_eq nth_Cons_Suc)
by (metis fst_conv nth_Cons_0 snd_conv zero_less_Suc)

lemma traces_otraces_1_ext_choice:
  "[| traces P (%p. otraces D ($p)) <= otraces D P;
  traces Q (%p. otraces D ($p)) <= otraces D Q |]
  ==> traces (P [+] Q) (%p. otraces D ($p)) <= otraces D (P [+] Q)"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
(**)
apply(rule subsetI)
apply(clarsimp)
apply(erule disjE)
apply(drule_tac subsetD)
apply(assumption)
apply(erule otraces_r_ext_choice2[rule_format])
(**)
apply(rotate_tac 1)
apply(drule_tac subsetD)
apply(assumption)
apply(erule otraces_r_ext_choice[rule_format])
done

lemma comp_to_trace_initial:
  "comp_to_trace ((P, u, R) # cs) = comp_to_trace ((Q, u, R) # cs)"
apply(induct_tac cs)
apply(case_tac u)
apply(auto)
apply(case_tac u)
apply(auto)
done

lemma otraces_if_true:
  "otraces_r D (IF True THEN P ELSE Q) = otraces_r D P"
apply(unfold otraces_r_def)
apply(auto)
apply(erule contrapos_pp)
apply(simp)
apply(frule comps_car)
apply(erule ptrans_cases_if)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply (metis comps_cdr)
(**)
apply(clarsimp)
apply(erule contrapos_pp)
apply(simp)
apply(rule_tac x="P" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="((P, u, P') # cs)" in exI)
apply(clarsimp)
by (metis comps.comps_step2 ptrans.ptrans_if1)

lemma otraces_if_false:
  "otraces_r D (IF False THEN P ELSE Q) = otraces_r D Q"
apply(unfold otraces_r_def)
apply(auto)
apply(erule contrapos_pp)
apply(simp)
apply(frule comps_car)
apply(erule ptrans_cases_if)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply (metis comps_cdr)
(**)
apply(erule contrapos_pp)
apply(simp)
apply(rule_tac x="Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="((Q, u, P') # cs)" in exI)
apply(clarsimp)
by (metis comps.comps_step2 ptrans.ptrans_if2)

lemma traces_otraces_1_if:
  "[| traces proc1 (%p. otraces D ($p)) <= otraces D proc1;
      traces proc2 (%p. otraces D ($p)) <= otraces D proc2 |]
  ==> traces (IF bool THEN proc1 ELSE proc2) (%p. otraces D ($p))
        <= otraces D (IF bool THEN proc1 ELSE proc2)"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
(**)
apply(case_tac bool)
apply(simp)
apply(subst otraces_if_true)
apply(assumption)
apply(simp)
apply(case_tac bool)
apply(clarsimp)
apply(subst otraces_if_false)
apply(clarsimp)
done

lemma comp_trace_tau_seq_par1:
  "ALL X P.
    (ALL i<length cs. fst (snd (cs ! i)) = Tau) -->
   comp_to_trace (map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) cs) = []"
apply(induct_tac cs)
apply(auto)
done

lemma comp_trace_tau_seq_par2:
  "ALL X P.
    (ALL i<length cs. fst (snd (cs ! i)) = Tau) -->
   comp_to_trace (map (%(p, u, q). (p |[X]| P, u, q |[X]| P)) cs) = []"
apply(induct_tac cs)
apply(auto)
done

lemma comps_tau_seq_par1_0:
  "ALL X P. 
     cs : comps D -->
     (ALL i<length cs. fst (snd (cs ! i)) = Tau | fst (snd (cs ! i)) ~: Ev ` X) -->
     map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) cs : comps D"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(frule comps_car)
apply(drule mp)
apply(clarsimp)
apply(drule_tac x="X" in spec)
apply(drule mp)
apply(clarsimp)
apply (metis Suc_mono event.distinct(1) imageI nth_Cons_Suc)
apply(drule_tac x="P" in spec)
apply(case_tac list)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply (metis ptrans.ptrans_par5)
apply(case_tac aa)
apply(clarsimp)
apply (metis ptrans.ptrans_par5)
apply(clarsimp)
apply (metis image_eqI ptrans.ptrans_par2)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(rule comps_step2)
apply(assumption)
apply(case_tac aa)
apply(clarsimp)
apply(erule ptrans_par5)
apply(clarsimp)
apply(erule ptrans_par2)
apply (metis (no_types, hide_lams) event.distinct(1) fst_conv image_eqI nth_Cons_0 snd_conv zero_less_Suc)
done

lemma comps_tau_seq_par1:
  "[| cs : comps D;
     (ALL i<length cs. fst (snd (cs ! i)) = Tau | fst (snd (cs ! i)) ~: Ev ` X) |]
  ==> map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) cs : comps D"
apply(rule comps_tau_seq_par1_0[rule_format])
apply(auto)
done

lemma comp_to_trace_nil0:
  "comp_to_trace cs = [] --> (ALL i<length cs. fst (snd (cs!i)) = Tau)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply (metis (erased, hide_lams) fst_conv less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc snd_conv)
apply(clarsimp)
done

lemma comp_to_trace_nil [rule_format]:
  "comp_to_trace cs = [] --> (ALL i<length cs. fst (snd (cs!i)) = Tau)"
apply(rule comp_to_trace_nil0)
done

lemma comp_to_trace_nil1:
  "comp_to_trace cs = [] ==> (ALL i<length cs. fst (snd (cs!i)) = Tau)"
apply(insert comp_to_trace_nil0)
apply(auto)
done

lemma comp_to_trace_map_tau_par1_0:
  "(ALL i<length cs. fst (snd (cs!i)) = Tau) -->
    comp_to_trace (map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) cs) = []"
apply(induct_tac cs)
apply(auto)
done

lemma comp_to_trace_map_tau_par1:
  "(ALL i<length cs. fst (snd (cs!i)) = Tau) ==>
    comp_to_trace (map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) cs) = []"
apply(insert comp_to_trace_map_tau_par1_0)
apply(auto)
done


lemma comp_to_trace_nil2 [rule_format]:
  "comp_to_trace cs = [] --> forall (%(P, u, Q). u = Tau) cs"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(clarsimp)
done

lemma comp_to_trace_set_disj_X:
  "set (comp_to_trace cs) Int X = {}
    --> (forall (%(P, u, Q). case u of Tau => True | Ev a => a ~: X) cs)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(clarsimp)
done

lemma comp_to_trace_map_tau_par2 [rule_format]:
  "(forall (%(P, u, Q). u = Tau) cs) -->
    comp_to_trace (map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) cs) = []"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
done

lemma comp_to_trace_map_tau_par2_2 [rule_format]:
  "(forall (%(P, u, P'). u = Tau) cs) -->
    comp_to_trace (map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) cs) = []"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
done

lemma comps_tau_seq_par1_1_0:
  "forall (%(P, u, P'). case u of Tau => True | Ev a => a ~: X) cs
  --> (ALL i < length cs. fst (snd (cs ! i)) = Tau | fst (snd (cs ! i)) ~: Ev ` X)"
apply(induct_tac cs)
apply(auto)
apply(case_tac aa)
apply(clarsimp)
apply(case_tac i)
apply(clarsimp)
apply(clarsimp)
apply (metis event.distinct(1) imageI)
apply(clarsimp)
apply(case_tac i)
apply(clarsimp)
apply(clarsimp)
by (metis event.distinct(1) imageI)

lemma comps_tau_seq_par1_1:
  "[| cs : comps D;
      forall (%(P, u, P'). case u of Tau => True | Ev a => a ~: X) cs |]
  ==> map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) cs : comps D"
apply(erule comps_tau_seq_par1_0[rule_format])
apply(rule comps_tau_seq_par1_1_0[rule_format])
apply(auto)
done

lemma comps_tau_seq_par1_2 [rule_format]:
  "cs : comps D ==>
  forall (%(P, u, P'). case u of Tau => True | Ev a => a ~: X) cs
  --> map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) cs : comps D"
apply(erule comps.induct)
apply(auto)
apply(case_tac u)
apply(auto)
apply (metis ptrans.ptrans_par4)
apply (metis ptrans.ptrans_par1)
apply(rule comps_step2)
apply(clarsimp)
apply(case_tac u')
apply(clarsimp)
apply (metis ptrans.ptrans_par4)
apply(clarsimp)
by (metis ptrans.ptrans_par1)

lemma comps_app_D_0 [rule_format]:
  "ALL ys P Q R u v.
      xs @ [(P, u, Q)] : comps D -->
      (Q, v, R) # ys : comps D -->
  xs @ (P, u, Q) # (Q, v, R) # ys : comps D"
apply(induct_tac xs)
apply(clarsimp)
apply(erule comps_step2)
apply (metis comps_car)
apply(clarsimp)
apply(drule_tac x="ys" in spec)
apply(drule_tac x="P" in spec)
apply(drule_tac x="Q" in spec)
apply(drule_tac x="R" in spec)
apply(drule_tac x="u" in spec)
apply(frule comps_car)
apply(frule comps_cdr)
apply(clarsimp)
apply(drule_tac x="v" in spec)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(rule comps_step2)
apply(assumption)
apply(assumption)
done

lemma otraces_r_interleave[rule_format]:
  "ALL P Q.
       t : otraces_r D Q -->
       set t Int X = {} -->
    t : otraces_r D (P |[X]| Q)"
apply(induct_tac t)
apply(clarsimp)
apply(clarsimp)
apply(unfold otraces_r_def)
apply(clarsimp)
apply(frule non_nil_comp_to_trace_forall)
apply(clarsimp)
(****)
(*
to use the hypothesis
 comp_to_trace cs1 = comp_to_trace ((Q, u, P') # cs) 
is needed. try to create this from
    a # comp_to_trace cs1 = comp_to_trace (cs0 @ (Pa, Ev a, Qa) # cs1);
*)
apply(case_tac cs1)
(* cs1=[] *)
apply(clarsimp)
apply(case_tac cs0)
(* case_tac cs0 to find out the initial process corresponding to Q
 cs0=[] *)
apply(clarsimp)
apply(rule_tac x="P |[X]| Qa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(drule comps_car)
apply(erule ptrans_par2)
apply(assumption)
(* cs0=aa#list *)
apply(clarsimp)
apply(rule_tac x="P |[X]| b" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) (list @ [(Pa, Ev a, Qa)])" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(subgoal_tac "map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) ((aa, Tau, b) # list @ [(Pa, Ev a, Qa)]) : comps D")
apply(clarsimp)
apply(rule comps_tau_seq_par1_1)
apply(assumption)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
(* cs1=aa#list, use hypo *)
apply(clarsimp)
apply(drule_tac x="P" in spec)
apply(drule_tac x="aa" in spec)
apply(drule mp)
(* hypo *)
apply(rule_tac x="b" in exI)
apply(rule_tac x="ab" in exI)
apply(rule_tac x="list" in exI)
apply(clarsimp)
apply(drule comps_app_D2)
apply(drule comps_cdr)
apply(assumption)
(* body *)
apply(erule disjE)
(* case 1/2: comp_to_trace ((aa, ab, b) # list) = [] *)
apply(clarsimp)
apply(frule comps_app_D2)
apply(frule comps_connect)
apply(clarsimp)
(* case_tac cs0 to find out Q's partner *)
apply(case_tac cs0)
(* 1/2 *)
apply(clarsimp)
apply(rule_tac x="P |[X]| aa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="[]" in exI)
apply(rule conjI)
apply(clarsimp)
apply(drule comps_car)
apply (metis comps.comps_step1 ptrans.ptrans_par2)
apply(clarsimp)
apply(rule_tac x="P |[X]| ba" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) (lista @[(Pa, Ev a, aa)])" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(subgoal_tac "map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) ((ac,Tau,ba)#lista@[(Pa, Ev a, aa)]) : comps D")
apply(clarsimp)
apply(rule comps_tau_seq_par1_1)
apply(erule comps_car_car_cdr)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
(**)
apply(clarsimp)
apply(frule comps_app_D2)
apply(frule comps_connect)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="P |[X]| aa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="(P |[X]| aa, ua, P'a) # csa" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(assumption)
apply(rule ptrans_par2)
apply(erule comps_car)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="P |[X]| ba" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) (lista @[(Pa, Ev a, aa)])) @
                  (P |[X]| aa, ua, P'a) # csa" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(clarsimp)
apply(subgoal_tac 
  "map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) ((ac,Tau,ba)#lista) @
           (P |[X]| Pa, Ev a, P |[X]| aa) # (P |[X]| aa, ua, P'a) # csa
           : comps D")
apply(clarsimp)
apply(rule comps_app_D_0)
apply(subgoal_tac "map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) ((ac,Tau,ba)#lista@[(Pa, Ev a, aa)]) : comps D")
apply(clarsimp)
apply(rule comps_tau_seq_par1_1)
apply(erule comps_car_car_cdr)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(clarsimp)
done

lemma otraces_r_interleave2[rule_format]:
  "ALL Q P.
    t : otraces_r D P -->
     set t Int X = {} -->
     t : otraces_r D (P |[X]| Q)"
apply(induct_tac t)
apply(clarsimp)
apply(clarsimp)
apply(unfold otraces_r_def)
apply(clarsimp)
apply(frule non_nil_comp_to_trace_forall)
apply(clarsimp)
(****)
(*
to use the hypothesis
 comp_to_trace cs1 = comp_to_trace ((Q, u, P') # cs) 
is needed. try to create this from
    a # comp_to_trace cs1 = comp_to_trace (cs0 @ (Pa, Ev a, Qa) # cs1);
*)
apply(case_tac cs1)
(* cs1=[] *)
apply(clarsimp)
apply(case_tac cs0)
(* case_tac cs0 to find out the initial process corresponding to Q
 cs0=[] *)
apply(clarsimp)
apply(rule_tac x="Qa |[X]| Q" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(drule comps_car)
apply(erule ptrans_par1)
apply(assumption)
(* cs0=aa#list *)
apply(clarsimp)
apply(rule_tac x="b |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) (list @ [(Pa, Ev a, Qa)])" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(subgoal_tac "map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) ((aa, Tau, b) # list @ [(Pa, Ev a, Qa)]) : comps D")
apply(clarsimp)
apply(rule comps_tau_seq_par1_2)
apply(assumption)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
(* cs1=aa#list, use hypo *)
apply(clarsimp)
apply(drule_tac x="Q" in spec)
apply(drule_tac x="aa" in spec)
apply(drule mp)
(* hypo *)
apply(rule_tac x="b" in exI)
apply(rule_tac x="ab" in exI)
apply(rule_tac x="list" in exI)
apply(clarsimp)
apply(drule comps_app_D2)
apply(drule comps_cdr)
apply(assumption)
(* body *)
apply(erule disjE)
(* case 1/2: comp_to_trace ((aa, ab, b) # list) = [] *)
apply(clarsimp)
apply(frule comps_app_D2)
apply(frule comps_connect)
apply(clarsimp)
(* case_tac cs0 to find out Q's partner *)
apply(case_tac cs0)
(* 1/2 *)
apply(clarsimp)
apply(rule_tac x="aa |[X]| Q" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="[]" in exI)
apply(rule conjI)
apply(clarsimp)
apply(drule comps_car)
apply (metis comps.comps_step1 ptrans.ptrans_par1)
apply(clarsimp)
apply(rule_tac x="ba |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) (lista @[(Pa, Ev a, aa)])" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(subgoal_tac "map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) ((ac,Tau,ba)#lista@[(Pa, Ev a, aa)]) : comps D")
apply(clarsimp)
apply(rule comps_tau_seq_par1_2)
apply(erule comps_car_car_cdr)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
(**)
apply(clarsimp)
apply(frule comps_app_D2)
apply(frule comps_connect)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="aa |[X]| Q" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="(aa |[X]| Q, ua, P'a) # csa" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(assumption)
apply(rule ptrans_par1)
apply(erule comps_car)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="ba |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) (lista @[(Pa, Ev a, aa)])) @
                  (aa |[X]| Q, ua, P'a) # csa" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(clarsimp)
apply(subgoal_tac 
  "map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) ((ac,Tau,ba)#lista) @
           (Pa |[X]| Q, Ev a, aa |[X]| Q) # (aa |[X]| Q, ua, P'a) # csa
           : comps D")
apply(clarsimp)
apply(rule comps_app_D_0)
apply(subgoal_tac "map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) ((ac,Tau,ba)#lista@[(Pa, Ev a, aa)]) : comps D")
apply(clarsimp)
apply(rule comps_tau_seq_par1_2)
apply(erule comps_car_car_cdr)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(clarsimp)
done

lemma otraces_r_E:
  "[| s : otraces_r D P;
      s = [] ==> R;
      !!P' u cs. [| s = comp_to_trace ((P, u, P') # cs);
          (P, u, P') # cs : comps D |]
       ==> R |]
   ==> R"
apply(unfold otraces_r_def)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(clarsimp)
done

lemma cut_tail [intro!]:
  "x#xs@x1#xs1 : comps D ==> x#xs@[x1] : comps D"
apply(subgoal_tac "(x#xs@[x1])@xs1 : comps D")
apply(rotate_tac -1)
apply(drule comps_app)
apply(clarsimp)
apply(clarsimp)
done

lemma comp_app_conn2:
  "x # xs @ (P, u, P')#(Q, v, Q')#ys : comps D
  ==> P'=Q | (EX q f. P' = f($q) & Q = f(D q))"
apply(subgoal_tac "(x # xs) @ ((P, u, P')#(Q, v, Q')#ys) : comps D")
apply(rotate_tac -1)
apply(drule comps_app)
apply(erule conjE)
apply(rotate_tac -1)
apply(drule comps_connect)
apply(clarsimp)
apply(clarsimp)
done

lemma comp_app_div:
  "[|
  x#xs@[(P,u,P')] : comps D;
  (Q,v,Q')#ys : comps D;
  P'=Q |]
  ==> x#xs@(P,u,P')#(Q,v,Q')#ys : comps D"
apply(clarsimp)
apply(subgoal_tac "(x # xs @ [(P, u, Q)]) @ ((Q, v, Q') # ys) : comps D")
apply(clarsimp)
apply(rule comps_conn_app)
apply(clarsimp)
apply(clarsimp)
apply(subst comp_conn_def)
apply(clarsimp)
done

lemma map_hd:
  "(f P, v, f Q) # (map (%(p, u, q). (f p, u, f q)) xs)
  = (map (%(p, u, q). (f p, u, f q)) ((P,v,Q)#xs))"
apply(clarsimp)
done

lemma map_tl:
  "(map (%(p, u, q). (f p, u, f q)) xs) @ [(f P, v, f Q)]
  = (map (%(p, u, q). (f p, u, f q)) (xs@[(P,v,Q)]))"
apply(clarsimp)
done

lemma comps_cont [rule_format]:
  "ALL P u Q. (P, u, Q)#cs : comps D --> comp_to_trace cs : otraces_r D Q"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(unfold otraces_r_def)
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(simp)
apply(rule_tac x="b" in exI)
apply(rule_tac x="aa" in exI)
apply(rule_tac x="list" in exI)
apply(clarsimp)
apply(erule comps_cdr)
done

lemma comps_interleave_seq1 [rule_format]:
  "cs : comps D ==>
  (forall (%(p, u, q). case u of Tau => True | Ev a => a ~: X) cs) -->
  (map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) cs) : comps D"
apply(erule comps.induct)
apply(clarsimp)
apply(clarsimp)
apply(case_tac u)
apply(clarsimp)
apply (metis ptrans.ptrans_par5)
apply(clarsimp)
apply (metis ptrans.ptrans_par2)
apply(clarsimp)
apply(rule comps_step2)
apply(assumption)
apply(case_tac u')
apply(clarsimp)
apply (metis ptrans.ptrans_par5)
apply(clarsimp)
by (metis ptrans.ptrans_par2)

lemma comps_interleave_seq2 [rule_format]:
  "cs : comps D ==>
  (forall (%(p, u, q). case u of Tau => True | Ev a => a ~: X) cs) -->
  (map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) cs) : comps D"
apply(erule comps.induct)
apply(clarsimp)
apply(clarsimp)
apply(case_tac u)
apply(clarsimp)
apply (metis ptrans.ptrans_par4)
apply(clarsimp)
apply (metis ptrans.ptrans_par1)
apply(clarsimp)
apply(rule comps_step2)
apply(assumption)
apply(case_tac u')
apply(clarsimp)
apply (metis ptrans.ptrans_par4)
apply(clarsimp)
by (metis ptrans.ptrans_par1)

lemma comp_connI2:
  "P' = Q ==> comp_conn D (cs'@[(P, u, P')]) ((Q, v, Q')#cs)"
apply(unfold comp_conn_def)
apply(auto)
done

lemma rm_hypo: "Q ==> P ==> P"
apply(auto)
done

lemma otraces_par_1_1:
  "[| ALL u a lista.
             (ALL u t.
                 u : sync X lista t -->
                 (ALL P.
                     lista : otraces_r D P -->
                     (ALL Q.
                         t : otraces_r D Q -->
                         u : otraces_r D (P |[X]| Q)))) -->
             u : sync X (a # lista) list -->
             a # lista : otraces_r D P -->
             list : otraces_r D Q --> u : otraces_r D (P |[X]| Q);
          ALL u t.
             u : sync X lista t -->
             (ALL P.
                 lista : otraces_r D P -->
                 (ALL Q.
                     t : otraces_r D Q -->
                     u : otraces_r D (P |[X]| Q)));
          a # lista : otraces_r D P; a # list : otraces_r D Q;
          a : X; ua : sync X lista list |]
       ==> a # ua : otraces_r D (P |[X]| Q)"
apply(erule_tac s="a#lista" in otraces_r_E)
apply(clarsimp)
apply(frule_tac a="a" in non_nil_comp_to_trace_forall)
apply(drule_tac s="a # lista" in sym)
apply(clarsimp)
apply(erule_tac s="a#list" in otraces_r_E)
apply(clarsimp)
apply(frule_tac tr="list" in non_nil_comp_to_trace_forall)
apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="ua" in spec)
apply(rotate_tac -1)
apply(drule_tac x="(comp_to_trace cs1a)" in spec)
apply(drule mp)
apply(assumption)
apply(drule_tac x="Qa" in spec)
apply(drule mp)
apply(rule comps_cont)
apply(erule comps_app_D2)
apply(drule_tac x="Qaa" in spec)
apply(drule mp)
apply(rule comps_cont)
apply(erule comps_app_D2)
apply(erule_tac s="ua" in otraces_r_E)
apply(clarsimp)
apply(subst otraces_r_def)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(case_tac cs0a)
apply(clarsimp)
apply(rule_tac x="Qa |[X]| Qaa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply (metis comps_car ptrans.ptrans_par3)
(* cs0a = aa # listb *)
apply(clarsimp)
apply(rule_tac x="P |[X]| b" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) listb)@[(P |[X]| Pa, Ev a, Qa |[X]| Qaa)]" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau)
apply(clarsimp)
apply(erule ptrans_par5)
apply(subst append_Cons[THEN sym])
apply(rule comps_conn_app)
apply(subst map_hd)
apply(rule comps_interleave_seq1)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(drule comp_to_trace_nil2)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_step1)
apply(rule ptrans_par3)
apply(erule comps_car)
apply (metis append_Cons comps_app_D2 comps_car)
apply(clarsimp)
apply(subst map_hd)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(drule cut_tail)
apply(clarsimp)
apply(assumption)
(* cs0 = aa # listb *)
apply(clarsimp)
apply(case_tac cs0a)
apply(clarsimp)
apply(rule_tac x="b |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) listb)@[(Pa |[X]| Q, Ev a, Qa |[X]| Qaa)]" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule_tac f="(%x. x |[X]| Q)" in comp_to_trace_map_tau)
apply(clarsimp)
apply(erule ptrans_par4)
apply(subst append_Cons[THEN sym])
apply(rule comps_conn_app)
apply(subst map_hd)
apply(rule comps_interleave_seq2)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(drule comp_to_trace_nil2)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_step1)
apply(rule ptrans_par3)
apply (metis comps_car comps_car_app_D2)
apply(erule comps_car)
apply(clarsimp)
apply(subst map_hd)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(drule cut_tail)
apply(clarsimp)
apply(assumption)
(* cs0a = aa # listaa *)
apply(clarsimp)
apply(rule_tac x="b |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="
  (map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) listb)@
  (map (%(p, u, q). (Pa |[X]| p, u, Pa |[X]| q))
       ((Q,Tau,ba)#listaa))@
  [(Pa |[X]| Paa, Ev a, Qa |[X]| Qaa)]" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule conjI)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq2)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq1)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_step1)
apply(rule ptrans_par3)
apply (metis comps_car comps_car_app_D2)
apply (metis comps_car comps_car_app_D2)
apply(clarsimp)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(clarsimp)
apply(assumption)
apply(insert list_rev_cases)
apply(rotate_tac -1)
apply(drule_tac x="listaa" in spec)
apply(erule disjE)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(subst map_hd)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(drule cut_tail)
apply(clarsimp)
apply(assumption)
apply(clarsimp)
apply(frule_tac x="(Q,Tau,ba)" in comps_cdr)
apply(rotate_tac -1)
apply(drule comps_app_D2)
apply(rotate_tac -1)
apply(frule comps_connect)
apply(clarsimp)
apply(insert list_rev_cases)
apply(rotate_tac -1)
apply(drule_tac x="listb" in spec)
apply(erule disjE)
apply(clarsimp)
apply(rotate_tac 3)
apply(frule comps_connect)
apply(clarsimp)
apply(rule comp_connI)
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac 3)
apply(drule comps_cdr)
apply(rotate_tac -1)
apply(drule comps_app_D2)
apply(rotate_tac -1)
apply(drule comps_connect)
apply(clarsimp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comp_connI2)
apply(clarsimp)
(* the last *)
apply(rotate_tac -1)
apply(erule rm_hypo)
apply(rotate_tac -1)
apply(erule rm_hypo)
apply(rotate_tac 12)
apply(erule rm_hypo)
apply(clarsimp)
apply(subst otraces_r_def)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(case_tac cs0a)
apply(clarsimp)
apply(rule_tac x="Qa |[X]| Qaa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="(Qa |[X]| Qaa, ub, P'b)#csb" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply (metis comps_car ptrans.ptrans_par3)
(* cs0a = aa # listb *)
apply(clarsimp)
apply(rule_tac x="P |[X]| b" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p, u, q). (P |[X]| p, u, P |[X]| q)) listb)@(P |[X]| Pa, Ev a, Qa |[X]| Qaa)#(Qa |[X]| Qaa, ub, P'b)#csb" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq1)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_step2)
apply(simp)
apply(rule ptrans_par3)
apply (metis comps_car)
apply (metis comps_car comps_car_app_D2)
apply(clarsimp)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(clarsimp)
apply(assumption)
(**)
apply(clarsimp)
apply(case_tac cs0a)
apply(clarsimp)
apply(rule_tac x="b |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) listb)@(Pa |[X]| Q, Ev a, Qa |[X]| Qaa)#(Qa |[X]| Qaa, ub, P'b) # csb" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq2)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply (metis comps_car comps_car_app_D2 ptrans.ptrans_par3)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(clarsimp)
apply(assumption)
(**)
apply(clarsimp)
apply(rule_tac x="b |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="
  (map (%(p, u, q). (p |[X]| Q, u, q |[X]| Q)) listb)@
  (map (%(p, u, q). (Pa |[X]| p, u, Pa |[X]| q))
       ((Q,Tau,ba)#listaa))@
  (Pa |[X]| Paa, Ev a, Qa |[X]| Qaa)#(Qa |[X]| Qaa, ub, P'b) # csb" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule conjI)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq2)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq1)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(rule ptrans_par3)
apply (metis comps_car comps_car_app_D2)
apply (metis comps_car comps_car_app_D2)
apply(clarsimp)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(clarsimp)
apply(assumption)
apply(insert list_rev_cases)
apply(rotate_tac -1)
apply(drule_tac x="listaa" in spec)
apply(erule disjE)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(subst map_hd)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(drule cut_tail)
apply(clarsimp)
apply(assumption)
apply(clarsimp)
apply(frule_tac x="(Q,Tau,ba)" in comps_cdr)
apply(rotate_tac -1)
apply(drule comps_app_D2)
apply(rotate_tac -1)
apply(frule comps_connect)
apply(clarsimp)
apply(insert list_rev_cases)
apply(rotate_tac -1)
apply(drule_tac x="listb" in spec)
apply(erule disjE)
apply(clarsimp)
apply(rotate_tac 3)
apply(frule comps_connect)
apply(clarsimp)
apply(rule comp_connI)
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac 3)
apply(drule comps_cdr)
apply(rotate_tac -1)
apply(drule comps_app_D2)
apply(rotate_tac -1)
apply(drule comps_connect)
apply(clarsimp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comp_connI2)
apply(clarsimp)
done

lemma otraces_par_1_2:
  "[| ALL u a lista.
             (ALL u t.
                 u : sync X lista t -->
                 (ALL P.
                     lista : otraces_r D P -->
                     (ALL Q.
                         t : otraces_r D Q -->
                         u : otraces_r D (P |[X]| Q)))) -->
             u : sync X (a # lista) list -->
             a # lista : otraces_r D P -->
             list : otraces_r D Q --> u : otraces_r D (P |[X]| Q);
          ALL u t.
             u : sync X lista t -->
             (ALL P.
                 lista : otraces_r D P -->
                 (ALL Q.
                     t : otraces_r D Q -->
                     u : otraces_r D (P |[X]| Q)));
          aa # lista : otraces_r D P; a # list : otraces_r D Q;
          a : X; aa ~: X; ua : sync X lista (a # list) |]
       ==> aa # ua : otraces_r D (P |[X]| Q)"
apply(erule rm_hypo)
apply(drule_tac x="ua" in spec)
apply(drule_tac x="a#list" in spec)
apply(clarsimp)
apply(erule_tac s="aa#lista" in otraces_r_E)
apply(clarsimp)
apply(frule_tac a="aa" in non_nil_comp_to_trace_forall)
apply(drule_tac s="aa # lista" in sym)
apply(clarsimp)
apply(drule_tac x="Qa" in spec)
apply(drule mp)
apply(rule comps_cont)
apply(drule comps_app_D2)
apply(assumption)
apply(drule_tac x="Q" in spec)
apply(drule mp)
apply(clarsimp)
(**)
apply(erule_tac s="ua" in otraces_r_E)
apply(clarsimp)
apply(subst otraces_r_def)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="Qa |[X]| Q" in exI)
apply(rule_tac x="Ev aa" in exI)
apply(rule_tac x="[]" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step1)
apply (metis comps_car ptrans.ptrans_par1)
apply(clarsimp)
apply(rule_tac x="b |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p,u,q). (p |[X]| Q,u,q |[X]| Q)) (listb@[(Pa,Ev aa,Qa)]))" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(simp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq2)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_step1)
apply (metis comps_car comps_car_app_D2 ptrans.ptrans_par1)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(clarsimp)
apply(assumption)
(**)
apply(clarsimp)
apply(subst otraces_r_def)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="Qa |[X]| Q" in exI)
apply(rule_tac x="Ev aa" in exI)
apply(rule_tac x="(Qa |[X]| Q, uaa, P'a) # csa" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply (metis comps_car ptrans.ptrans_par1)
(**)
apply(clarsimp)
apply(rule_tac x="b |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p,u,q). (p |[X]| Q,u,q |[X]| Q)) (listb@[(Pa,Ev aa,Qa)])) @ (Qa |[X]| Q, uaa, P'a) # csa" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(simp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq2)
apply (metis comps_car_app_D1)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply (metis comps_car comps_car_app_D2 ptrans.ptrans_par1)
apply(rule comp_conn_map)
apply(rule comps_app_conn)
apply(clarsimp)
apply(assumption)
done

lemma otraces_par_1_3:
  "[| ALL u a lista.
             (ALL u t.
                 u : sync X lista t -->
                 (ALL P.
                     lista : otraces_r D P -->
                     (ALL Q.
                         t : otraces_r D Q -->
                         u : otraces_r D (P |[X]| Q)))) -->
             u : sync X (a # lista) list -->
             (ALL P.
                 a # lista : otraces_r D P -->
                 (ALL Q.
                     list : otraces_r D Q -->
                     u : otraces_r D (P |[X]| Q)));
          ALL u t.
             u : sync X lista t -->
             (ALL P.
                 lista : otraces_r D P -->
                 (ALL Q.
                     t : otraces_r D Q -->
                     u : otraces_r D (P |[X]| Q)));
          aa # lista : otraces_r D P; a # list : otraces_r D Q;
          a ~: X; aa : X; ua : sync X (aa # lista) list |]
       ==> a # ua : otraces_r D (P |[X]| Q)"
apply(drule_tac x="ua" in spec)
apply(drule_tac x="aa" in spec)
apply(rotate_tac -1)
apply(drule_tac x="lista" in spec)
apply(drule mp)
apply(clarsimp)
apply(erule rm_hypo)
apply(clarsimp)
apply(drule_tac x="P" in spec)
apply(clarsimp)
apply(erule_tac s="a#list" in otraces_r_E)
apply(clarsimp)
apply(frule_tac a="a" in non_nil_comp_to_trace_forall)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(drule_tac x="Qa" in spec)
apply(drule mp)
apply(rule comps_cont)
apply(assumption)
apply(subst otraces_r_def)
apply(clarsimp)
apply(erule_tac s="ua" in otraces_r_E)
apply(clarsimp)
apply(rule_tac x="P |[X]| Qa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="[]" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step1)
apply (metis comps_car ptrans.ptrans_par2)
apply(clarsimp)
apply(rule_tac x="P |[X]| Qa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="(P |[X]| Qa, u, P') # cs" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply (metis comps_car ptrans.ptrans_par2)
(**)
apply(clarsimp)
apply(drule_tac x="Qa" in spec)
apply(drule mp)
apply(rule comps_cont)
apply(drule comps_cdr)
apply(rotate_tac -1)
apply(drule comps_app_D2)
apply(assumption)
apply(subst otraces_r_def)
apply(clarsimp)
apply(erule_tac s="ua" in otraces_r_E)
apply(clarsimp)
apply(rule_tac x="P |[X]| b" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p,u,q). (P |[X]| p,u,P |[X]| q)) (listb@[(Pa,Ev a,Qa)]))" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(subst map_hd)
apply(rule comps_interleave_seq1)
apply(drule cut_tail)
apply(clarsimp)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
(**)
apply(clarsimp)
apply(rule_tac x="P |[X]| b" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p,u,q). (P |[X]| p,u,P |[X]| q)) (listb@[(Pa,Ev a,Qa)]))@(P |[X]| Qa, u, P') # cs" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq1)
apply(drule cut_tail)
apply(clarsimp)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(clarsimp)
apply(rule comp_conn_map)
apply(subst append_Cons[THEN sym])
apply(rule comp_connI2)
apply(clarsimp)
done

lemma otraces_par_1_4:
  "[| ALL u a lista.
             (ALL u t.
                 u : sync X lista t -->
                 (ALL P.
                     lista : otraces_r D P -->
                     (ALL Q.
                         t : otraces_r D Q -->
                         u : otraces_r D (P |[X]| Q)))) -->
             u : sync X (a # lista) list -->
             (ALL P.
                 a # lista : otraces_r D P -->
                 (ALL Q.
                     list : otraces_r D Q -->
                     u : otraces_r D (P |[X]| Q)));
          ALL u t.
             u : sync X lista t -->
             (ALL P.
                 lista : otraces_r D P -->
                 (ALL Q.
                     t : otraces_r D Q -->
                     u : otraces_r D (P |[X]| Q)));
          aa # lista : otraces_r D P; a # list : otraces_r D Q;
          a ~: X; aa ~: X; ua : sync X lista (a # list) |]
       ==> aa # ua : otraces_r D (P |[X]| Q)"
apply(erule rm_hypo)
apply(drule_tac x="ua" in spec)
apply(drule_tac x="a#list" in spec)
apply(clarsimp)
apply(erule_tac s="aa#lista" in otraces_r_E)
apply(clarsimp)
apply(frule_tac a="aa" in non_nil_comp_to_trace_forall)
apply(clarsimp)
apply(drule_tac x="Qa" in spec)
apply(drule mp)
apply(rule comps_cont)
apply(drule comps_app_D2)
apply(assumption)
apply(drule_tac x="Q" in spec)
apply(clarsimp)
apply(subst otraces_r_def)
apply(clarsimp)
apply(erule_tac s="ua" in otraces_r_E)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="Qa |[X]| Q" in exI)
apply(rule_tac x="Ev aa" in exI)
apply(rule_tac x="[]" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step1)
apply (metis comps_car ptrans.ptrans_par1)
(* cs0 = ab#listb *)
apply(clarsimp)
apply(rule_tac x="b |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p,u,q). (p|[X]|Q,u,q|[X]|Q)) (listb@[(Pa,Ev aa,Qa)]))" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(subst map_hd)
apply(rule comps_interleave_seq2)
apply(drule cut_tail)
apply(clarsimp)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
(**)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="Qa |[X]| Q" in exI)
apply(rule_tac x="Ev aa" in exI)
apply(rule_tac x="(Qa |[X]| Q, uaa, P'a) # csa" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply (metis comps_car ptrans.ptrans_par1)
(* cs0 = ab#listb *)
apply(clarsimp)
apply(rule_tac x="b |[X]| Q" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p,u,q). (p|[X]|Q,u,q|[X]|Q)) (listb@[(Pa,Ev aa,Qa)]))@(Qa |[X]| Q, uaa, P'a) # csa" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2_2)
apply(clarsimp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq2)
apply(drule cut_tail)
apply(clarsimp)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(clarsimp)
apply(rule comp_conn_map)
apply(subst append_Cons[THEN sym])
apply(rule comp_connI2)
apply(clarsimp)
done

lemma otraces_par_1_5:
  "[| ALL u a lista.
             (ALL u t.
                 u : sync X lista t -->
                 (ALL P.
                     lista : otraces_r D P -->
                     (ALL Q.
                         t : otraces_r D Q -->
                         u : otraces_r D (P |[X]| Q)))) -->
             u : sync X (a # lista) list -->
             (ALL P.
                 a # lista : otraces_r D P -->
                 (ALL Q.
                     list : otraces_r D Q -->
                     u : otraces_r D (P |[X]| Q)));
          ALL u t.
             u : sync X lista t -->
             (ALL P.
                 lista : otraces_r D P -->
                 (ALL Q.
                     t : otraces_r D Q -->
                     u : otraces_r D (P |[X]| Q)));
          aa # lista : otraces_r D P; a # list : otraces_r D Q;
          a ~: X; aa ~: X; ua : sync X (aa # lista) list |]
       ==> a # ua : otraces_r D (P |[X]| Q)"
apply(drule_tac x="ua" in spec)
apply(drule_tac x="aa" in spec)
apply(rotate_tac -1)
apply(drule_tac x="lista" in spec)
apply(clarsimp)
apply(erule rm_hypo)
apply(drule_tac x="P" in spec)
apply(clarsimp)
apply(erule_tac s="a#list" in otraces_r_E)
apply(clarsimp)
apply(frule_tac a="a" in non_nil_comp_to_trace_forall)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(drule_tac x="Qa" in spec)
apply(drule mp)
apply(rule comps_cont)
apply(assumption)
apply(subst otraces_r_def)
apply(clarsimp)
apply(erule_tac s="ua" in otraces_r_E)
apply(clarsimp)
apply(rule_tac x="P |[X]| Qa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="[]" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step1)
apply (metis comps_car ptrans.ptrans_par2)
apply(clarsimp)
apply(rule_tac x="P |[X]| Qa" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="(P |[X]| Qa, u, P') # cs" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply (metis comps_car ptrans.ptrans_par2)
(**)
apply(clarsimp)
apply(drule_tac x="Qa" in spec)
apply(drule mp)
apply(rule comps_cont)
apply(drule comps_cdr)
apply(rotate_tac -1)
apply(drule comps_app_D2)
apply(assumption)
apply(subst otraces_r_def)
apply(clarsimp)
apply(erule_tac s="ua" in otraces_r_E)
apply(clarsimp)
apply(rule_tac x="P |[X]| b" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p,u,q). (P |[X]| p,u,P |[X]| q)) (listb@[(Pa,Ev a,Qa)]))" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(subst map_hd)
apply(rule comps_interleave_seq1)
apply(drule cut_tail)
apply(clarsimp)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
(**)
apply(clarsimp)
apply(rule_tac x="P |[X]| b" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(map (%(p,u,q). (P |[X]| p,u,P |[X]| q)) (listb@[(Pa,Ev a,Qa)]))@(P |[X]| Qa, u, P') # cs" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comp_to_trace_map_tau_par2)
apply(clarsimp)
apply(subst append_Cons[THEN sym])
apply(subst map_hd)
apply(rule comps_conn_app)
apply(rule comps_interleave_seq1)
apply(drule cut_tail)
apply(clarsimp)
apply(clarsimp)
apply(erule forall_mono)
apply(clarsimp)
apply(clarsimp)
apply(rule comp_conn_map)
apply(subst append_Cons[THEN sym])
apply(rule comp_connI2)
apply(clarsimp)
done

lemma otraces_par_1:
  "ALL u a list P Q.
  (ALL u t P Q.
             u : sync X list t -->
             list : otraces_r D P -->
             t : otraces_r D Q --> u : otraces_r D (P |[X]| Q)) -->
          u : sync X (a # list) t -->
          a # list : otraces_r D P -->
          t : otraces_r D Q -->
     u : otraces_r D (P |[X]| Q)"
apply(induct_tac t)
apply(clarsimp)
apply(drule sync_nil)
apply(clarsimp)
apply(erule otraces_r_interleave2)
apply(clarsimp)
apply(safe)
apply(clarsimp)
apply(case_tac "a:X")
apply(case_tac "aa:X")
apply(case_tac "a=aa")
apply(clarsimp)
defer
apply(clarsimp)
apply(clarsimp)
defer
apply(case_tac "aa:X")
apply(clarsimp)
defer
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
defer
apply(clarsimp)
defer
(*
   1/5  a=aa:X
*)
apply(rule otraces_par_1_1)
apply(auto)
apply(rule otraces_par_1_2)
apply(auto)
apply(rule otraces_par_1_3)
apply(auto)
apply(rule otraces_par_1_4)
apply(auto)
apply(rule otraces_par_1_5)
apply(auto)
done

lemma otraces_par:
  "ALL X s P Q t u.
      u : sync X s t -->
      s : otraces_r D P -->
      t : otraces_r D Q -->
    u : otraces_r D (P |[X]| Q)"
apply(rule allI)
apply(rule allI)
apply(induct_tac s)
apply(auto)
apply(drule sync_nil)
apply(clarsimp)
apply(erule otraces_r_interleave)
apply(assumption)
(**)
apply(rule otraces_par_1[rule_format])
defer
apply(assumption)
apply(assumption)
apply(assumption)
apply(clarsimp)
done

lemma traces_otraces_1_par:
  "[| traces proc1 (%p. otraces D ($p)) <= otraces D proc1;
      traces proc2 (%p. otraces D ($p)) <= otraces D proc2 |]
       ==> traces (proc1 |[X]| proc2) (%p. otraces D ($p))
           <= otraces D (proc1 |[X]| proc2)"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
(**)
apply(rule subsetI)
apply(clarsimp)
apply(drule subsetD)
apply(assumption)
apply(drule subsetD)
apply(assumption)
apply(rule otraces_par[rule_format])
apply(auto)
done

lemma comps_hide1 [rule_format]:
  "cs:comps D --> ceal X (comp_to_trace cs) =
  comp_to_trace
    (map (%(p, u, q).
         (p -- X,
           case u of Tau => Tau
                 | Ev a => if a : X then Tau else Ev a,
         q -- X))
       cs)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(case_tac "ab:X")
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_cdr)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(clarsimp)
done

lemma comps_hide2 [rule_format]:
  "cs : comps D
--> (map (%(p,u,q). (p--X, case u of Tau => Tau | Ev a => if a:X then Tau else Ev a,q--X)) cs) : comps D"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply (metis comps_car ptrans.ptrans_hide3)
apply(clarsimp)
apply(case_tac "ab:X")
apply(clarsimp)
apply (metis comps_car ptrans.ptrans_hide2)
apply(clarsimp)
apply (metis comps_car ptrans.ptrans_hide1)
(**)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply (metis (full_types, hide_lams) comps_car ptrans.ptrans_hide3)
apply(case_tac "ad:X")
apply(clarsimp)
apply (metis (full_types, hide_lams) comps_car ptrans.ptrans_hide2)
apply(clarsimp)
by (metis (no_types, hide_lams) comps_car ptrans.ptrans_hide1)

lemma otraces_hide_sub:
"a # list : otraces_r D P
  ==> ceal X (a # list) : otraces_r D (P -- X)"
apply(subst otraces_r_def)
apply(clarsimp)
apply(case_tac "a:X")
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(simp)
apply(erule otraces_r_E)
apply(clarsimp)
apply(frule_tac a="a" in non_nil_comp_to_trace_forall)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="Q -- X" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="map (%(p,u,q). (p--X, case u of Tau => Tau | Ev a => if a:X then Tau else Ev a,q--X)) cs1" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_hide1)
apply(erule comps_cdr)
apply(subgoal_tac 
  "map (%(p, u, q).
                   (p -- X,
                    case u of Tau => Tau
                    | Ev a => if a : X then Tau else Ev a,
                    q -- X))
            ((P,Ev a,Q)#cs1)
           : comps D")
apply(clarsimp)
apply(rule comps_hide2)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="b -- X" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="map (%(p,u,q). (p--X, case u of Tau => Tau | Ev a => if a:X then Tau else Ev a,q--X)) (lista@(Pa,Ev a,Q)#cs1)" in exI)
apply(rule conjI)
apply(subgoal_tac 
  "ceal X (comp_to_trace ((P,Tau,b)#lista @ (Pa, Ev a, Q) # cs1)) =
  comp_to_trace
  (map (%(p, u, q).
  (p -- X,
  case u of Tau => Tau
  | Ev a => if a : X then Tau else Ev a,
  q -- X))
  ((P,Tau,b)#lista @ (Pa, Ev a, Q) # cs1))")
apply(clarsimp)
apply(rule comps_hide1)
apply(assumption)
apply(subgoal_tac 
  "map (%(p, u, q).
                   (p -- X,
                    case u of Tau => Tau
                    | Ev a => if a : X then Tau else Ev a,
                    q -- X))
            ((P,Tau,b)#lista@(Pa,Ev a,Q)#cs1)
           : comps D")
apply(clarsimp)
apply(rule comps_hide2)
apply(assumption)
(**)
apply(clarsimp)
apply(erule otraces_r_E)
apply(clarsimp)
apply(frule_tac a="a" in non_nil_comp_to_trace_forall)
apply(clarsimp)
apply(case_tac cs0)
apply(clarsimp)
apply(rule_tac x="Q -- X" in exI)
apply(rule_tac x="Ev a" in exI)
apply(rule_tac x="map (%(p,u,q). (p--X, case u of Tau => Tau | Ev a => if a:X then Tau else Ev a,q--X)) cs1" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_hide1)
apply(erule comps_cdr)
apply(subgoal_tac 
  "map (%(p, u, q).
                   (p -- X,
                    case u of Tau => Tau
                    | Ev a => if a : X then Tau else Ev a,
                    q -- X))
            ((P,Ev a,Q)#cs1)
           : comps D")
apply(clarsimp)
apply(rule comps_hide2)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="b -- X" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="map (%(p,u,q). (p--X, case u of Tau => Tau | Ev a => if a:X then Tau else Ev a,q--X)) (lista@(Pa,Ev a,Q)#cs1)" in exI)
apply(rule conjI)
apply(subgoal_tac 
  "ceal X (comp_to_trace ((P,Tau,b)#lista @ (Pa, Ev a, Q) # cs1)) =
  comp_to_trace
  (map (%(p, u, q).
  (p -- X,
  case u of Tau => Tau
  | Ev a => if a : X then Tau else Ev a,
  q -- X))
  ((P,Tau,b)#lista @ (Pa, Ev a, Q) # cs1))")
apply(clarsimp)
apply(rule comps_hide1)
apply(assumption)
apply(subgoal_tac 
  "map (%(p, u, q).
                   (p -- X,
                    case u of Tau => Tau
                    | Ev a => if a : X then Tau else Ev a,
                    q -- X))
            ((P,Tau,b)#lista@(Pa,Ev a,Q)#cs1)
           : comps D")
apply(clarsimp)
apply(rule comps_hide2)
apply(assumption)
done

lemma otraces_hide [rule_format]:
  "s : otraces_r D P
  --> ceal X s : otraces_r D (P -- X)"
apply(induct_tac s)
apply(clarsimp)
apply(safe)
apply(erule otraces_hide_sub)
apply(erule otraces_hide_sub)
done

lemma traces_otraces_1_hide:
  "traces P (%p. otraces D ($p)) <= otraces D P
       ==> traces (P -- X) (%p. otraces D ($p))
           <= otraces D (P -- X)"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
(**)
apply(rule subsetI)
apply(clarsimp)
apply(drule subsetD)
apply(assumption)
apply(erule rm_hypo)
apply(erule otraces_hide)
done

lemma traces_otraces_1_pn:
  "traces ($p) (%q. otraces D ($q)) <= otraces D ($p)"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(clarsimp)
apply(erule contrapos_pp)
apply(subst Abs_domT_inverse)
apply(rule otraces_domT)
apply(clarsimp)
done

lemma traces_otraces_1_int_choice_1:
  "x : otraces_r D proc1
    ==> x : otraces_r D (proc1 |~| proc2)"
apply(erule otraces_r_E)
apply(clarsimp)
apply(unfold otraces_r_def)
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(simp)
apply(rule_tac x="proc1" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(proc1, u, P')#cs" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(clarsimp)
done

lemma traces_otraces_1_int_choice_2:
  "x : otraces_r D proc2
    ==> x : otraces_r D (proc1 |~| proc2)"
apply(erule otraces_r_E)
apply(clarsimp)
apply(unfold otraces_r_def)
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(simp)
apply(rule_tac x="proc2" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(proc2, u, P')#cs" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(clarsimp)
done

lemma traces_otraces_1_int_choice:
  "[| traces proc1 (%p. otraces D ($p)) <= otraces D proc1;
          traces proc2 (%p. otraces D ($p)) <= otraces D proc2 |]
       ==> traces (proc1 |~| proc2) (%p. otraces D ($p))
           <= otraces D (proc1 |~| proc2)"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
(**)
apply(rule subsetI)
apply(clarsimp)
apply(erule disjE)
apply(drule_tac c="x" and B="otraces_r D proc1" in subsetD)
apply(clarsimp)
apply(erule traces_otraces_1_int_choice_1)
apply(drule_tac c="x" and B="otraces_r D proc2" in subsetD)
apply(clarsimp)
apply(erule traces_otraces_1_int_choice_2)
done

lemma traces_otraces_1_rep_int_choice:
"(ALL x. traces (Pf x) (%p. otraces D ($p))
             <= otraces D (Pf x))
       ==> traces (!! :A .. Pf) (%p. otraces D ($p))
           <= otraces D (!! :A .. Pf)"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(rule subsetI)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="n" in spec)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule_tac c="x" in subsetD)
apply(assumption)
apply(erule otraces_r_E)
apply(clarsimp)
apply(clarsimp)
apply(subst otraces_r_def)
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(simp)
apply(rule_tac x="Pf n" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(Pf n, u, P')#cs" in exI)
apply(rule conjI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(erule ptrans_rep_int_choce)
done

lemma comps_rename [rule_format]:
  "cs : comps D ==>
    (ALL s. rename_tr R (comp_to_trace cs) s -->
    (EX cs'. cs' : comps D & length cs' = length cs &
             (comp_to_trace cs') = s &
             forall2 (%(p,u,q) (p2,v,q2).
                   p[[R]] = p2 & q[[R]] = q2 &
                   (case u of
                      Tau => v=Tau |
                      Ev a => (EX b. (a, b) : R & v=Ev b)))
               cs cs'))"
apply(erule comps.induct)
apply(clarsimp)
apply(drule rename_tr_nil2)
apply(clarsimp)
apply(clarsimp)
apply(case_tac u)
apply(clarsimp)
apply(rule_tac x="[(P[[R]], Tau, P'[[R]])]" in exI)
apply(clarsimp)
apply(drule rename_tr_nil2)
apply(clarsimp)
apply(erule ptrans_rename2)
apply(clarsimp)
apply(unfold rename_tr_def)
apply(clarsimp)
apply(case_tac s)
apply(clarsimp)
apply(clarsimp)
apply(rename_tac b)
apply(rule_tac x="[(P[[R]], Ev b, P'[[R]])]" in exI)
apply(clarsimp)
apply(erule ptrans_rename1)
apply(assumption)
(**)
apply(clarsimp)
apply(case_tac u')
apply(clarsimp)
apply(drule_tac x="s" in spec)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(case_tac u)
apply(clarsimp)
apply(rule_tac x="(P''[[R]], Tau, P[[R]])#(P [[R]], Tau, P' [[R]]) # list" in exI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(erule ptrans_rename2)
(**)
apply(clarsimp)
apply(rule_tac x="(P''[[R]], Tau, P[[R]])#(P [[R]], Ev b, P' [[R]]) # list" in exI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(erule ptrans_rename2)
(**)
apply(clarsimp)
apply(case_tac s)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="list" in spec)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(case_tac u)
apply(clarsimp)
apply(rule_tac x="(P''[[R]], Ev aa, P[[R]])#(P [[R]], Tau, P' [[R]]) # list" in exI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(erule ptrans_rename1)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="(P''[[R]], Ev aa, P[[R]])#(P [[R]], Ev b, P' [[R]]) # list" in exI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(erule ptrans_rename1)
apply(assumption)
done

lemma traces_otraces_1_rename:
  "traces P (%p. otraces D ($p)) <= otraces D P
       ==> traces (P[[R]]) (%p. otraces D ($p))
           <= otraces D (P[[R]])"
apply(unfold traces_def otraces_def)
apply(rule Abs_domT_I)
defer
apply(rule traces_r_domT)
apply(rule otraces_domT)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule otraces_domT)
(**)
apply(rule subsetI)
apply(clarsimp)
apply(drule subsetD)
apply(assumption)
apply(erule otraces_r_E)
apply(clarsimp)
apply(drule rename_tr_nil2)
apply(clarsimp)
apply(clarsimp)
apply(unfold otraces_r_def)
apply(clarsimp)
apply(drule comps_rename)
apply(assumption)
apply(clarsimp)
apply(rotate_tac 2)
apply(erule contrapos_pp)
apply(simp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(case_tac u)
apply(clarsimp)
apply(rule_tac x="P'[[R]]" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="list" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="P'[[R]]" in exI)
apply(rule_tac x="Ev b" in exI)
apply(rule_tac x="list" in exI)
apply(clarsimp)
done

lemma traces_otraces_1: "traces P (%p. otraces D ($p)) <= otraces D P"
apply(induct_tac P)
apply(rule traces_otraces_1_STOP)
apply(erule traces_otraces_1_prefix)
apply(rule traces_otraces_1_prefix_choice)
apply(clarsimp)
apply(erule traces_otraces_1_ext_choice)
apply(clarsimp)
apply(erule traces_otraces_1_int_choice)
apply(clarsimp)
apply(rule traces_otraces_1_rep_int_choice)
apply(clarsimp)
apply(erule traces_otraces_1_if)
apply(clarsimp)
apply(erule traces_otraces_1_par)
apply(clarsimp)
apply(erule traces_otraces_1_hide)
apply(erule traces_otraces_1_rename)
apply(rule traces_otraces_1_pn)
done

lemma otraces_r_unfold1_0:
 "ALL D p. otraces_r D ($p) = otraces_r D (D p)"
apply(rule allI)+
apply(unfold otraces_r_def)
apply(rule subset_antisym)
apply(rule subsetI)
apply(clarsimp)
apply(erule contrapos_pp)
apply(simp)
apply(frule comps_car)
apply(erule ptrans_cases_pn)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(rule_tac x="b" in exI)
apply(rule_tac x="aa" in exI)
apply(rule_tac x="list" in exI)
apply(rule conjI)
apply(clarsimp)
apply(erule comps_cdr)
(**)
apply(clarsimp)
apply(erule contrapos_pp)
apply(simp)
apply(frule comps_car)
apply(drule ptrans_pn)
apply(drule comps_step2)
apply(assumption)
apply(rule_tac x="D p" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(D p, u, P') # cs" in exI)
apply(rule conjI)
apply(clarsimp)
apply(clarsimp)
done

lemma otraces_r_unfold1:
 "otraces_r D ($p) = otraces_r D (D p)"
by (metis otraces_r_unfold1_0)

lemma otraces_unfold1: "otraces D ($p) = otraces D (D p)"
apply(unfold otraces_def)
by (metis otraces_r_unfold1_0)

lemma opsem_F_1:
  "F D (%p. otraces D ($p)) <= (%p. otraces D ($p))"
apply(unfold F_def)
apply(subst le_fun_def)
apply(clarsimp)
apply(rename_tac q)
apply(subst (2) otraces_unfold1)
apply(rule traces_otraces_1)
done

lemma deno_sem_otraces:
  "deno_sem D <= (%p. otraces D ($p))"
apply(unfold deno_sem_def)
(* apply(rule lfp_induct) *)
apply(rule lfp_lowerbound)
(* apply(rule mono_csp) *)
apply(rule opsem_F_1)
done

lemma comps_conn_head:
  "[| cs : comps D;
      (P', u', P) : ptrans D;
      cs ~= [] --> fst (hd cs) = P |] ==>
    (P', u', P)#cs : comps D"
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
by (metis comps.comps_step2)


lemma comp_to_trace_tau_forall [rule_format]:
  "forall (%(p,u,q). u=Tau) cs --> comp_to_trace cs = []"
apply(induct_tac cs)
apply(auto)
done

fun comps_par ::
               "'a set =>
                ((('p, 'a)proc * 'a event * ('p, 'a)proc) list) =>
                ((('p, 'a)proc * 'a event * ('p, 'a)proc) list) =>
                ((('p, 'a)proc * 'a event * ('p, 'a)proc) list) => bool" where
  "comps_par X [] csp csq = (csp = [] & csq = [])"
| "comps_par X ((R, u, R')#cs) csp csq =
    (EX P Q P' Q' csp' csq' a. R = P |[X]| Q & R' = P' |[X]| Q' &
     ((u=Ev a & a:X & csp=(P, Ev a, P')#csp' & csq=(Q, Ev a, Q')#csq' & comps_par X cs csp' csq') |
      (u=Ev a & a~:X & csp=(P, Ev a, P')#csp' & csq=csq' & Q=Q' & comps_par X cs csp' csq) |
      (u=Ev a & a~:X & csp=csp' & csq=(Q, Ev a, Q')#csq' & P=P' & comps_par X cs csp csq') |
      (u=Tau & csp=(P, Tau, P')#csp' & csq=csq' & Q=Q' & comps_par X cs csp' csq) |
      (u=Tau & csp=csp' & csq=(Q, Tau, Q')#csq' & P=P' & comps_par X cs csp csq')))"

lemma comps_par_sub:
  "cs : comps D ==>
     cs ~= [] -->
     (EX X P Q. fst(hd cs) = P |[X]| Q) -->
     (EX X csp csq. comps_par X cs csp csq)"
apply(erule comps.induct)
apply(clarsimp)
apply(clarsimp)
apply(erule ptrans_cases_par)
apply(blast)+
apply(clarsimp)
apply(erule ptrans_cases_par)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(clarsimp)
apply metis
(**)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(clarsimp)
apply metis
(**)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(clarsimp)
apply metis
(**)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(clarsimp)
apply metis
(**)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(erule disjE)
apply(clarsimp)
apply metis
apply(clarsimp)
apply metis
done

lemma par_csp_csq_hd [rule_format]:
  "ALL P Q P' Q' u csp csq.
   cs : comps D -->
     cs ~= [] -->
     comps_par X cs csp csq -->
       (csp ~= [] --> (EX Q. fst (hd csp) |[X]| Q = fst (hd cs))) &
       (csq ~= [] --> (EX P. P |[X]| fst (hd csq) = fst (hd cs)))"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(case_tac list)
apply(clarsimp)
apply (metis fst_conv list.sel(1))
(**)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csq')
apply(clarsimp)
apply(clarsimp)
apply (metis comps_connect fst_conv list.distinct(1) list.sel(1) proc.inject(7))
apply(erule disjE)
apply(clarsimp)
apply (metis comps_connect fst_conv fst_eqD list.sel(1) not_Cons_self2 proc.inject(7))
apply(erule disjE)
apply(clarsimp)
apply (metis comps_connect fst_conv fst_eqD list.sel(1) not_Cons_self2 proc.inject(7))
apply(clarsimp)
by (metis comps_connect fst_eqD list.sel(1) proc.inject(7))

lemma par_comps_connect_1:
  "[| (P |[X]| Q, u, P' |[X]| Q')#cs : comps D;
      comps_par X cs csp csq;
      csp : comps D;
      (P'', v, P') : ptrans D |]
  ==> (P'', v, P')#csp : comps D"
apply(case_tac cs)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(drule par_csp_csq_hd)
apply(clarsimp)
apply(assumption)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(erule disjE)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(erule disjE)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(clarsimp)
by (metis comps.comps_step2)

lemma par_comps_connect_2:
  "[| (P |[X]| Q, u, P' |[X]| Q')#cs : comps D;
      comps_par X cs csp csq;
      csq : comps D;
      (Q'', v, Q') : ptrans D |]
  ==> (Q'', v, Q')#csq : comps D"
apply(case_tac cs)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(drule par_csp_csq_hd)
apply(clarsimp)
apply(assumption)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(erule disjE)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(clarsimp)
by (metis comps.comps_step2)

lemma comps_par_sub2 [rule_format]:
  "cs : comps D -->
     cs ~= [] -->
     (EX X P Q. fst(hd cs) = P |[X]| Q) -->
     (EX X csp csq. comps_par X cs csp csq &
           csp : comps D & csq : comps D)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(case_tac list)
apply(clarsimp)
apply(drule comps_car)
apply(erule ptrans_cases_par)
apply(blast)+
(**)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_par)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P')#(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev ac,Q')#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev ac,Q')#csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P')#(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev ac,Q')#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q,Ev ac,Q')#csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(rule conjI)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_1)
apply(assumption)
apply(assumption)
apply(assumption)
apply(assumption)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P')#(P',Tau,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P',Tau,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Tau,Q')#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q,Tau,Q')#csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_1)
apply(assumption)+
(****)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev ac,P')#csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q')#(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P,Ev ac,P')#csp'" in exI)
apply(rule_tac x="(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev ac,P')#csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P,Ev ac,P')#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_2)
apply(assumption)+
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q')#(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Tau,P')#csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P,Tau,P')#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_2)
apply(assumption)+
(**)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q')#(Q',Tau,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q',Tau,Q'a)#csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
(****)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P')#(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q')#(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(rule conjI)
apply (metis comps.comps_step2)
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P')#(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply (metis comps.comps_step2 comps_cdr par_comps_connect_2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q')#(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(rule conjI)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_1)
apply(assumption)+
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P')#(P',Tau,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P',Tau,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(rule conjI)
apply (metis comps.comps_step2)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_2)
apply(assumption)+
(**)
apply(clarsimp)
apply(rule_tac x="(P,Ev e,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev e,Q')#(Q',Tau,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q',Tau,Q'a)#csq'" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(rule conjI)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_1)
apply(assumption)+
apply (metis comps.comps_step2)
(****)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Tau,P')#(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev ac,Q')#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev ac,Q')#csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Tau,P')#(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P',Ev ac,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Tau,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Ev ac,Q')#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q,Ev ac,Q')#csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_1)
apply(assumption)+
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Tau,P')#(P',Tau,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P',Tau,P'a)#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(clarsimp)
apply(rule_tac x="(P,Tau,P'a)#csp'" in exI)
apply(rule_tac x="(Q,Tau,Q')#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q,Tau,Q')#csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_1)
apply(assumption)+
(****)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev ac,P')#csp'" in exI)
apply(rule_tac x="(Q,Tau,Q')#(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P,Ev ac,P')#csp'" in exI)
apply(rule_tac x="(Q',Ev ac,Q'a)#csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Ev ac,P')#csp'" in exI)
apply(rule_tac x="(Q,Tau,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P,Ev ac,P')#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_2)
apply(assumption)+
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q,Tau,Q') #(Q',Ev ac,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q',Ev ac,Q'a)#csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
(**)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P,Tau,P')#csp'" in exI)
apply(rule_tac x="(Q,Tau,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="(P,Tau,P')#csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(erule par_comps_connect_2)
apply(assumption)+
(**)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q,Tau,Q')#(Q',Tau,Q'a)#csq'" in exI)
apply(rule conjI)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="(Q',Tau,Q'a)#csq'" in exI)
apply(clarsimp)
apply(rule_tac x="csp'" in exI)
apply(rule_tac x="csq'" in exI)
apply(clarsimp)
apply(clarsimp)
apply (metis comps.comps_step2)
done

lemma sync_no_sync_1 [rule_format]:
  "ALL u s.
     u : sync X s t -->
          a ~: X -->
       (a # u) : sync X (a # s) t"
apply(induct_tac t)
apply(auto)
apply(case_tac s)
apply(auto)
done

lemma sync_no_sync_2 [rule_format]:
  "ALL u t.
     u : sync X s t -->
          a ~: X -->
       (a # u) : sync X s (a#t)"
apply(induct_tac s)
apply(clarsimp)
apply(clarsimp)
done

lemma comps_par_traces_sync [rule_format]:
  "ALL csp csq.
    comps_par X cs csp csq
       --> comp_to_trace cs : sync X (comp_to_trace csp) (comp_to_trace csq)"
apply(induct_tac cs)
apply(auto)
apply(rule sync_no_sync_1)
apply metis
apply(assumption)
apply(rule sync_no_sync_2)
apply metis
apply(assumption)
done

lemma a_Abs_domT_I: "[| Rep_domT a <= r; r : domT |] ==> a <= Abs_domT r"
by (metis Abs_domT_inverse domT_less_eq_def)

lemma comps_hide:
  "ALL D cs X.
  cs : comps D -->
  cs ~= [] -->
  (EX P. fst(hd cs) = P -- X) -->
  (EX cs'. cs' : comps D &
             forall2 (%(p,u,q) (p2,v,q2).
                         p = p2 -- X &
                         q = q2 -- X &
                         u = (case v of Tau => Tau | Ev a => if a:X then Tau else Ev a)
                     ) cs cs')"
apply(rule allI)
apply(rule allI)
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(drule comps_car)
apply(erule ptrans_cases_hide)
apply(clarsimp)
apply(rule_tac x="[(P, Ev e, P')]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="[(P, Ev e, P')]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="[(P, Tau, P')]" in exI)
apply(clarsimp)
(**)
apply(clarsimp)
apply(frule comps_car)
apply(frule comps_connect)
apply(clarsimp)
apply(erule ptrans_cases_hide)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(clarsimp)
apply(rule_tac x="(P, Ev e, P')#cs'" in exI)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="(P, Ev e, a)#(a,aa,b)#list" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="(P, Tau, a)#(a,aa,b)#list" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
done

lemma hide_seq:
  "ALL cs X cs'.
      forall2
           (%(p, u, q) (p2, v, q2).
               p = p2 -- X &
               q = q2 -- X &
               u = (case v of Tau => Tau | Ev a => if a : X then Tau else Ev a))
           cs cs' -->
     comp_to_trace cs = ceal X (comp_to_trace cs')"
apply(rule allI)
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(case_tac ab)
apply(clarsimp)
apply(clarsimp)
apply(case_tac "a:X")
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(case_tac ac)
apply(clarsimp)
apply(clarsimp)
apply(case_tac "a:X")
apply(clarsimp)
apply(clarsimp)
done

lemma ptrans_c_ev0 [rule_format]:
  "(P, u, P') : ptrans D ==>
     (EX e. u = Ev e) --> (ptel m P, u, ptel m P') : ptrans (G D)"
apply(erule ptrans.induct)
apply(auto)
apply(rule ptrans_prefix)
apply (metis ptrans_prefix_choice)
apply (metis ptrans_ext_choice1)
apply (metis ptrans_ext_choice2)
apply (metis ptrans_par1)
apply (metis ptrans_par2)
apply (metis ptrans_par3)
apply(metis ptrans_hide1)
by (metis ptrans.ptrans_rename1)

lemma ptrans_c_ev:
  "(P, Ev e, P') : ptrans D ==> (ptel m P, Ev e, ptel m P') : ptrans (G D)"
apply(erule ptrans_c_ev0)
apply(simp)
done

lemma finite_ptelset_ptel [intro]:
  "finite (ptelset (ptel m P))"
apply(induct_tac P)
apply(auto)
apply (metis finite.emptyI finite_insert finite_subset ptel.simps(3) ptelset.simps(3) ptelset_ptel)
by (metis finite.emptyI finite_insert finite_subset ptel.simps(6) ptelset.simps(6) ptelset_ptel)

lemma ptrans_c_pbound [rule_format, intro]:
  "(P, u, Q) : ptrans (G D) ==>
   pbound P -->
   pbound Q"
apply(erule ptrans.induct)
apply(unfold pbound_def)
apply(auto)
apply (metis (mono_tags, lifting) SUP_identity_eq Sup_set_def Sup_upper mem_Collect_eq rev_finite_subset)
apply (metis (mono_tags, lifting) SUP_identity_eq Sup_set_def Sup_upper mem_Collect_eq rev_finite_subset)
apply(erule contrapos_np)
apply(unfold G_def)
apply(clarsimp)
apply(case_tac b)
apply(clarsimp)
apply(clarsimp)
apply(rule finite_subset)
apply(rule ptelset_ptel)
apply(clarsimp)
apply(case_tac b)
apply(clarsimp)
apply(clarsimp)
apply(rule finite_subset)
apply(rule ptelset_ptel)
apply(clarsimp)
done

lemma ptrans_c:
  "(P, u, Q) : ptrans (G D) ==>
   (rmtel P, u, rmtel Q) : ptrans D"
apply(erule ptrans.induct)
apply(auto)
apply (metis ptrans.ptrans_prefix)
apply (metis ptrans.ptrans_prefix_choice)
apply (metis ptrans.ptrans_ext_choice1)
apply (metis ptrans.ptrans_ext_choice2)
apply (metis ptrans.ptrans_ext_choice3)
apply (metis ptrans.ptrans_ext_choice4)
apply (metis ptrans.ptrans_rep_int_choce)
apply(rule ptrans_par1)
apply(assumption)
apply(assumption)
apply(rule ptrans_par2)
apply(assumption)
apply(assumption)
apply(rule ptrans_par3)
apply(assumption)
apply(assumption)
apply(assumption)
apply(rule ptrans_par4)
apply(assumption)
apply(rule ptrans_par5)
apply(assumption)
apply(erule ptrans_hide1)
apply(assumption)
apply(erule ptrans_hide2)
apply(assumption)
apply(erule ptrans_hide3)
apply(erule ptrans_rename1)
apply(assumption)
apply(erule ptrans_rename2)
apply (metis ptrans.ptrans_if1)
apply(metis ptrans.ptrans_if2)
apply(unfold G_def)
apply(clarsimp)
apply(case_tac b)
apply(clarsimp)
apply(erule ptrans_cases_STOP)
apply(clarsimp)
by (metis (no_types, hide_lams) ptrans.ptrans_pn)


lemma ptrans_ptrans_0 [rule_format]:
  "(P, u, P') : ptrans D ==>
      EX m Q. (ptel m P, u, Q) : ptrans (G D) &
               rmtel Q = P'"
apply(erule ptrans.induct)
apply(rule_tac x="0" in exI)
apply(rule_tac x="ptel 0 P" in exI)
apply(clarsimp)
apply (metis ptrans_prefix)
apply(rule_tac x="0" in exI)
apply(rule_tac x="ptel 0 (Pf a)" in exI)
apply(clarsimp)
apply (metis ptrans_prefix_choice)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Qa" in exI)
apply(clarsimp)
apply (metis ptrans_ext_choice1)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Qa" in exI)
apply(clarsimp)
apply (metis ptrans_ext_choice2)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Qa [+] ptel m Q" in exI)
apply(clarsimp)
apply (metis ptrans_ext_choice3)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="ptel m P [+] Qa" in exI)
apply(clarsimp)
apply (metis ptrans_ext_choice4)
apply(clarsimp)
apply(rule_tac x="0" in exI)
apply(rule_tac x="ptel 0 P" in exI)
apply(clarsimp)
apply(rule_tac x="0" in exI)
apply(rule_tac x="ptel 0 Q" in exI)
apply(clarsimp)
apply(rule_tac x="0" in exI)
apply(rule_tac x="ptel 0 (Pf x)" in exI)
apply(clarsimp)
apply (metis ptrans.ptrans_rep_int_choce)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Qa |[X]| ptel m Q" in exI)
apply(clarsimp)
apply(erule ptrans_par1)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="ptel m P |[X]| Qa" in exI)
apply(clarsimp)
apply(erule ptrans_par2)
apply(assumption)
apply(clarsimp)
apply(drule_tac m="0" in ptrans_c_ev)
apply(drule_tac m="0" in ptrans_c_ev)
apply(rule_tac x="0" in exI)
apply(rule_tac x="ptel 0 (rmtel Qa) |[X]| ptel 0 (rmtel Qb)" in exI)
apply(rule conjI)
apply(erule ptrans_par3)
apply(assumption)
apply(assumption)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Qa |[X]| ptel m Q" in exI)
apply(clarsimp)
apply(erule ptrans_par4)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="ptel m P |[X]| Qa" in exI)
apply(clarsimp)
apply(erule ptrans_par5)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Q -- X" in exI)
apply(clarsimp)
apply(erule ptrans_hide1)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Q -- X" in exI)
apply(clarsimp)
apply(erule ptrans_hide2)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Q -- X" in exI)
apply(clarsimp)
apply(erule ptrans_hide3)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Q[[R]]" in exI)
apply(clarsimp)
apply(erule ptrans_rename1)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="Q[[R]]" in exI)
apply(clarsimp)
apply(erule ptrans_rename2)
apply(rule_tac x="0" in exI)
apply(rule_tac x="ptel 0 P" in exI)
apply(clarsimp)
apply (metis ptrans_if1)
apply(clarsimp)
apply(rule_tac x="0" in exI)
apply(rule_tac x="ptel 0 Q" in exI)
apply(clarsimp)
apply (metis ptrans_if2)
apply(clarsimp)
apply(rule_tac x="Suc m" in exI)
apply(rule_tac x="ptel m (D p)" in exI)
apply(clarsimp)
apply(subgoal_tac "($(p, Suc m), Tau, (G D) (p, Suc m)) : ptrans (G D)")
defer
apply(rule ptrans_pn)
apply(subst G_def)
apply(clarsimp)
apply(assumption)
apply(unfold G_def)
apply(clarsimp)
done

lemma forall2_append [rule_format]:
  "ALL xs2 ys1 ys2. length xs1 = length ys1 --> length xs2 = length ys2 --> forall2 f (xs1 @ xs2) (ys1 @ ys2) --> forall2 f xs1 ys1 & forall2 f xs2 ys2"
apply(induct_tac xs1)
apply(clarsimp)
apply(clarsimp)
apply(case_tac ys1)
apply(clarsimp)
apply(clarsimp)
done

lemma forall2_appD:
  "[| forall2 f (xs1 @ xs2) (ys1 @ ys2); length xs1 = length ys1; length xs2 = length ys2 |]
  ==> forall2 f xs1 ys1 & forall2 f xs2 ys2"
apply(rule forall2_append)
apply(auto)
done

lemma forall2_rev [rule_format]:
  "ALL ys. length xs = length ys --> forall2 f (rev xs) (rev ys) --> forall2 f xs ys"
apply(induct_tac xs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac ys)
apply(clarsimp)
apply(clarsimp)
apply(drule forall2_appD)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
done

lemma forall2_rev2:
  "[| forall2 f xs ys; length xs = length ys |]
  ==> forall2 f (rev xs) (rev ys)"
apply(rule forall2_rev)
apply(auto)
done

primrec otel :: "nat => ('p * nat, 'a) proc => ('p * nat, 'a) proc" where
  "otel m STOP = STOP" |
  "otel m (a->P) = a->(otel m P)" |
  "otel m (?:A->Pf) = (?:A->(%a. otel m (Pf a)))" |
  "otel m (P[+]Q) = (otel m P)[+](otel m Q)" |
  "otel m (P|~|Q) = (otel m P)|~|(otel m Q)" |
  "otel m (!!:A..Pf) = (!!:A..(%a. otel m (Pf a)))" |
  "otel m (P|[X]|Q) = (otel m P) |[X]| (otel m Q)" |
  "otel m (P--X) = (otel m P)--X" |
  "otel m (P[[R]]) = (otel m P)[[R]]" |
  "otel m (IF b THEN P ELSE Q) = (IF b THEN (otel m P) ELSE (otel m Q))" |
  "otel m ($p) = $(fst p, snd p + m)"

primrec atel :: "('p * nat, 'a) proc => ('p * nat, 'a) proc => ('p * nat, 'a) proc" where
  "atel STOP R = STOP" |
  "atel (a->P) R = (case R of (a'->P') => a->(atel P P') | _ => a->P)" |
  "atel (?:A->Pf) R = (case R of (?:A'->Pf') => (?:A->(%a. atel (Pf a) (Pf' a))) | _ => (?:A->Pf))" |
  "atel (P[+]Q) R = (case R of (P'[+]Q') => (atel P P')[+](atel Q Q') | _ => (P[+]Q))" |
  "atel (P|~|Q) R = (case R of (P'|~|Q') => (atel P P')|~|(atel Q Q') | _ => (P|~|Q))" |
  "atel (!!:A..Pf) R = (case R of (!!:A'..Pf') => (!!:A..(%a. atel (Pf a) (Pf' a))) | _ => (!!:A..Pf))" |
  "atel (P|[X]|Q) R = (case R of (P'|[X']|Q') => (atel P P') |[X]| (atel Q Q') | _ => (P|[X]|Q))" |
  "atel (P--X) R = (case R of (P'--X') => (atel P P')--X | _ => P--X)" |
  "atel (P[[r]]) R = (case R of (P'[[r']]) => (atel P P')[[r]] | _ => P[[r]])" |
  "atel (IF b THEN P ELSE Q) R = (case R of (IF b' THEN P' ELSE Q') => (IF b THEN (atel P P') ELSE (atel Q Q')) | _ => (IF b THEN P ELSE Q))" |
  "atel ($p) R = (case R of ($p') => $(fst p, snd p + snd p') | _ => $p)"

lemma otel_ptel [simp]:
  "otel m (ptel n P) = ptel (m+n) P"
apply(induct_tac P)
apply(auto)
done

lemma ptrans_otel:
  "(P, u, P') : ptrans (G D) ==>
     (otel m P, u, otel m P') : ptrans (G D)"
apply(erule ptrans.induct)
apply(clarsimp)
apply (metis ptrans.ptrans_prefix)
apply (metis otel.simps(3) ptrans.ptrans_prefix_choice)
apply (metis otel.simps(4) ptrans.ptrans_ext_choice1)
apply (metis otel.simps(4) ptrans.ptrans_ext_choice2)
apply (metis otel.simps(4) ptrans.ptrans_ext_choice3)
apply (metis otel.simps(4) ptrans.ptrans_ext_choice4)
apply (metis otel.simps(5) ptrans.ptrans_int_choce1)
apply (metis otel.simps(5) ptrans.ptrans_int_choce2)
apply (metis otel.simps(6) ptrans.ptrans_rep_int_choce)
apply (metis otel.simps(7) ptrans.ptrans_par1)
apply (metis otel.simps(7) ptrans.ptrans_par2)
apply (metis otel.simps(7) ptrans.ptrans_par3)
apply (metis otel.simps(7) ptrans.ptrans_par4)
apply (metis otel.simps(7) ptrans.ptrans_par5)
apply (metis otel.simps(8) ptrans.ptrans_hide1)
apply (metis otel.simps(8) ptrans.ptrans_hide2)
apply (metis otel.simps(8) ptrans.ptrans_hide3)
apply (metis otel.simps(9) ptrans.ptrans_rename1)
apply (metis otel.simps(9) ptrans.ptrans_rename2)
apply (metis otel.simps(10) ptrans.ptrans_if1)
apply (metis otel.simps(10) ptrans.ptrans_if2)
apply(clarsimp)
apply(subgoal_tac "($(a, b + m), Tau, (G D (a, b + m))) : ptrans (G D)")
defer
apply(rule_tac u="u" and Q="otel m Q" in ptrans_pn)
apply(unfold G_def)
apply(clarsimp)
apply(case_tac b)
apply(clarsimp)
apply(erule ptrans_cases_STOP)
apply(clarsimp)
apply(subst add.commute)
apply(clarsimp)
apply(subst add.commute)
apply(clarsimp)
apply(clarsimp)
apply(case_tac b)
apply(clarsimp)
apply(erule ptrans_cases_STOP)
apply(clarsimp)
apply(subst (2) add.commute)
apply(clarsimp)
done

lemma comps_otel:
  "cs : comps (G D) ==>
     (map (%(p,u,q). (otel m p, u, otel m q)) cs) : comps (G D)"
apply(erule comps.induct)
apply(clarsimp)
apply(clarsimp)
apply(rule ptrans_otel)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac m="m" in ptrans_otel)
by (metis comps.comps_step2)


lemma atel_rmtel_prefix:
  "ALL Q. rmtel Q = rmtel proc --> rmtel (atel proc Q) = rmtel proc
       ==> ALL Q.
              rmtel Q = rmtel (a -> proc) -->
              rmtel (atel (a -> proc) Q) = rmtel (a -> proc)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
done

lemma atel_rmtel_prefix_choice:
  "(ALL x. ALL Q.
                rmtel Q = rmtel (Pf x) -->
                rmtel (atel (Pf x) Q) = rmtel (Pf x))
       ==> ALL Q.
              rmtel Q = rmtel (? :X -> Pf) -->
              rmtel (atel (? :X -> Pf) Q) = rmtel (? :X -> Pf)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(rule ext)
by metis

lemma atel_rmtel_ext_choice:
  "[| ALL Q.
             rmtel Q = rmtel proc1 --> rmtel (atel proc1 Q) = rmtel proc1;
          ALL Q.
             rmtel Q = rmtel proc2 --> rmtel (atel proc2 Q) = rmtel proc2 |]
       ==> ALL Q.
              rmtel Q = rmtel (proc1 [+] proc2) -->
              rmtel (atel (proc1 [+] proc2) Q) = rmtel (proc1 [+] proc2)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
done

lemma atel_rmtel_int_choice:
  "[| ALL Q.
             rmtel Q = rmtel proc1 --> rmtel (atel proc1 Q) = rmtel proc1;
          ALL Q.
             rmtel Q = rmtel proc2 --> rmtel (atel proc2 Q) = rmtel proc2 |]
       ==> ALL Q.
              rmtel Q = rmtel (proc1 |~| proc2) -->
              rmtel (atel (proc1 |~| proc2) Q) = rmtel (proc1 |~| proc2)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
done

lemma atel_rmtel_rep_int_choice:
  "(ALL x. ALL Q.
                rmtel Q = rmtel (Pf x) -->
                rmtel (atel (Pf x) Q) = rmtel (Pf x))
       ==> ALL Q.
              rmtel Q = rmtel (!! :X .. Pf) -->
              rmtel (atel (!! :X .. Pf) Q) = rmtel (!! :X .. Pf)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(rule ext)
by metis

lemma atel_rmtel_if:
  "[| ALL Q.
             rmtel Q = rmtel proc1 --> rmtel (atel proc1 Q) = rmtel proc1;
          ALL Q.
             rmtel Q = rmtel proc2 --> rmtel (atel proc2 Q) = rmtel proc2 |]
       ==> ALL Q.
              rmtel Q = rmtel (IF bool THEN proc1 ELSE proc2) -->
              rmtel (atel (IF bool THEN proc1 ELSE proc2) Q) =
              rmtel (IF bool THEN proc1 ELSE proc2)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
done

lemma atel_rmtel_par:
  "[| ALL Q.
             rmtel Q = rmtel proc1 --> rmtel (atel proc1 Q) = rmtel proc1;
          ALL Q.
             rmtel Q = rmtel proc2 --> rmtel (atel proc2 Q) = rmtel proc2 |]
       ==> ALL Q.
              rmtel Q = rmtel (proc1 |[X]| proc2) -->
              rmtel (atel (proc1 |[X]| proc2) Q) =
              rmtel (proc1 |[X]| proc2)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
done

lemma atel_rmtel_hide:
  "ALL Q. rmtel Q = rmtel proc --> rmtel (atel proc Q) = rmtel proc
       ==> ALL Q.
              rmtel Q = rmtel (proc -- X) -->
              rmtel (atel (proc -- X) Q) = rmtel (proc -- X)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
done

lemma atel_rmtel_rename:
  "ALL Q. rmtel Q = rmtel proc --> rmtel (atel proc Q) = rmtel proc
       ==> ALL Q. rmtel Q = rmtel (proc [[R]]) -->
                  rmtel (atel (proc [[R]]) Q) = rmtel (proc [[R]])"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
done

lemma atel_rmtel_pn:
  "ALL Q. rmtel Q = rmtel ($p) --> rmtel (atel ($p) Q) = rmtel ($p)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
done

lemma atel_rmtel [simp]:
  "ALL Q. rmtel Q = rmtel P --> rmtel (atel P Q) = rmtel P"
apply(induct_tac P)
apply(clarsimp)
apply(erule atel_rmtel_prefix)
apply(rule atel_rmtel_prefix_choice)
apply(clarsimp)
apply(erule atel_rmtel_ext_choice)
apply(clarsimp)
apply(erule atel_rmtel_int_choice)
apply(clarsimp)
apply(rule atel_rmtel_rep_int_choice)
apply(clarsimp)
apply(erule atel_rmtel_if)
apply(clarsimp)
apply(erule atel_rmtel_par)
apply(clarsimp)
apply(erule atel_rmtel_hide)
apply(rule atel_rmtel_rename)
apply(clarsimp)
apply(rule atel_rmtel_pn)
done


lemma [simp]: "G D (p, Suc n) = ptel n (D p)"
apply(unfold G_def)
apply(clarsimp)
done

lemma [simp]: "G  D (p, 0) = STOP"
apply(unfold G_def)
apply(clarsimp)
done

lemma [dest!]: "(G D (p, 0), u, Q) : ptrans (G D) ==> False"
apply(unfold G_def)
apply(clarsimp)
apply(erule ptrans_cases_STOP)
done

lemma [dest!]: "(STOP, u, Q) : ptrans D ==> False"
apply(erule ptrans_cases_STOP)
done

lemma ptrans_atel_prefix:
  "ALL Q.
          rmtel Q = rmtel (a -> P) -->
          (EX Q'.
              (atel (a -> P) Q, Ev a, Q') : ptrans (G D) &
              rmtel Q' = rmtel P)"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(rule_tac x="atel P proc" in exI)
apply(clarsimp)
apply(rule ptrans_prefix)
done

lemma ptrans_atel_prefix_choice:
  "a : A
       ==> ALL Q.
              rmtel Q = rmtel (? :A -> Pf) -->
              (EX Q'.
                  (atel (? :A -> Pf) Q, Ev a, Q') : ptrans (G D) &
                  rmtel Q' = rmtel (Pf a))"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(rule_tac x="atel (Pf a) (fun a)" in exI)
apply(rule conjI)
apply(erule ptrans_prefix_choice)
by (metis atel_rmtel)

lemma ptrans_atel_ext_choice1:
  "[| (P, Ev e, P') : ptrans (G D);
          ALL Q.
             rmtel Q = rmtel P -->
             (EX Q'.
                 (atel P Q, Ev e, Q') : ptrans (G D) &
                 rmtel Q' = rmtel P') |]
       ==> ALL Qa.
              rmtel Qa = rmtel (P [+] Q) -->
              (EX Q'.
                  (atel (P [+] Q) Qa, Ev e, Q') : ptrans (G D) &
                  rmtel Q' = rmtel P')"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(drule_tac x="proc1" in spec)
apply(clarsimp)
apply(rule_tac x="Q'" in exI)
apply(clarsimp)
apply(erule ptrans_ext_choice1)
done

lemma ptrans_atel_ext_choice2:
  "[| (Q, Ev e, Q') : ptrans (G D);
          ALL Qa.
             rmtel Qa = rmtel Q -->
             (EX Q'a.
                 (atel Q Qa, Ev e, Q'a) : ptrans (G D) &
                 rmtel Q'a = rmtel Q') |]
       ==> ALL Qa.
              rmtel Qa = rmtel (P [+] Q) -->
              (EX Q'a.
                  (atel (P [+] Q) Qa, Ev e, Q'a) : ptrans (G D) &
                  rmtel Q'a = rmtel Q')"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(drule_tac x="proc2" in spec)
apply(clarsimp)
apply(rule_tac x="Q'a" in exI)
apply(clarsimp)
apply(erule ptrans_ext_choice2)
done

lemma ptrans_atel_ext_choice3:
  "[| (P, Tau, P') : ptrans (G D);
          ALL Q.
             rmtel Q = rmtel P -->
             (EX Q'.
                 (atel P Q, Tau, Q') : ptrans (G D) &
                 rmtel Q' = rmtel P') |]
       ==> ALL Qa.
              rmtel Qa = rmtel (P [+] Q) -->
              (EX Q'.
                  (atel (P [+] Q) Qa, Tau, Q') : ptrans (G D) &
                  rmtel Q' = rmtel (P' [+] Q))"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(drule_tac x="proc1" in spec)
apply(clarsimp)
apply(rule_tac x="Q' [+] atel Q proc2" in exI)
apply(clarsimp)
apply(erule ptrans_ext_choice3)
done

lemma ptrans_atel_ext_choice4:
  "[| (Q, Tau, Q') : ptrans (G D);
          ALL Qa.
             rmtel Qa = rmtel Q -->
             (EX Q'a.
                 (atel Q Qa, Tau, Q'a) : ptrans (G D) &
                 rmtel Q'a = rmtel Q') |]
       ==> ALL Qa.
              rmtel Qa = rmtel (P [+] Q) -->
              (EX Q'a.
                  (atel (P [+] Q) Qa, Tau, Q'a) : ptrans (G D) &
                  rmtel Q'a = rmtel (P [+] Q'))"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(drule_tac x="proc2" in spec)
apply(clarsimp)
apply(rule_tac x="atel P proc1 [+] Q'a" in exI)
apply(clarsimp)
apply(erule ptrans_ext_choice4)
done

lemma ptrans_atel_int_choice1:
  "ALL Qa.
          rmtel Qa = rmtel (P |~| Q) -->
          (EX Q'.
              (atel (P |~| Q) Qa, Tau, Q') : ptrans (G D) &
              rmtel Q' = rmtel P)"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
done

lemma ptrans_atel_int_choice2:
  "ALL Qa.
          rmtel Qa = rmtel (P |~| Q) -->
          (EX Q'.
              (atel (P |~| Q) Qa, Tau, Q') : ptrans (G D) &
              rmtel Q' = rmtel Q)"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
done

lemma ptrans_atel_rep_int_choice:
  "x : A
       ==> ALL Q.
              rmtel Q = rmtel (!! :A .. Pf) -->
              (EX Q'.
                  (atel (!! :A .. Pf) Q, Tau, Q') : ptrans (G D) &
                  rmtel Q' = rmtel (Pf x))"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(rule_tac x="atel (Pf x) (fun x)" in exI)
apply(rule conjI)
apply(erule ptrans_rep_int_choce)
by (metis atel_rmtel)

lemma ptrans_atel_par1:
  "[| (P, Ev e, P') : ptrans (G D);
           ALL Q.
              rmtel Q = rmtel P -->
              (EX Q'.
                  (atel P Q, Ev e, Q') : ptrans (G D) &
                  rmtel Q' = rmtel P');
           e ~: X |]
        ==> ALL Qa.
               rmtel Qa = rmtel (P |[X]| Q) -->
               (EX Q'.
                   (atel (P |[X]| Q) Qa, Ev e, Q') : ptrans (G D) &
                   rmtel Q' = rmtel (P' |[X]| Q))"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(drule_tac x="proc1" in spec)
apply(clarsimp)
apply(rule_tac x="Q' |[X]| atel Q proc2" in exI)
apply(clarsimp)
apply(erule ptrans_par1)
apply(assumption)
done

lemma ptrans_atel_par2:
  "[| (Q, Ev e, Q') : ptrans (G D);
           ALL Qa.
              rmtel Qa = rmtel Q -->
              (EX Q'a.
                  (atel Q Qa, Ev e, Q'a) : ptrans (G D) &
                  rmtel Q'a = rmtel Q');
           e ~: X |]
        ==> ALL Qa.
               rmtel Qa = rmtel (P |[X]| Q) -->
               (EX Q'a.
                   (atel (P |[X]| Q) Qa, Ev e, Q'a) : ptrans (G D) &
                   rmtel Q'a = rmtel (P |[X]| Q'))"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(drule_tac x="proc2" in spec)
apply(clarsimp)
apply(rule_tac x="atel P proc1 |[X]| Q'a" in exI)
apply(clarsimp)
apply(erule ptrans_par2)
apply(assumption)
done

lemma ptrans_atel_par3:
  "[| (P, Ev e, P') : ptrans (G D);
           ALL Q.
              rmtel Q = rmtel P -->
              (EX Q'.
                  (atel P Q, Ev e, Q') : ptrans (G D) &
                  rmtel Q' = rmtel P');
           (Q, Ev e, Q') : ptrans (G D);
           ALL Qa.
              rmtel Qa = rmtel Q -->
              (EX Q'a.
                  (atel Q Qa, Ev e, Q'a) : ptrans (G D) &
                  rmtel Q'a = rmtel Q');
           e : X |]
        ==> ALL Qa.
               rmtel Qa = rmtel (P |[X]| Q) -->
               (EX Q'a.
                   (atel (P |[X]| Q) Qa, Ev e, Q'a) : ptrans (G D) &
                   rmtel Q'a = rmtel (P' |[X]| Q'))"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(drule_tac x="proc1" in spec)
apply(drule_tac x="proc2" in spec)
apply(clarsimp)
apply(rule_tac x="Q'a |[X]| Q'aa" in exI)
apply(clarsimp)
apply(erule ptrans_par3)
apply(assumption)
apply(assumption)
done

lemma ptrans_atel_par4:
  "[| (P, Tau, P') : ptrans (G D);
           ALL Q.
              rmtel Q = rmtel P -->
              (EX Q'.
                  (atel P Q, Tau, Q') : ptrans (G D) &
                  rmtel Q' = rmtel P') |]
        ==> ALL Qa.
               rmtel Qa = rmtel (P |[X]| Q) -->
               (EX Q'.
                   (atel (P |[X]| Q) Qa, Tau, Q') : ptrans (G D) &
                   rmtel Q' = rmtel (P' |[X]| Q))"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(drule_tac x="proc1" in spec)
apply(clarsimp)
apply(rule_tac x="Q' |[X]| atel Q proc2" in exI)
apply(clarsimp)
apply(erule ptrans_par4)
done

lemma ptrans_atel_par5:
  "[| (Q, Tau, Q') : ptrans (G D);
           ALL Qa.
              rmtel Qa = rmtel Q -->
              (EX Q'a.
                  (atel Q Qa, Tau, Q'a) : ptrans (G D) &
                  rmtel Q'a = rmtel Q') |]
        ==> ALL Qa.
               rmtel Qa = rmtel (P |[X]| Q) -->
               (EX Q'a.
                   (atel (P |[X]| Q) Qa, Tau, Q'a) : ptrans (G D) &
                   rmtel Q'a = rmtel (P |[X]| Q'))"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(drule_tac x="proc2" in spec)
apply(clarsimp)
apply(rule_tac x="atel P proc1 |[X]| Q'a" in exI)
apply(clarsimp)
apply(erule ptrans_par5)
done

lemma ptrans_atel_hide1:
  "[| (P, Ev e, P') : ptrans (G D);
           ALL Q.
              rmtel Q = rmtel P -->
              (EX Q'.
                  (atel P Q, Ev e, Q') : ptrans (G D) &
                  rmtel Q' = rmtel P');
           e ~: X |]
        ==> ALL Q.
               rmtel Q = rmtel (P -- X) -->
               (EX Q'.
                   (atel (P -- X) Q, Ev e, Q') : ptrans (G D) &
                   rmtel Q' = rmtel (P' -- X))"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(drule_tac x="proc" in spec)
apply(clarsimp)
apply(rule_tac x="Q' -- X" in exI)
apply(clarsimp)
apply(erule ptrans_hide1)
apply(assumption)
done

lemma ptrans_atel_hide2:
  "[| (P, Ev e, P') : ptrans (G D);
           ALL Q.
              rmtel Q = rmtel P -->
              (EX Q'.
                  (atel P Q, Ev e, Q') : ptrans (G D) &
                  rmtel Q' = rmtel P');
           e : X |]
        ==> ALL Q.
               rmtel Q = rmtel (P -- X) -->
               (EX Q'.
                   (atel (P -- X) Q, Tau, Q') : ptrans (G D) &
                   rmtel Q' = rmtel (P' -- X))"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(drule_tac x="proc" in spec)
apply(clarsimp)
apply(rule_tac x="Q' -- X" in exI)
apply(clarsimp)
apply(erule ptrans_hide2)
apply(assumption)
done

lemma ptrans_atel_hide3:
  "[| (P, Tau, P') : ptrans (G D);
           ALL Q.
              rmtel Q = rmtel P -->
              (EX Q'.
                  (atel P Q, Tau, Q') : ptrans (G D) &
                  rmtel Q' = rmtel P') |]
        ==> ALL Q.
               rmtel Q = rmtel (P -- X) -->
               (EX Q'.
                   (atel (P -- X) Q, Tau, Q') : ptrans (G D) &
                   rmtel Q' = rmtel (P' -- X))"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(drule_tac x="proc" in spec)
apply(clarsimp)
apply(rule_tac x="Q' -- X" in exI)
apply(clarsimp)
apply(erule ptrans_hide3)
done

lemma ptrans_atel_rename1:
  "[| (P, Ev a, P') : ptrans (G D);
          ALL Q. rmtel Q = rmtel P -->
                 (EX Q'. (atel P Q, Ev a, Q') : ptrans (G D) & rmtel Q' = rmtel P');
          (a, b) : R |]
       ==> ALL Q. rmtel Q = rmtel (P [[R]]) -->
                  (EX Q'. (atel (P [[R]]) Q, Ev b, Q') : ptrans (G D) &
                          rmtel Q' = rmtel (P' [[R]]))"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(drule_tac x="proc" in spec)
apply(clarsimp)
apply(rule_tac x="Q'[[R]]" in exI)
apply(clarsimp)
apply(erule ptrans_rename1)
apply(assumption)
done

lemma ptrans_atel_rename2:
  "[| (P, Tau, P') : ptrans (G D);
          ALL Q. rmtel Q = rmtel P -->
                 (EX Q'. (atel P Q, Tau, Q') : ptrans (G D) & rmtel Q' = rmtel P') |]
       ==> ALL Q. rmtel Q = rmtel (P [[R]]) -->
                  (EX Q'. (atel (P [[R]]) Q, Tau, Q') : ptrans (G D) &
                          rmtel Q' = rmtel (P' [[R]]))"
apply(clarsimp)
apply(case_tac Q)
apply(auto)
apply(drule_tac x="proc" in spec)
apply(clarsimp)
apply(rule_tac x="Q'[[R]]" in exI)
apply(clarsimp)
apply(erule ptrans_rename2)
done

lemma ptrans_atel_if1:
  "b ==> ALL Qa.
                 rmtel Qa = rmtel (IF b THEN P ELSE Q) -->
                 (EX Q'.
                     (atel (IF b THEN P ELSE Q) Qa, Tau, Q')
                     : ptrans (G D) &
                     rmtel Q' = rmtel P)"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(rule_tac x="atel P proc1" in exI)
apply(clarsimp)
by (metis ptrans.ptrans_if1)

lemma ptrans_atel_if2:
  "~ b
        ==> ALL Qa.
               rmtel Qa = rmtel (IF b THEN P ELSE Q) -->
               (EX Q'.
                   (atel (IF b THEN P ELSE Q) Qa, Tau, Q') : ptrans (G D) &
                   rmtel Q' = rmtel Q)"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(rule_tac x="atel Q proc2" in exI)
apply(clarsimp)
by (metis ptrans.ptrans_if2)

lemma ptrans_atel_pn:
  "[| (G D p, u, Q) : ptrans (G D);
           ALL Qa.
              rmtel Qa = rmtel (G D p) -->
              (EX Q'.
                  (atel (G D p) Qa, u, Q') : ptrans (G D) &
                  rmtel Q' = rmtel Q) |]
        ==> ALL Q.
               rmtel Q = rmtel ($p) -->
               (EX Q'.
                   (atel ($p) Q, Tau, Q') : ptrans (G D) &
                   rmtel Q' = rmtel (G D p))"
apply(clarsimp)
apply(case_tac Qa)
apply(auto)
apply(case_tac p)
apply(clarsimp)
apply(rule_tac x="(G D) (a, ba + b)" in exI)
apply(rule conjI)
prefer 2
apply(subst G_def)
apply(subst G_def)
apply(clarsimp)
apply(rule_tac u="u" and Q="otel b Q" in ptrans_pn)
apply(drule_tac m="b" in ptrans_otel)
apply(unfold G_def)
apply(clarsimp)
apply(case_tac ba)
apply(clarsimp)
apply(case_tac b)
apply(clarsimp)
apply(clarsimp)
apply(subst add.commute)
apply(clarsimp)
done

lemma ptrans_atel:
  "(P, u, P') : ptrans (G D) ==>
    (ALL Q. rmtel Q = rmtel P -->
       (EX Q'. (atel P Q, u, Q') : ptrans (G D) & rmtel Q' = rmtel P'))"
apply(erule ptrans.induct)
apply(rule ptrans_atel_prefix)
apply(erule ptrans_atel_prefix_choice)
apply(erule ptrans_atel_ext_choice1)
apply(clarsimp)
apply(erule ptrans_atel_ext_choice2)
apply(clarsimp)
apply(erule ptrans_atel_ext_choice3)
apply(clarsimp)
apply(erule ptrans_atel_ext_choice4)
apply(clarsimp)
apply(rule ptrans_atel_int_choice1)
apply(rule ptrans_atel_int_choice2)
apply(erule ptrans_atel_rep_int_choice)
apply(erule ptrans_atel_par1)
apply(clarsimp)
apply(clarsimp)
apply(erule ptrans_atel_par2)
apply(clarsimp)
apply(clarsimp)
apply(erule ptrans_atel_par3)
apply(assumption)+
apply(erule ptrans_atel_par4)
apply(assumption)+
apply(erule ptrans_atel_par5)
apply(assumption)+
apply(erule ptrans_atel_hide1)
apply(assumption)+
apply(erule ptrans_atel_hide2)
apply(assumption)+
apply(erule ptrans_atel_hide3)
apply(assumption)+
apply(erule ptrans_atel_rename1)
apply(assumption)+
apply(erule ptrans_atel_rename2)
apply(assumption)+
apply(erule ptrans_atel_if1)
apply(erule ptrans_atel_if2)
apply(erule ptrans_atel_pn)
apply(clarsimp)
done

lemma rmtel_otel [simp]:
  "rmtel (otel m P) = rmtel P"
apply(induct_tac P)
apply(auto)
done

lemma atel_ptel_rmtel [simp]:
  "atel (ptel m (rmtel P)) P = otel m P"
apply(induct_tac P)
apply(auto)
done

lemma comps_conn_tail [rule_format]:
  "ALL P u P' u' P''.
  cs @ [(P, u, P')] : comps D -->
  (P', u', P'') : ptrans D -->
  cs @ [(P, u, P'), (P', u', P'')] : comps D"
apply(induct_tac cs)
apply(clarsimp)
apply (metis comps.comps_step1 comps.comps_step2 comps_car)
apply(clarsimp)
by (metis comp_app_div comps.comps_step1)

lemma forall2_map_2 [rule_format]:
  "ALL ys. forall2 (%x. (%y. f x (g y))) xs ys -->
           forall2 f xs (map g ys)"
apply(induct_tac xs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac ys)
apply(clarsimp)
apply(clarsimp)
done

lemma forall2_mono [rule_format]:
  "ALL ys.
     forall2 f xs ys -->
     (ALL x y. f x y --> g x y) -->
     forall2 g xs ys"
apply(induct_tac xs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac ys)
apply(clarsimp)
apply(clarsimp)
done

lemma comps_c:
  "cs : comps D -->
   cs ~= [] -->
   (EX n cs'. cs' : comps (G D) &
              length cs' = length cs &
              fst (hd cs') = ptel n (rmtel (fst (hd cs'))) &
              forall2 (%(p1, u, q1) (p2, v, q2).
                     p1 = rmtel p2 & q1 = rmtel q2 &
                     u = v)
               cs cs')"
apply(rule rev_list_induct)
apply(clarsimp)
apply(clarsimp)
apply(insert list_rev_cases)
apply(drule_tac x="x" in spec)
apply(erule disjE)
apply(clarsimp)
apply(drule comps_car)
apply(drule ptrans_ptrans_0)
apply(clarsimp)
apply(drule_tac m="0" in ptrans_otel)
apply(clarsimp)
apply(rule_tac x="m" in exI)
apply(rule_tac x="[(ptel m a, aa, otel 0 Q)]" in exI)
apply(clarsimp)
(**)
apply(clarsimp)
(* make
ys @ [(ab, ac, ba)] : comps D
(a, aa, b) : ptrans D
*)
apply(subgoal_tac "(ys @ [(ab, ac, ba)]) @ [(a, aa, b)] : comps D")
prefer 2
apply(clarsimp)
apply(rotate_tac -1)
apply(frule comps_app_D1)
apply(frule comps_app_D2)
apply(rotate_tac -3)
apply(frule comps_app_D2)
apply(rotate_tac -1)
apply(drule comps_connect)
apply(clarsimp)
(* find ptel trans for last *)
apply(drule comps_car)
apply(drule ptrans_ptrans_0)
apply(clarsimp)
(* otel hypo cs *)
apply(drule_tac m="m" in comps_otel)
(* tail div cs' *)
apply(insert list_rev_cases)
apply(drule_tac x="cs'" in spec)
apply(erule disjE)
apply(clarsimp)
apply(clarsimp)
apply(drule forall2_rev2)
apply(clarsimp)
apply(clarsimp)
(* get tail of cs' *)
apply(rotate_tac 4)
apply(frule comps_app_D2)
apply(rotate_tac -1)
apply(drule comps_car)
(* atel *)
apply(drule ptrans_atel)
apply(drule_tac x="b" in spec)
apply(drule mp)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="m+n" in exI)
apply(rule_tac x="map (%(p, u, q). (otel m p, u, otel m q)) ysa @
          [(otel m ad, ae, otel m b), (otel m b, aa, Q')]" in exI)
apply(clarsimp)
apply(case_tac ysa)
apply(clarsimp)
apply(rule conjI)
apply (metis comps.comps_step1 comps.comps_step2)
apply(rotate_tac 3)
apply(drule sym)
apply(rotate_tac -1)
apply(erule subst)
apply(clarsimp)
apply(clarsimp)
apply(rule conjI)
apply(subgoal_tac "((otel m a, ab, otel m ba) #
           map (%(p, u, q). (otel m p, u, otel m q)) list) @
        [(otel m ad, ae, otel m b), (otel m b, aa, Q')]
           : comps (G D)")
apply(clarsimp)
apply(rule comps_conn_tail)
apply(clarsimp)
apply(clarsimp)
apply(rule conjI)
apply(rotate_tac -4)
apply(erule ssubst)
apply(clarsimp)
apply(drule forall2_rev2)
apply(clarsimp)
apply(clarsimp)
apply(case_tac ys)
apply(clarsimp)
apply(clarsimp)
apply(rule forall2_rev)
apply(clarsimp)
apply(clarsimp)
apply(rule forall2_rev2)
defer
apply(clarsimp)
apply(rule forall2_map_2)
apply(erule forall2_mono)
apply(clarsimp)
done

lemma comps_comp_to_trace_eq [rule_format]:
  "ALL cs'.
      forall2 (%(p1, u, q1) (p2, v, q2).
                     p1 = rmtel p2 & q1 = rmtel q2 &
                     u = v)
                cs cs'
   --> comp_to_trace cs = comp_to_trace cs'"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(clarsimp)
apply(case_tac ac)
apply(clarsimp)
apply(clarsimp)
done

lemma otraces_r_rc:
  "s : otraces_r D P ==> EX n. s : otraces_r (G D) (ptel n P)"
apply(erule otraces_r_E)
apply(clarsimp)
apply(rule_tac x="0" in exI)
apply(clarsimp)
apply(frule comps_car)
apply(subst otraces_r_def)
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(simp)
apply(frule comps_c[rule_format])
apply(clarsimp)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="n" in exI)
apply(rule_tac x="b" in exI)
apply(rule_tac x="aa" in exI)
apply(rule_tac x="list" in exI)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(rule comps_comp_to_trace_eq)
apply(clarsimp)
apply(clarsimp)
apply(rule comps_comp_to_trace_eq)
apply(clarsimp)
done


(**************************************************************************)

lemma mono_F_n_sub:
  "(F D ^^ n) (%p. Abs_domT {[]}) <= F D ((F D ^^ n) (%p. Abs_domT {[]}))"
apply(induct_tac n)
apply(clarsimp)
apply(subst F_def)
apply(subst traces_def)
apply(rule le_funI)
apply(rule Abs_domT_I)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(subgoal_tac "mono (F D)")
apply(erule monoD)
apply(assumption)
apply(rule mono_csp)
done

lemma mono_F_n:
  "ALL D n2 n1. n1 <= n2 --> (F D ^^ n1) (%p. Abs_domT {[]}) <= (F D ^^ n2) (%p. Abs_domT {[]})"
apply(rule allI)
apply(rule allI)
apply(induct_tac n2)
apply(clarsimp)
apply(clarsimp)
apply(case_tac "n1=Suc n")
apply(clarsimp)
apply(drule_tac x="n1" in spec)
apply(clarsimp)
apply(subgoal_tac "(F D ^^ n) (%p. Abs_domT {[]}) <= F D ((F D ^^ n) (%p. Abs_domT {[]}))")
apply(erule order_trans)
apply(assumption)
apply(rule mono_F_n_sub)
done

lemma mono_traces_r:
  "m1 <= m2 ==> traces_r P m1 <= traces_r P m2"
apply(insert mono_traces)
apply(drule_tac x="P" in spec)
apply(unfold mono_def)
apply(unfold traces_def)
apply(drule_tac x="m1" in spec)
apply(drule_tac x="m2" in spec)
apply(clarsimp)
apply(drule Abs_domT_D)
apply(rule traces_r_domT)
apply(rule traces_r_domT)
apply(erule subsetD)
apply(assumption)
done

lemma traces_r_n_mono:
  "[| s : traces_r P ((F D ^^ k) (%p. Abs_domT {[]})); k <= n |] 
  ==> s : traces_r P ((F D ^^ n) (%p. Abs_domT {[]}))"
apply(rule subsetD)
defer
apply(assumption)
apply(rule mono_traces_r)
apply(rule mono_F_n[rule_format])
apply(assumption)
done
lemma Abs_domT_I2: "[| r <= Rep_domT a; r : domT |] ==> Abs_domT r <= a"
by (metis Rep_domT Rep_domT_inverse domT_Abs_mono)

lemma Rep_domT_I: "x <= y ==> Rep_domT x <= Rep_domT y"
by (metis domT_less_eq_def)

lemma Abs_domT_D2:
  "[| Abs_domT r <= a; r : domT |] ==> r <= Rep_domT a"
by (metis Abs_domT_inverse domT_less_eq_def)


lemma lm2_prefix_choice:
  "(ALL x. ALL u' P u P' cs.
                (Pf x, u', P) : ptrans (G D) -->
                Pf x = ptel n (rmtel (Pf x)) -->
                (P, u, P') # cs : comps (G D) -->
                (P = ptel n (rmtel P) -->
                 comp_to_trace ((P, u, P') # cs)
                 : traces_r (rmtel P)
                    (%p. Abs_domT (otraces_r (G D) ($(p, n))))) -->
                comp_to_trace ((Pf x, u', P) # (P, u, P') # cs)
                : traces_r (rmtel (Pf x))
                   (%p. Abs_domT (otraces_r (G D) ($(p, n)))))
       ==> ALL u' P u P' cs.
              (? :X -> Pf, u', P) : ptrans (G D) -->
              ? :X -> Pf = ptel n (rmtel (? :X -> Pf)) -->
              (P, u, P') # cs : comps (G D) -->
              (P = ptel n (rmtel P) -->
               comp_to_trace ((P, u, P') # cs)
               : traces_r (rmtel P)
                  (%p. Abs_domT (otraces_r (G D) ($(p, n))))) -->
              comp_to_trace
               ((? :X -> Pf, u', P) # (P, u, P') # cs)
              : traces_r (rmtel (? :X -> Pf))
                 (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(clarsimp)
apply(erule ptrans_cases_prefix_choice)
apply(clarsimp)
apply(drule_tac x="a" in spec)
apply(drule_tac x="u" in spec)
apply(drule_tac x="P'" in spec)
apply(clarsimp)
by metis

lemma lm2_pn:
  "ALL u' P u P' cs.
            ($p, u', P) : ptrans (G D) -->
            $p = ptel n (rmtel ($p)) -->
            (P, u, P') # cs : comps (G D) -->
            (P = ptel n (rmtel P) -->
             comp_to_trace ((P, u, P') # cs)
             : traces_r (rmtel P)
                (%p. Abs_domT (otraces_r (G D) ($(p, n))))) -->
            comp_to_trace (($p, u', P) # (P, u, P') # cs)
            : traces_r (rmtel ($p))
               (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(clarsimp)
apply(erule ptrans_cases_pn)
apply(clarsimp)
apply(case_tac p)
apply(clarsimp)
apply(rename_tac q)
apply(subst Abs_domT_inverse)
apply(rule otraces_domT)
apply(subst otraces_r_def)
apply(clarsimp)
apply(rotate_tac -1)
apply(erule contrapos_pp)
apply(simp)
apply(subst G_def)
apply(clarsimp)
apply(case_tac n)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="ptel nat (D q)" in exI)
apply(rule_tac x="Tau" in exI)
apply(rule_tac x="(ptel nat (D q), u, P') # cs" in exI)
apply(clarsimp)
apply(rule comps_step2)
apply(clarsimp)
apply(subgoal_tac "ptel nat (D q) = (G D) (q, Suc nat)")
apply(rotate_tac -1)
apply(erule ssubst)
apply(rule ptrans_pn)
apply(subst G_def)
apply(clarsimp)
apply(assumption)
apply(clarsimp)
done

lemma lm2_rep_int_choice:
  "(ALL x. ALL u' P u P' cs.
                (Pf x, u', P) : ptrans (G D) -->
                Pf x = ptel n (rmtel (Pf x)) -->
                (P, u, P') # cs : comps (G D) -->
                (P = ptel n (rmtel P) -->
                 comp_to_trace ((P, u, P') # cs)
                 : traces_r (rmtel P)
                    (%p. Abs_domT (otraces_r (G D) ($(p, n))))) -->
                comp_to_trace ((Pf x, u', P) # (P, u, P') # cs)
                : traces_r (rmtel (Pf x))
                   (%p. Abs_domT (otraces_r (G D) ($(p, n)))))
       ==> ALL u' P u P' cs.
              (!! :X .. Pf, u', P) : ptrans (G D) -->
              !! :X .. Pf = ptel n (rmtel (!! :X .. Pf)) -->
              (P, u, P') # cs : comps (G D) -->
              (P = ptel n (rmtel P) -->
               comp_to_trace ((P, u, P') # cs)
               : traces_r (rmtel P)
                  (%p. Abs_domT (otraces_r (G D) ($(p, n))))) -->
              comp_to_trace
               ((!! :X .. Pf, u', P) # (P, u, P') # cs)
              : traces_r (rmtel (!! :X .. Pf))
                 (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(clarsimp)
apply(erule ptrans_cases_rep_int_choice)
apply(clarsimp)
apply(drule_tac x="x" in spec)
apply(drule_tac x="u" in spec)
apply(drule_tac x="P'" in spec)
apply(frule comps_car)
apply(clarsimp)
by metis

lemma lm1_prefix_choice:
  "(ALL x. ALL u P' cs.
                (Pf x, u, P') # cs : comps (G D) -->
                Pf x = ptel n (rmtel (Pf x)) -->
                comp_to_trace ((Pf x, u, P') # cs)
                : traces_r (rmtel (Pf x))
                   (%p. Abs_domT (otraces_r (G D) ($(p, n)))))
       ==> ALL u P' cs.
              (? :X -> Pf, u, P') # cs : comps (G D) -->
              ? :X -> Pf = ptel n (rmtel (? :X -> Pf)) -->
              comp_to_trace ((? :X -> Pf, u, P') # cs)
              : traces_r (rmtel (? :X -> Pf))
                 (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_prefix_choice)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(drule_tac x="a" in spec)
apply(drule_tac x="ab" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list" in spec)
apply(clarsimp)
by (metis comps_cdr)

lemma lm1_rep_int_choice:
  "(ALL x. ALL u P' cs.
                (Pf x, u, P') # cs : comps (G D) -->
                Pf x = ptel n (rmtel (Pf x)) -->
                comp_to_trace ((Pf x, u, P') # cs)
                : traces_r (rmtel (Pf x))
                   (%p. Abs_domT (otraces_r (G D) ($(p, n)))))
       ==> ALL u P' cs.
              (!! :X .. Pf, u, P') # cs : comps (G D) -->
              !! :X .. Pf =
              ptel n (rmtel (!! :X .. Pf)) -->
              comp_to_trace ((!! :X .. Pf, u, P') # cs)
              : traces_r (rmtel (!! :X .. Pf))
                 (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_rep_int_choice)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(drule_tac x="x" in spec)
apply(drule_tac x="aa" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list" in spec)
apply(drule mp)
apply(erule comps_cdr)
apply(rotate_tac 2)
apply(erule contrapos_pp)
apply(simp)
apply(rule_tac x="traces_r (rmtel (Pf x))
             (%p. Abs_domT (otraces_r (G D) ($(p, n))))" in exI)
apply(rule conjI)
apply(rule_tac x="x" in exI)
apply(clarsimp)
apply(clarsimp)
by metis

lemma lm1_if:
  "[| ALL u P' cs.
             (proc1, u, P') # cs : comps (G D) -->
             proc1 = ptel n (rmtel proc1) -->
             comp_to_trace ((proc1, u, P') # cs)
             : traces_r (rmtel proc1)
                (%p. Abs_domT (otraces_r (G D) ($(p, n))));
          ALL u P' cs.
             (proc2, u, P') # cs : comps (G D) -->
             proc2 = ptel n (rmtel proc2) -->
             comp_to_trace ((proc2, u, P') # cs)
             : traces_r (rmtel proc2)
                (%p. Abs_domT (otraces_r (G D) ($(p, n)))) |]
       ==> ALL u P' cs.
              (IF bool THEN proc1 ELSE proc2, u, P') # cs
              : comps (G D) -->
              IF bool THEN proc1 ELSE proc2 =
              ptel n (rmtel (IF bool THEN proc1 ELSE proc2)) -->
              comp_to_trace
               ((IF bool THEN proc1 ELSE proc2, u, P') # cs)
              : traces_r (rmtel (IF bool THEN proc1 ELSE proc2))
                 (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(clarsimp)
apply(case_tac bool)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_if)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_cdr)
apply metis
apply(clarsimp)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_if)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_cdr)
apply metis
done

lemma lm1_hide:
  "ALL u P' cs.
          (proc, u, P') # cs : comps (G D) -->
          proc = ptel n (rmtel proc) -->
          comp_to_trace ((proc, u, P') # cs)
          : traces_r (rmtel proc)
             (%p. Abs_domT (otraces_r (G D) ($(p, n))))
       ==> ALL u P' cs.
              (proc -- X, u, P') # cs : comps (G D) -->
              proc -- X = ptel n (rmtel (proc -- X)) -->
              comp_to_trace ((proc -- X, u, P') # cs)
              : traces_r (rmtel (proc -- X))
                 (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(clarsimp)
apply(insert comps_hide)
apply(rotate_tac -1)
apply(drule_tac x="G D" in spec)
apply(rotate_tac -1)
apply(drule_tac x="(proc -- X, u, P') # cs" in spec)
apply(rotate_tac -1)
apply(drule_tac x="X" in spec)
apply(rotate_tac -1)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="aa" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list" in spec)
apply(clarsimp)
apply(rule_tac x="comp_to_trace ((proc, aa, b) # list)" in exI)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(insert hide_seq)
apply(rotate_tac -1)
apply(drule_tac x="cs" in spec)
apply(drule_tac x="X" in spec)
apply(drule_tac x="list" in spec)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="cs" in spec)
apply(drule_tac x="X" in spec)
apply(drule_tac x="list" in spec)
apply(clarsimp)
done

lemma sync_sym_0:
  "sync X [] t = sync X t []"
apply(induct_tac  t)
apply(auto)
done

lemma sync_sym_1:
  "ALL a list.
  (ALL t. sync X list t = sync X t list)
    --> sync X (a # list) t = sync X t (a # list)"
apply(induct_tac t)
apply(auto)
done

lemma lm1_par:
  "[| ALL u P' cs.
             (proc1, u, P') # cs : comps (G D) -->
             proc1 = ptel n (rmtel proc1) -->
             comp_to_trace ((proc1, u, P') # cs)
             : traces_r (rmtel proc1)
                (%p. Abs_domT (otraces_r (G D) ($(p, n))));
          ALL u P' cs.
             (proc2, u, P') # cs : comps (G D) -->
             proc2 = ptel n (rmtel proc2) -->
             comp_to_trace ((proc2, u, P') # cs)
             : traces_r (rmtel proc2)
                (%p. Abs_domT (otraces_r (G D) ($(p, n)))) |]
       ==> ALL u P' cs.
              (proc1 |[X]| proc2, u, P') # cs : comps (G D) -->
              proc1 |[X]| proc2 =
              ptel n (rmtel (proc1 |[X]| proc2)) -->
              comp_to_trace ((proc1 |[X]| proc2, u, P') # cs)
              : traces_r (rmtel (proc1 |[X]| proc2))
                 (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(clarsimp)
apply(frule comps_par_sub2)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="P'a" in spec)
apply(drule_tac x="csp'" in spec)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="Q'" in spec)
apply(drule_tac x="csq'" in spec)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace csp'" in exI)
apply(rule_tac x="a # comp_to_trace csq'" in exI)
apply(clarsimp)
apply (metis comps_par_traces_sync)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="P'a" in spec)
apply(drule_tac x="csp'" in spec)
apply(clarsimp)
(* ! *)
apply(frule comps_par_traces_sync)
apply(case_tac cs)
(* if cs=[] then csq is [] *)
apply(clarsimp)
apply(rule_tac x="[a]" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
(* cs ~=[] *)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev ac" in spec)
apply(drule_tac x="Q'" in spec)
apply(drule_tac x="csq'a" in spec)
apply(clarsimp)
apply(rule_tac x="a # ac # comp_to_trace csp'a" in exI)
apply(rule_tac x="ac # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(case_tac "comp_to_trace csq'a")   (* POINT *)
apply(clarsimp)
apply(rule_tac x="a # ac # comp_to_trace csp'a" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
(* if comp_to_trace csq'a ~= [] then some ... *)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac -2)
apply(drule sym)
apply(clarsimp)
(* next case dist is cs0=[] or not, if [], Pa=proc2 *)
apply(case_tac cs0)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Ev a, P |[X]| proc2)#(P |[X]| proc2, Ev ac, P' |[X]| proc2)#list" and csp="(proc1, Ev a, P) # (P, Ev ac, P')#csp'a" and csq="((Pa, Ev aa, Q) # cs1)" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(case_tac "aa:X")
apply(clarsimp)
apply metis
apply(clarsimp)
apply metis
apply(clarsimp)
apply(drule_tac x="Ev aa" in spec)
apply(drule_tac x="Q" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(rule_tac x="a # ac # comp_to_trace csp'a" in exI)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(clarsimp)
apply(case_tac "aa:X")
apply(clarsimp)
apply(clarsimp)
(* cs0 ~= [] *)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Ev a, P |[X]| proc2)#(P |[X]| proc2, Ev ac, P' |[X]| proc2)#list" and csp="(proc1, Ev a, P) # (P, Ev ac, P')#csp'a" and csq="((ab, Tau, b) # lista @ (Pa, Ev aa, Q) # cs1)" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="lista @ (Pa, Ev aa, Q) # cs1" in spec)
apply(clarsimp)
apply(rule_tac x="a # ac # comp_to_trace csp'a" in exI)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(clarsimp)
apply(case_tac "aa:X")
apply(clarsimp)
apply(clarsimp)
(**)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev ac" in spec)
apply(drule_tac x="Q'" in spec)
apply(drule_tac x="csq'a" in spec)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace csp'a" in exI)
apply(rule_tac x="ac # comp_to_trace csq'a" in exI)
apply(clarsimp)
(**)
apply(erule disjE)
apply(clarsimp)
(* csq again! *)
apply(case_tac "comp_to_trace csq'a")   (* POINT *)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace csp'a" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule conjI)
apply(subst sync_sym)
apply(clarsimp)
apply(clarsimp)
(* if comp_to_trace csq'a ~= [] then some ... *)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac -2)
apply(drule sym)
apply(clarsimp)
(* next case dist is cs0=[] or not, if [], Pa=proc2 *)
apply(case_tac cs0)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Ev a, P |[X]| proc2) # (P |[X]| proc2, Tau, P' |[X]| proc2) # list" and csp="(proc1, Ev a, P) # (P, Tau, P') # csp'a" and csq="((Pa, Ev aa, Q) # cs1)" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(drule_tac x="Ev aa" in spec)
apply(drule_tac x="Q" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace csp'a" in exI)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(clarsimp)
(* cs0 ~= [] *)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Ev a, P |[X]| proc2) # (P |[X]| proc2, Tau, P' |[X]| proc2) # list" and csp="(proc1, Ev a, P) # (P, Tau, P') # csp'a" and csq="(ab, Tau, b) # lista @ (Pa, Ev aa, Q) # cs1" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(metis)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="lista @ (Pa, Ev aa, Q) # cs1" in spec)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace csp'a" in exI)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(clarsimp)
(**)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="Q'" in spec)
apply(drule_tac x="csq'a" in spec)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace csp'a" in exI)
apply(rule_tac x="comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(rule sync_no_sync_1)
apply(clarsimp)
apply(clarsimp)
(* proc2 *)
apply(erule disjE)
apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="Q'" in spec)
apply(drule_tac x="csq'" in spec)
apply(clarsimp)
(* ! *)
apply(frule comps_par_traces_sync)
apply(case_tac cs)
(* if cs=[] then csq is [] *)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="[a]" in exI)
apply(clarsimp)
(* cs ~=[] *)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev ac" in spec)
apply(drule_tac x="P'" in spec)
apply(drule_tac x="csp'a" in spec)
apply(clarsimp)
apply(rule_tac x="ac # comp_to_trace csp'a" in exI)
apply(rule_tac x="a#ac # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev ac" in spec)
apply(drule_tac x="P'" in spec)
apply(drule_tac x="csp'a" in spec)
apply(clarsimp)
apply(rule_tac x="ac # comp_to_trace csp'a" in exI)
apply(rule_tac x="a # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(case_tac "comp_to_trace csp'a")   (* POINT *)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="a # ac # comp_to_trace csq'a" in exI)
apply(clarsimp)
(* if comp_to_trace csq'a ~= [] then some ... *)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac -2)
apply(drule sym)
apply(clarsimp)
(* next case dist is cs0=[] or not, if [], Pa=proc2 *)
apply(case_tac cs0)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Ev a, proc1 |[X]| Q) # (proc1 |[X]| Q, Ev ac, proc1 |[X]| Q'a) # list" and csp="(P, Ev aa, Qa) # cs1" and csq="(proc2, Ev a, Q) # (Q, Ev ac, Q'a) # csq'a" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(case_tac "aa:X")
apply(clarsimp)
apply metis
apply(clarsimp)
apply metis
apply(case_tac "aa:X")
apply(clarsimp)
apply(drule_tac x="Ev aa" in spec)
apply(drule_tac x="Qa" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(rule_tac x="a#ac # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="Ev aa" in spec)
apply(drule_tac x="Qa" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(rule_tac x="a#ac # comp_to_trace csq'a" in exI)
apply(clarsimp)
(* cs0 ~= [] *)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Ev a, proc1 |[X]| Q) # (proc1 |[X]| Q, Ev ac, proc1 |[X]| Q'a) # list" and csp="(ab, Tau, b) # lista @ (P, Ev aa, Qa) # cs1" and csq="(proc2, Ev a, Q) # (Q, Ev ac, Q'a) # csq'a" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="lista @ (P, Ev aa, Qa) # cs1" in spec)
apply(clarsimp)
apply(case_tac "aa:X")
apply(clarsimp)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(rule_tac x="a # ac # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(rule_tac x="a # ac # comp_to_trace csq'a" in exI)
apply(clarsimp)
(**)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="P'" in spec)
apply(drule_tac x="csp'a" in spec)
apply(clarsimp)
apply(rule_tac x="comp_to_trace csp'a" in exI)
apply(rule_tac x="a # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(rule sync_no_sync_2)
apply(clarsimp)
apply(clarsimp)
(**)
apply(clarsimp)
(* csp again! *)
apply(case_tac "comp_to_trace csp'a")   (* POINT *)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="a # comp_to_trace csq'a" in exI)
apply(clarsimp)
(* if comp_to_trace csq'a ~= [] then some ... *)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac -2)
apply(drule sym)
apply(clarsimp)
(* next case dist is cs0=[] or not, if [], Pa=proc2 *)
apply(case_tac cs0)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Ev a, proc1 |[X]| Q) # (proc1 |[X]| Q, Tau, proc1 |[X]| Q'a) # list" and csp="(P, Ev aa, Qa) # cs1" and csq="(proc2, Ev a, Q) # (Q, Tau, Q'a) # csq'a" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(drule_tac x="Ev aa" in spec)
apply(drule_tac x="Qa" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(rule_tac x="a # comp_to_trace csq'a" in exI)
apply(clarsimp)
(* cs0 ~= [] *)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Ev a, proc1 |[X]| Q) # (proc1 |[X]| Q, Tau, proc1 |[X]| Q'a) # list" and csp="(ab, Tau, b) # lista @ (P, Ev aa, Qa) # cs1" and csq="(proc2, Ev a, Q) # (Q, Tau, Q'a) # csq'a" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(metis)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="lista @ (P, Ev aa, Qa) # cs1" in spec)
apply(clarsimp)
apply(rule_tac x="aa # comp_to_trace cs1" in exI)
apply(rule_tac x="a # comp_to_trace csq'a" in exI)
apply(clarsimp)
(**)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="P'a" in spec)
apply(drule_tac x="csp'" in spec)
apply(clarsimp)
apply(case_tac cs)
(* if cs=[] then csq is [] *)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
(* cs ~=[] *)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev ab" in spec)
apply(drule_tac x="Q'" in spec)
apply(drule_tac x="csq'a" in spec)
apply(clarsimp)
apply(rule_tac x="ab # comp_to_trace csp'a" in exI)
apply(rule_tac x="ab # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(erule comps_par_traces_sync)
apply(erule disjE)
apply(clarsimp)
apply(case_tac "comp_to_trace csq'a")   (* POINT *)
apply(rule_tac x="ab # comp_to_trace csp'a" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule conjI)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(subst sync_sym)
apply(clarsimp)
apply(clarsimp)
(* if comp_to_trace csq'a ~= [] then some ... *)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac -2)
apply(drule sym)
apply(clarsimp)
(* next case dist is cs0=[] or not, if [], Pa=proc2 *)
apply(case_tac cs0)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Tau, P |[X]| proc2) # (P |[X]| proc2, Ev ab, P' |[X]| proc2) # list" and csp="(proc1, Tau, P) # (P, Ev ab, P') # csp'a" and csq="(Pa, Ev a, Q) # cs1" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="Q" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(rule_tac x="ab # comp_to_trace csp'a" in exI)
apply(rule_tac x="a # comp_to_trace cs1" in exI)
apply(clarsimp)
apply(case_tac "a:X")
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
(* cs0 ~= [] *)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Tau, P |[X]| proc2) # (P |[X]| proc2, Ev ab, P' |[X]| proc2) # list" and csp="(proc1, Tau, P) # (P, Ev ab, P') # csp'a" and csq="(aa, Tau, b) # lista @ (Pa, Ev a, Q) # cs1" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="lista @ (Pa, Ev a, Q) # cs1" in spec)
apply(clarsimp)
apply(rule_tac x="ab # comp_to_trace csp'a" in exI)
apply(rule_tac x="a # comp_to_trace cs1" in exI)
apply(clarsimp)
apply(case_tac "a:X")
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
(**)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev ab" in spec)
apply(drule_tac x="Q'" in spec)
apply(drule_tac x="csq'a" in spec)
apply(clarsimp)
apply(rule_tac x="comp_to_trace csp'a" in exI)
apply(rule_tac x="ab # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(rule sync_no_sync_2)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(clarsimp)
(**)
apply(erule disjE)
apply(clarsimp)
(* csq again! *)
apply(case_tac "comp_to_trace csq'a")   (* POINT *)
apply(rule_tac x="comp_to_trace csp'a" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
apply(rule conjI)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(clarsimp)
(* if comp_to_trace csq'a ~= [] then some ... *)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac -2)
apply(drule sym)
apply(clarsimp)
(* next case dist is cs0=[] or not, if [], Pa=proc2 *)
apply(case_tac cs0)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Tau, P |[X]| proc2) # (P |[X]| proc2, Tau, P' |[X]| proc2) # list" and csp="(proc1, Tau, P) # (P, Tau, P') # csp'a" and csq="(Pa, Ev a, Q) # cs1" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="Q" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(rule_tac x="comp_to_trace csp'a" in exI)
apply(rule_tac x="a # comp_to_trace cs1" in exI)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
(* cs0 ~= [] *)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Tau, P |[X]| proc2) # (P |[X]| proc2, Tau, P' |[X]| proc2) # list" and csp="(proc1, Tau, P) # (P, Tau, P') # csp'a" and csq="(aa, Tau, b) # lista @ (Pa, Ev a, Q) # cs1" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(metis)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="lista @ (Pa, Ev a, Q) # cs1" in spec)
apply(clarsimp)
apply(rule_tac x="comp_to_trace csp'a" in exI)
apply(rule_tac x="a # comp_to_trace cs1" in exI)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
(**)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="Q'" in spec)
apply(drule_tac x="csq'a" in spec)
apply(clarsimp)
apply(rule_tac x="comp_to_trace csp'a" in exI)
apply(rule_tac x="comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
(***********************)

(* csp <-> csq *)

apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="Q'" in spec)
apply(drule_tac x="csq'" in spec)
apply(clarsimp)
apply(case_tac cs)
(* if cs=[] then csq is [] *)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="[]" in exI)
apply(clarsimp)
(* cs ~=[] *)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev ab" in spec)
apply(drule_tac x="P'" in spec)
apply(drule_tac x="csp'a" in spec)
apply(clarsimp)
apply(rule_tac x="ab # comp_to_trace csp'a" in exI)
apply(rule_tac x="ab # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(erule comps_par_traces_sync)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Ev ab" in spec)
apply(drule_tac x="P'" in spec)
apply(drule_tac x="csp'a" in spec)
apply(clarsimp)
apply(rule_tac x="ab # comp_to_trace csp'a" in exI)
apply(rule_tac x="comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(rule sync_no_sync_1)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(case_tac "comp_to_trace csp'a")   (* POINT *)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="ab # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(rule conjI)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(clarsimp)
(* if comp_to_trace csq'a ~= [] then some ... *)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac -2)
apply(drule sym)
apply(clarsimp)
(* next case dist is cs0=[] or not, if [], Pa=proc2 *)
apply(case_tac cs0)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Tau, proc1 |[X]| Q) # (proc1 |[X]| Q, Ev ab, proc1 |[X]| Q'a) # list" and csp="(P, Ev a, Qa) # cs1" and csq="(proc2, Tau, Q) # (Q, Ev ab, Q'a) # csq'a" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="Qa" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace cs1" in exI)
apply(rule_tac x="ab # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(case_tac "a:X")
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
(* cs0 ~= [] *)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Tau, proc1 |[X]| Q) # (proc1 |[X]| Q, Ev ab, proc1 |[X]| Q'a) # list" and csp="(aa, Tau, b) # lista @ (P, Ev a, Qa) # cs1" and csq="(proc2, Tau, Q) # (Q, Ev ab, Q'a) # csq'a" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="lista @ (P, Ev a, Qa) # cs1" in spec)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace cs1" in exI)
apply(rule_tac x="ab # comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(case_tac "a:X")
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
(**)
apply(erule disjE)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="P'" in spec)
apply(drule_tac x="csp'a" in spec)
apply(clarsimp)
apply(rule_tac x="comp_to_trace csp'a" in exI)
apply(rule_tac x="comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
(* csq again! *)
apply(case_tac "comp_to_trace csp'a")   (* POINT *)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(rule conjI)
apply(drule comps_par_traces_sync)
apply(clarsimp)
apply(clarsimp)
(* if comp_to_trace csq'a ~= [] then some ... *)
apply(rotate_tac -1)
apply(drule sym)
apply(frule non_nil_comp_to_trace_forall)
apply(rotate_tac -2)
apply(drule sym)
apply(clarsimp)
(* next case dist is cs0=[] or not, if [], Pa=proc2 *)
apply(case_tac cs0)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Tau, proc1 |[X]| Q) #
          (proc1 |[X]| Q, Tau, proc1 |[X]| Q'a) # list" and csp="(P, Ev a, Qa) # cs1" and csq="(proc2, Tau, Q) # (Q, Tau, Q'a) # csq'a" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="Qa" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace cs1" in exI)
apply(rule_tac x="comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
(* cs0 ~= [] *)
apply(clarsimp)
apply(frule_tac X="X" and cs="(proc1 |[X]| proc2, Tau, proc1 |[X]| Q) #
          (proc1 |[X]| Q, Tau, proc1 |[X]| Q'a) # list" and csp="(aa, Tau, b) # lista @ (P, Ev a, Qa) # cs1" and csq="(proc2, Tau, Q) # (Q, Tau, Q'a) # csq'a" in par_csp_csq_hd)
apply(clarsimp)
apply(clarsimp)
apply(metis)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="lista @ (P, Ev a, Qa) # cs1" in spec)
apply(clarsimp)
apply(rule_tac x="a # comp_to_trace cs1" in exI)
apply(rule_tac x="comp_to_trace csq'a" in exI)
apply(clarsimp)
apply(drule comps_par_traces_sync)
apply(clarsimp)
done

fun comps_interleave :: "((('p, 'a)proc * 'a event * ('p, 'a)proc) list) =>
                         ((('p, 'a)proc * 'a event * ('p, 'a)proc) list) =>
                         ((('p, 'a)proc * 'a event * ('p, 'a)proc) list) => bool" where
  "comps_interleave [] csp csq = (csp = [] & csq = [])"
| "comps_interleave ((R, u, R')#cs) csp csq =
    (EX P Q P' Q'. u=Tau & R = P [+] Q & R' = P' [+] Q' &
        ((csp ~= [] & (P,Tau,P') = hd csp & Q=Q' & comps_interleave cs (tl csp) csq) |
         (csq ~= [] & (Q,Tau,Q') = hd csq & P=P' & comps_interleave cs csp (tl csq))))"

lemma comps_interleave_tau [rule_format]:
  "ALL csp csq. comps_interleave cs csp csq -->
  forall (%(p,u,q). u=Tau) cs &
  forall (%(p,u,q). u=Tau) csp &
  forall (%(p,u,q). u=Tau) csq"
apply(induct_tac cs)
apply(auto)
apply (metis comp_to_trace.simps(2) comp_to_trace_nil2 comp_to_trace_tau_forall list.collapse)
by (metis comp_to_trace.simps(2) comp_to_trace_nil2 comp_to_trace_tau_forall hd_Cons_tl)

lemma csp_csq_hd [rule_format]:
  "ALL P Q P' Q' u csp csq.
   (P [+] Q, u, P' [+] Q')#cs : comps PNfun -->
     comps_interleave cs csp csq -->
       (csp ~= [] --> fst (hd csp) = P') &
       (csq ~= [] --> fst (hd csq) = Q')"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="a" in spec)
apply(drule_tac x="Q'a" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="Q'a" in spec)
apply(drule mp)
apply(drule comps_cdr)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(drule_tac x="csq" in spec)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
(**)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="P'a" in spec)
apply(drule_tac x="a" in spec)
apply(drule_tac x="P'a" in spec)
apply(drule_tac x="b" in spec)
apply(drule mp)
apply(drule comps_cdr)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(drule_tac x="csp" in spec)
apply(drule_tac x="lista" in spec)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
done

lemma comps_ext_choice_tau [rule_format]:
  "cs : comps PNfun -->
  cs ~= [] -->
  (EX P Q. fst (hd cs) = P [+] Q) -->
    forall (%(p,u,q). u=Tau) cs -->
      (EX csp csq.
          comps_interleave cs csp csq &
          csp : comps PNfun & csq : comps PNfun)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(drule comps_car)
apply(erule ptrans_cases_ext_choice)
apply(clarsimp)+
apply(rule_tac x="[(P,Tau,P')]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="[(Q,Tau,Q')]" in exI)
apply(clarsimp)
(**)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_ext_choice)
apply(clarsimp)+
apply(erule disjE)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)+
apply(rule_tac x="(P,Tau,a)#(a,Tau,b)#list" in exI)
apply(rule_tac x="csq" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
(**)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(rule_tac x="[(P,Tau,P'a)]" in exI)
apply(clarsimp)
apply(rule_tac x="(a,Tau,b)#list" in exI)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(drule_tac csp="csp" and csq="list" in csp_csq_hd)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="(P,Tau,aa)#(aa,ab,ba)#listb" in exI)
apply(rule_tac x="(a,Tau,b)#list" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
(**)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(drule_tac csp="list" and csq="csq" in csp_csq_hd)
apply(assumption)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(rule_tac x="(a,Tau,b)#list" in exI)
apply(rule_tac x="[(Q,Tau,Q'a)]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="(a,Tau,b)#list" in exI)
apply(rule_tac x="(Q,Tau,aa)#(aa,ab,ba)#listb" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
(**)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(drule_tac csp="csp" and csq="list" in csp_csq_hd)
apply(assumption)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="(Q,Tau,a)#(a,Tau,b)#list" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
(**)
apply(clarsimp)
apply(rule_tac x="(aa,ab,ba)#listb" in exI)
apply(rule_tac x="(Q,Tau,a)#(a,Tau,b)#list" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
done

lemma csp_csq_hd2 [rule_format]:
  "ALL P Q P' Q' u csp csq.
   cs : comps PNfun -->
     cs ~= [] -->
     comps_interleave cs csp csq -->
       (csp ~= [] --> (EX Q. fst (hd csp) [+] Q = fst (hd cs))) &
       (csq ~= [] --> (EX P. P [+] fst (hd csq) = fst (hd cs)))"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(case_tac list)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(clarsimp)
(**)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(case_tac list)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(clarsimp)
done

lemma comps_ev [rule_format]:
  "cs : comps PNfun -->
    ~forall (%(p,u,q). u=Tau) cs -->
     (EX cs0 cs1 P Q R a.
         cs0 @ (P, Ev a, Q) # cs1 = cs &
         forall (%(p,u,q). u=Tau) cs0)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(clarsimp)
apply (metis append_Cons comp_to_trace.simps(2) comp_to_trace_nil2 comp_to_trace_tau_forall)
apply(clarsimp)
by (metis forall.elims(3) list.distinct(2) self_append_conv2)

lemma comps_interleave_hd:
  "ALL csp csq.
    comps_interleave cs csp csq -->
     cs ~= [] --> (EX P Q. fst (hd cs) = P [+] Q)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
done

lemma comps_interleave_all:
  "ALL csp csq.
    comps_interleave cs csp csq -->
     forall (%(p,u,q). u=Tau & (EX P Q P' Q'. p = P [+] Q & q = P' [+] Q')) cs"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
done

lemma comps_ext_choice_next [rule_format]:
  "ALL R u R'.
   cs @ [(R, u, R')] : comps PNfun -->
    cs ~= [] -->
    (EX P Q. fst(hd cs) = P [+] Q) -->
    forall (%(p,u,q). u=Tau) cs -->
    (EX P Q. R = P [+] Q)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_ext_choice)
apply(clarsimp)+
apply(drule comps_connect)
apply(clarsimp)
apply(drule comps_connect)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_ext_choice)
apply(clarsimp)+
apply(drule_tac x="R" in spec)
apply(clarsimp)
apply(drule_tac x="u" in spec)
apply(drule_tac x="R'" in spec)
apply(clarsimp)
apply(drule comps_cdr)
apply(assumption)
apply(clarsimp)
apply(drule_tac x="R" in spec)
apply(clarsimp)
apply(drule_tac x="u" in spec)
apply(drule_tac x="R'" in spec)
apply(clarsimp)
apply(drule comps_cdr)
apply(assumption)
done

lemma ext_choice_comps_2_1 [rule_format]:
  "ALL cs PNfun.
  cs : comps PNfun -->
  cs ~= [] -->
  (EX P0 Q0. fst (hd cs) = P0 [+] Q0) -->
     ~forall (%(p,u,q). u=Tau) cs -->
       (EX cs0 cs1 P Q R a csp csq.
          cs = cs0 @ (P [+] Q, Ev a, R) # cs1 &
          comps_interleave cs0 csp csq &
          (csp @ (P, Ev a, R) # cs1: comps PNfun | csq @ (Q, Ev a, R) # cs1: comps PNfun) &
          (csp @ (P, Ev a, R) # cs1: comps PNfun -->
              (csp ~= [] --> (EX Q. fst(hd csp) [+] Q = fst (hd cs))) &
              (csp = [] --> (EX Q. P [+] Q = fst (hd cs)))) &
          (csq @ (Q, Ev a, R) # cs1: comps PNfun -->
              (csq ~= [] --> (EX P. P [+] fst(hd csq) = fst (hd cs))) &
              (csq = [] --> (EX P. P [+] Q = fst (hd cs)))))" 
apply(rule allI)+
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(drule mp)
apply(erule comps_cdr)
apply(case_tac list)
apply(clarsimp)
apply(drule comps_car)
apply(erule ptrans_cases_ext_choice)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="P0" in exI)
apply(rule_tac x="Q0" in exI)
apply(rule_tac x="b" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="P0" in exI)
apply(rule_tac x="Q0" in exI)
apply(rule_tac x="b" in exI)
apply(rule_tac x="e" in exI)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_ext_choice)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="(P0 [+] Q0, Tau, P' [+] Q0) # cs0" in exI)
apply(rule_tac x="cs1" in exI)
apply(rule_tac x="P" in exI)
apply(rule_tac x="Q" in exI)
apply(rule_tac x="R" in exI)
apply(rule_tac x="aa" in exI)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="(P0,Tau,P')#csp" in exI)
apply(rule_tac x="csq" in exI)
apply(clarsimp)
apply(rule conjI)
prefer 2
apply(clarsimp)
apply(rule disjI1)
apply(case_tac cs0)
apply(subgoal_tac "csp=[]")
apply(subgoal_tac "P'=P")
apply(clarify)
apply(simp)
apply(erule comps_step2)
apply(assumption)
apply(clarsimp)
apply(clarify)
apply(unfold comps_interleave.simps(1))
apply(simp)
apply(drule comps_cdr)
apply(rotate_tac -1)
apply(drule comps_app_D1)
apply(rotate_tac -1)
apply(drule_tac csp="csp" and csq="csq" in csp_csq_hd2)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
apply(clarsimp)
(**)
apply(rule_tac x="(P0,Tau,P')#csp" in exI)
apply(rule_tac x="csq" in exI)
apply(clarsimp)
(**)
apply(clarsimp)
apply(rule_tac x="(P0 [+] Q0, Tau, P0 [+] Q') # cs0" in exI)
apply(rule_tac x="cs1" in exI)
apply(rule_tac x="P" in exI)
apply(rule_tac x="Q" in exI)
apply(rule_tac x="R" in exI)
apply(rule_tac x="aa" in exI)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(rule_tac x="csp" in exI)
apply(rule_tac x="(Q0,Tau,Q')#csq" in exI)
apply(clarsimp)
(**)
apply(clarsimp)
apply(rule_tac x="csp" in exI)
apply(rule_tac x="(Q0,Tau,Q')#csq" in exI)
apply(clarsimp)
apply(rule conjI)
prefer 2
apply(clarsimp)
apply(rule disjI2)
apply(case_tac cs0)
apply(subgoal_tac "csq=[]")
apply(subgoal_tac "Q'=Q")
apply(clarify)
apply(simp)
apply(erule comps_step2)
apply(assumption)
apply(clarsimp)
apply(clarify)
apply(unfold comps_interleave.simps(1))
apply(simp)
apply(drule comps_cdr)
apply(rotate_tac -1)
apply(drule comps_app_D1)
apply(rotate_tac -1)
apply(drule_tac csp="csp" and csq="csq" in csp_csq_hd2)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
apply(clarsimp)
apply(erule comps_step2)
apply(assumption)
(**)
apply(clarsimp)
apply(rule_tac x="[]" in exI)
apply(rule_tac x="(a, ab, ba) # lista" in exI)
apply(rule_tac x="P0" in exI)
apply(rule_tac x="Q0" in exI)
apply(rule_tac x="a" in exI)
apply(rule_tac x="ac" in exI)
apply(clarsimp)
apply(frule comps_car)
apply(drule comps_cdr)
apply(erule ptrans_cases_ext_choice)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(clarsimp)
apply (metis comps.comps_step2)
apply(clarsimp)
apply(clarsimp)
done

lemma ext_choice_comps_2:
  "ALL cs PNfun.
  cs : comps PNfun -->
  cs ~= [] -->
  (EX P0 Q0. fst (hd cs) = P0 [+] Q0) -->
    (forall (%(p,u,q). u=Tau) cs &
      (EX csp csq.
          comps_interleave cs csp csq &
          csp : comps PNfun & csq : comps PNfun &
          (csp ~= [] --> (EX Q. (fst (hd csp)) [+] Q = fst (hd cs))) &
          (csq ~= [] --> (EX P. P [+] (fst (hd csq)) = fst (hd cs))) ))
 |  (~forall (%(p,u,q). u=Tau) cs &
       (EX cs0 cs1 P Q R a csp csq.
          cs = cs0 @ (P [+] Q, Ev a, R) # cs1 &
          comps_interleave cs0 csp csq &
          (csp @ (P, Ev a, R) # cs1: comps PNfun | csq @ (Q, Ev a, R) # cs1: comps PNfun) &
          (csp @ (P, Ev a, R) # cs1: comps PNfun -->
              (csp ~= [] --> (EX Q. fst(hd csp) [+] Q = fst (hd cs))) &
              (csp = [] --> (EX Q. P [+] Q = fst (hd cs)))) &
          (csq @ (Q, Ev a, R) # cs1: comps PNfun -->
              (csq ~= [] --> (EX P. P [+] fst(hd csq) = fst (hd cs))) &
              (csq = [] --> (EX P. P [+] Q = fst (hd cs))))))" 
apply(rule allI)+
apply(rule impI)
apply(rule impI)
apply(case_tac "forall (%(p,u,q). u=Tau) cs")
apply(rule impI)
apply(frule comps_ext_choice_tau)
apply(assumption)
apply(clarsimp)
apply(assumption)
apply(clarsimp)
apply(rule_tac x="csp" in exI)
apply(rule_tac x="csq" in exI)
apply(clarsimp)
apply(drule csp_csq_hd2)
apply(assumption)+
apply(clarsimp)
(**)
apply(rule impI)
apply(rule disjI2)
apply(frule ext_choice_comps_2_1)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
done

lemma lm1_ext_choice:
  "[| ALL u P' cs.
             (proc1, u, P') # cs : comps (G D) -->
             proc1 = ptel n (rmtel proc1) -->
             comp_to_trace ((proc1, u, P') # cs)
             : traces_r (rmtel proc1)
                (%p. Abs_domT (otraces_r (G D) ($(p, n))));
          ALL u P' cs.
             (proc2, u, P') # cs : comps (G D) -->
             proc2 = ptel n (rmtel proc2) -->
             comp_to_trace ((proc2, u, P') # cs)
             : traces_r (rmtel proc2)
                (%p. Abs_domT (otraces_r (G D) ($(p, n)))) |]
       ==> ALL u P' cs.
              (proc1 [+] proc2, u, P') # cs : comps (G D) -->
              proc1 [+] proc2 = ptel n (rmtel (proc1 [+] proc2)) -->
              comp_to_trace ((proc1 [+] proc2, u, P') # cs)
              : traces_r (rmtel (proc1 [+] proc2))
                 (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(clarsimp)
apply(insert ext_choice_comps_2)
apply(rotate_tac -1)
apply(drule_tac x="(proc1 [+] proc2, u, P') # cs" in spec)
apply(rotate_tac -1)
apply(drule_tac x="G D" in spec)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list" in spec)
apply(clarsimp)
apply(drule comps_interleave_tau)
apply(clarsimp)
apply(drule_tac cs="cs" in comp_to_trace_tau_forall)
apply(drule_tac cs="list" in comp_to_trace_tau_forall)
apply(clarsimp)
(**)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="Tau" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list" in spec)
apply(clarsimp)
apply(drule comps_interleave_tau)
apply(clarsimp)
apply(drule_tac cs="cs" in comp_to_trace_tau_forall)
apply(drule_tac cs="list" in comp_to_trace_tau_forall)
apply(clarsimp)
(**)
apply(clarsimp)
apply(erule disjE)
apply(clarsimp)
apply(case_tac csp)
apply(clarsimp)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="R" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(drule comps_interleave_tau)
apply(clarsimp)
apply(drule_tac cs="cs0" in comp_to_trace_tau_forall)
apply(clarsimp)
(**)
apply(clarsimp)
apply(drule_tac x="ab" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list@(P, Ev a, R)#cs1" in spec)
apply(clarsimp)
apply(drule comps_interleave_tau)
apply(clarsimp)
apply(drule_tac cs="cs0" in comp_to_trace_tau_forall)
apply(drule_tac cs="list" in comp_to_trace_tau_forall)
apply(clarsimp)
(**)
apply(clarsimp)
apply(case_tac csq)
apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="Ev a" in spec)
apply(drule_tac x="R" in spec)
apply(drule_tac x="cs1" in spec)
apply(clarsimp)
apply(drule comps_interleave_tau)
apply(clarsimp)
apply(drule_tac cs="cs0" in comp_to_trace_tau_forall)
apply(clarsimp)
(**)
apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="ab" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list@(Q, Ev a, R)#cs1" in spec)
apply(clarsimp)
apply(drule comps_interleave_tau)
apply(clarsimp)
apply(drule_tac cs="cs0" in comp_to_trace_tau_forall)
apply(drule_tac cs="list" in comp_to_trace_tau_forall)
apply(clarsimp)
done

lemma comps_rename2:
  "ALL D R cs.
   cs : comps D -->
   cs ~= [] -->
   (EX P. fst (hd cs) = P[[R]]) -->
   (EX cs'.
       cs' : comps D &
       forall2
        (%(p, u, q) (p2, v, q2).
            p = p2[[R]] &
            q = q2[[R]] &
            (case u of Tau => v=Tau | Ev b => EX a. (a, b) : R & v=Ev a))
        cs cs')"
apply(rule allI)
apply(rule allI)
apply(rule allI)
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac list)
apply(clarsimp)
apply(drule comps_car)
apply(erule ptrans_cases_rename)
apply(clarsimp)
apply(rule_tac x="[(P, Ev a, P')]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="[(P, Tau, P')]" in exI)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_rename)
apply(clarsimp)
apply(drule mp)
apply(rule comps_cdr)
apply(assumption)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="(P, Ev ac, a)#(a, aa, bb) # list" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(clarsimp)
apply(clarsimp)
apply(drule mp)
apply(rule comps_cdr)
apply(assumption)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="(P, Tau, a)#(a, aa, b) # list" in exI)
apply(clarsimp)
apply(erule comps_step2)
apply(clarsimp)
done

lemma rename_tr_comp_to_trace [rule_format]:
  "ALL cs'.
      forall2
           (%(p, u, q) (p2, v, q2).
                (case u of Tau => v = Tau | Ev b => EX a. (a, b) : R & v = Ev a))
           cs cs'
  --> rename_tr R (comp_to_trace cs') (comp_to_trace cs)"
apply(induct_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="lista" in spec)
apply(clarsimp)
apply(case_tac aa)
apply(clarsimp)
apply(clarsimp)
done

lemma lm1_rename:
  "[| ALL u P' cs.
             (proc, u, P') # cs : comps (G D) -->
             comp_to_trace ((proc, u, P') # cs)
             : traces_r (rmtel proc) (%p. Abs_domT (otraces_r (G D) ($(p, n))));
          (proc [[R]], u, P') # cs : comps (G D); proc = ptel n (rmtel proc) |]
       ==> EX s. rename_tr R s (comp_to_trace ((proc [[R]], u, P') # cs)) &
                 s : traces_r (rmtel proc) (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(insert comps_rename2)
apply(drule_tac x="G D" in spec)
apply(rotate_tac -1)
apply(drule_tac x="R" in spec)
apply(rotate_tac -1)
apply(drule_tac x="(proc [[R]], u, P') # cs" in spec)
apply(rotate_tac -1)
apply(drule mp)
apply(clarsimp)
apply(drule mp)
apply(clarsimp)
apply(drule mp)
apply(clarsimp)
apply(clarsimp)
apply(case_tac cs')
apply(clarsimp)
apply(clarsimp)
apply(drule_tac x="aa" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list" in spec)
apply(clarsimp)
apply(rule_tac x="comp_to_trace ((proc, aa, b) # list)" in exI)
apply(clarsimp)
apply(rule rename_tr_comp_to_trace)
apply(rule_tac f="(%(p, u, q) (p2, ab).
               p = p2 [[R]] &
               (case ab of
                (v, q2) =>
                  q = q2 [[R]] &
                  (case u of Tau => v = Tau | Ev b => EX a. (a, b) : R & v = Ev a)))"
  in forall2_mono)
apply(case_tac  u)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
done

lemma lm3_1 [rule_format]:
  "ALL u P' cs.
   (P, u, P')#cs : comps (G D) -->
   P = ptel n (rmtel P) -->
   comp_to_trace ((P, u, P')#cs)
           : traces_r (rmtel P)
              (%p. Abs_domT (otraces_r (G D) ($(p, n))))"
apply(induct_tac P)
apply(clarsimp)
apply (metis comps_car ptrans_cases_STOP)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_prefix)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply (metis comps_cdr)
apply(rule lm1_prefix_choice)
apply(clarsimp)
apply(erule lm1_ext_choice)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_car)
apply(erule ptrans_cases_int_choice)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(drule_tac x="aa" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list" in spec)
apply(drule mp)
apply(erule comps_cdr)
apply(clarsimp)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(rotate_tac 1)
apply(drule_tac x="aa" in spec)
apply(drule_tac x="b" in spec)
apply(drule_tac x="list" in spec)
apply(drule mp)
apply(erule comps_cdr)
apply(clarsimp)
apply(rule lm1_rep_int_choice)
apply(clarsimp)
apply(erule lm1_if)
apply(assumption)
apply(erule lm1_par)
apply(clarsimp)
apply(erule lm1_hide)
apply(clarsimp)
apply(erule lm1_rename)
apply(clarsimp)
apply(clarsimp)
apply(clarsimp)
apply(subst Abs_domT_inverse)
apply(rule otraces_domT)
apply(frule comps_car)
apply(erule ptrans_cases_pn)
apply(clarsimp)
apply(subst otraces_r_def)
apply(clarsimp)
done

lemma lm3_2:
  "s : otraces_r (G D) ($(p, Suc n))
   ==> s : Rep_domT
      (F D (%p. Abs_domT (otraces_r (G D) ($(p, n)))) p)"
apply(erule otraces_r_E)
apply(clarsimp)
apply(clarsimp)
apply(unfold F_def)
apply(unfold traces_def)
apply(subst Abs_domT_inverse)
apply(rule traces_r_domT)
apply(frule comps_car)
apply(erule ptrans_cases_pn)
apply(clarsimp)
apply(case_tac cs)
apply(clarsimp)
apply(clarsimp)
apply(frule comps_connect)
apply(clarsimp)
apply(frule comps_cdr)
apply(rotate_tac -1)
apply(drule_tac n="n" in lm3_1)
apply(clarsimp)
apply(clarsimp)
done

lemma lm3_3:
  "(%p. otraces (G D) ($(p, Suc n)))
     <= F D (%p. otraces (G D) ($(p, n)))"
apply(rule le_funI)
apply(unfold otraces_def)
apply(rule Abs_domT_I2)
apply(rule subsetI)
apply(rename_tac p s)
apply(erule lm3_2)
apply(rule otraces_domT)
done

lemma otraces_r_GD_0 [simp]:
  "otraces_r (G D) ($(p, 0)) = {[]}"
apply(unfold otraces_r_def G_def)
apply(rule subset_antisym)
apply(clarsimp)
apply(drule comps_car)
apply(erule ptrans_cases_pn)
apply(clarsimp)
apply(clarsimp)
done

lemma otraces_GD_0 [simp]:
  "otraces (G D) ($(p, 0)) = Abs_domT {[]}"
apply(simp add: otraces_def)
done

lemma lm3_4:
  "(%p. otraces (G D) ($(p, n)))
      <= (F D ^^ n) (%p. Abs_domT {[]})"
apply(induct_tac n)
apply(clarsimp)
apply(subgoal_tac "(%p. otraces (G D) ($(p, Suc n)))
     <= F D (%p. otraces (G D) ($(p, n)))")
apply(erule order_trans)
apply(clarsimp)
apply(rule_tac f="F D" in monoD)
apply(rule mono_csp)
apply(assumption)
apply(rule lm3_3)
done

definition deno_sem2 :: "('p => ('p, 'a) proc) => 'p => 'a domT" where
  "deno_sem2 D = Sup {((F D)^^n) (%p. (Abs_domT {[]})) | n. True}"

lemma deno_sem2_domT:
  "(Union {X. EX n. X = Rep_domT ((((F D)^^n) (%p. (Abs_domT {[]}))) p)}) : domT"
apply(unfold domT_def)
apply(clarsimp)
apply(unfold HC_T1_def)
apply(rule conjI)
apply(subst ex_in_conv[THEN sym])
apply(rule_tac x="[]" in exI)
apply(subst Union_iff)
apply(clarsimp)
apply(subgoal_tac "EX n. [] : Rep_domT ((F D ^^ n) (%p. Abs_domT {[]}) p)")
apply(erule exE)
apply(rule_tac x="Rep_domT ((F D ^^ n) (%p. Abs_domT {[]}) p)" in exI)
apply(rule conjI)
apply(rule_tac x="n" in exI)
apply(clarsimp)
apply(clarsimp)
apply(rule_tac x="0" in exI)
apply(clarsimp)
apply(unfold prefix_closed_def)
apply(clarsimp)
apply(rule_tac x="Rep_domT ((F D ^^ n) (%p. Abs_domT {[]}) p)" in exI)
apply(rule conjI)
apply(rule_tac x="n" in exI)
apply(clarsimp)
by (metis domT_Rep_prefix)

lemma deno_sem_1_0:
  "F D u <= u ==>
  (F D ^^ n) (%p. Abs_domT {[]}) <= u"
apply(induct_tac n)
apply(clarsimp)
apply(rule le_funI)
apply(rule Abs_domT_I2)
apply(clarsimp)
apply(clarsimp)
apply(subgoal_tac "(F D ^^ Suc n) (%p. Abs_domT {[]}) <= F D u")
apply(erule order_trans)
apply(assumption)
apply(clarsimp)
apply(rule_tac f="F D" in monoD)
apply(rule mono_csp)
apply(assumption)
done

lemma fun_Sup:
  "Sup (A::('a => ('b::complete_lattice)) set) = (%x. Sup {y. EX f:A. y = f x})"
apply(rule antisym)
apply(rule Sup_least)
apply(rename_tac g)
apply(rule le_funI)
apply(rule Sup_upper)
apply(clarsimp)
apply(rule_tac x="g" in bexI)
apply(rule refl)
apply(assumption)
apply(rule le_funI)
apply(clarsimp)
apply(rule Sup_least)
apply(clarsimp)
by (metis SUP_upper2 eq_iff)

lemma traces_continuous_STOP:
  "traces STOP (%x. Sup {y. EX f:A. y = f x}) =
    Sup {y. EX f:A. y = traces STOP f}"
apply(unfold traces_def)
apply(unfold domT_Sup_def)
apply(clarsimp)
apply(subst Abs_domT_inject)
apply(clarsimp)
defer
apply(subgoal_tac "EX f. f : A")
apply(clarsimp)
apply (metis Abs_domT_inverse domT_STOP)
apply (metis all_not_in_conv)
apply(subgoal_tac "EX f. f : A")
apply(clarsimp)
apply (metis Rep_domT)
by (metis all_not_in_conv)

lemma otraces_rc_traces:
  "s : otraces_r (G D) ($(p, n)) ==>
   s : Rep_domT ((F D ^^ n) (%p. Abs_domT {[]}) p)"
apply(subgoal_tac "(%p. otraces (G D) ($(p, n))) <= (F D ^^ n) (%p. Abs_domT {[]})")
prefer 2
apply(rule lm3_4)
apply(drule_tac x="p" in le_funD)
apply(unfold otraces_def)
apply(drule Abs_domT_D2)
apply(rule otraces_domT)
apply(erule subsetD)
apply(assumption)
done

definition deno_sem3 :: "('p => ('p, 'a) proc) => 'p => 'a domT" where
  "deno_sem3 D = (%p. Abs_domT (Union {X. EX n. X = Rep_domT ((((F D)^^n) (%p. (Abs_domT {[]}))) p)}))"

lemma otraces_deno_sem3:
  "(%p. otraces D ($p)) <= deno_sem3 D"
apply(unfold deno_sem3_def)
apply(unfold le_fun_def)
apply(clarsimp)
apply(unfold otraces_def)
apply(rule Abs_domT_I2)
apply(rule subsetI)
apply(rename_tac s)
apply(subst Abs_domT_inverse)
apply (metis deno_sem2_domT)
apply(subst Union_iff)
apply(clarsimp)
apply(drule otraces_r_rc)
apply(clarsimp)
apply(drule otraces_rc_traces)
apply(rule_tac x="Rep_domT ((F D ^^ n) (%p. Abs_domT {[]}) x)" in exI)
apply(clarsimp)
apply(rule_tac x="n" in exI)
apply(clarsimp)
apply(rule otraces_domT)
done

lemma deno_sem_1:
  "deno_sem3 D <= deno_sem D"
apply(unfold deno_sem_def)
apply(rule lfp_greatest)
apply(unfold deno_sem3_def)
apply(rule le_funI)
apply(rule Abs_domT_I2)
defer
apply(rule deno_sem2_domT)
apply(rule subsetI)
apply(unfold Union_iff)
apply(clarsimp)
apply(drule_tac n="n" in deno_sem_1_0)
by (metis domT_less_eq_def le_funD subsetD)

lemma otraces_deno_sem:
  "(%p. otraces D ($p)) <= deno_sem D"
apply(subgoal_tac "(%p. otraces D ($p)) <= deno_sem3 D")
apply(erule order_trans)
apply(rule deno_sem_1)
apply(rule otraces_deno_sem3)
done

lemma "deno_sem2 D = deno_sem3 D"
apply(unfold deno_sem2_def deno_sem3_def)
apply(subst fun_Sup)
apply(subst domT_Sup_def)
apply(rule ext)
apply(clarsimp)
apply(rule conjI)
apply(clarsimp)
apply(subst Abs_domT_inject)
apply(clarsimp)
apply metis
apply(rule antisym)
apply(clarsimp)
apply metis
apply(clarsimp)
apply(erule contrapos_pp)
apply(simp)
apply metis
apply(clarsimp)
apply(subst Abs_domT_inject)
defer
apply (metis deno_sem2_domT)
apply(rule antisym)
apply(clarsimp)
apply metis
apply(clarsimp)
apply metis
apply(unfold domT_def)
apply(clarsimp)
apply(unfold HC_T1_def)
apply(clarsimp)
apply(rule conjI)
apply (metis HC_T1_Rep_domT HC_T1_def)
apply(unfold prefix_closed_def)
apply(clarsimp)
by (metis domT_Rep_prefix)

lemma operational_denotational_equiv:
  "(%p. otraces D ($p)) = deno_sem D"
apply(rule antisym)
apply(rule otraces_deno_sem)
apply(rule deno_sem_otraces)
done

end
