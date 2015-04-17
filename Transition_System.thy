theory Transition_System
imports
  Residual
begin

section \<open>Basic Lemmas\<close>

lemma symp_eqvt [eqvt]:
  assumes "symp R" shows "symp (p \<bullet> R)"
using assms unfolding symp_def by (subst permute_fun_def)+ (simp add: permute_pure)


section \<open>Nominal Transition Systems and Bisimulations\<close>

subsection \<open>Definition 1: Nominal transition systems\<close>

locale nominal_ts =
  fixes satisfies :: "'state\<Colon>fs \<Rightarrow> 'pred\<Colon>fs \<Rightarrow> bool"                 (infix "\<turnstile>" 70)
    and transition :: "'state \<Rightarrow> ('act\<Colon>bn,'state) residual \<Rightarrow> bool"  (infix "\<rightarrow>" 70)
  assumes satisfies_eqvt [eqvt]: "P \<turnstile> \<phi> \<Longrightarrow> p \<bullet> P \<turnstile> p \<bullet> \<phi>"
      and transition_eqvt [eqvt]: "P \<rightarrow> \<alpha>Q \<Longrightarrow> p \<bullet> P \<rightarrow> p \<bullet> \<alpha>Q"
begin
 
  lemma transition_eqvt':
    assumes "P \<rightarrow> \<langle>\<alpha>,Q\<rangle>" shows "p \<bullet> P \<rightarrow> \<langle>p \<bullet> \<alpha>, p \<bullet> Q\<rangle>"
  using assms by (metis abs_residual_pair_eqvt transition_eqvt)

end
 
subsection \<open>Definition 2: Bisimulations\<close>
 
context nominal_ts
begin

  definition is_bisimulation :: "('state \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> bool" where
    "is_bisimulation R \<equiv>
      symp R \<and>
      (\<forall>P Q. R P Q \<longrightarrow> (\<forall>\<phi>. P \<turnstile> \<phi> \<longrightarrow> Q \<turnstile> \<phi>)) \<and>
      (\<forall>P Q. R P Q \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* Q \<longrightarrow> P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> R P' Q')))"

  definition bisimilar :: "'state \<Rightarrow> 'state \<Rightarrow> bool"  (infix "\<sim>\<cdot>" 100) where
    "P \<sim>\<cdot> Q \<equiv> \<exists>R. is_bisimulation R \<and> R P Q"

  text \<open>Proposition 1: @{const bisimilar} is an equivariant equivalence relation.\<close>

  lemma is_bisimulation_eqvt [eqvt]:
    assumes "is_bisimulation R" shows "is_bisimulation (p \<bullet> R)"
  using assms
  apply (auto simp add: is_bisimulation_def)
     apply (metis symp_eqvt)
    apply (subgoal_tac "R (-p \<bullet> P) (-p \<bullet> Q)")
     apply (metis permute_minus_cancel(1) satisfies_eqvt)
    apply (metis (full_types) False_eqvt permute_fun_def)
  apply (subgoal_tac "R (-p \<bullet> P) (-p \<bullet> Q)")
   prefer 2
   apply (metis (full_types) False_eqvt permute_fun_def)
  apply (thin_tac "\<forall>P Q. R P Q \<longrightarrow> (\<forall>\<phi>. P \<turnstile> \<phi> \<longrightarrow> Q \<turnstile> \<phi>)")
  apply (drule_tac x="-p \<bullet> P" in spec)
  apply (drule_tac x="-p \<bullet> Q" in spec)
  apply simp
  apply (drule_tac x="-p \<bullet> \<alpha>" in spec)
  apply (drule mp)
   apply (metis bn_eqvt fresh_star_permute_iff)
  apply (drule_tac x="-p \<bullet> P'" in spec)
  apply (drule mp)
   apply (metis transition_eqvt')
  apply auto
  apply (rule_tac x="p \<bullet> Q'" in exI)
  apply (rule conjI)
   apply (metis permute_minus_cancel(1) transition_eqvt')
  apply (metis eqvt_apply eqvt_lambda permute_boolI unpermute_def)
  done

  lemma bisimilar_eqvt [eqvt]:
    assumes "P \<sim>\<cdot> Q" shows "(p \<bullet> P) \<sim>\<cdot> (p \<bullet> Q)"
  using assms
  apply (auto simp add: bisimilar_def)
  apply (rule_tac x="p \<bullet> R" in exI)
  apply (simp add: is_bisimulation_eqvt)
  apply (metis eqvt_apply permute_boolI)
  done

  lemma bisimilar_reflp: "reflp bisimilar"
  apply (rule reflpI)
  apply (simp add: bisimilar_def)
  apply (rule_tac x="op =" in exI)
  apply (simp add: is_bisimulation_def symp_def)
  done

  lemma bisimilar_symp: "symp bisimilar"
  apply (rule sympI)
  apply (auto simp add: bisimilar_def)
  apply (rule_tac x="R" in exI)
  apply (simp add: is_bisimulation_def symp_def)
  done

  lemma bisimilar_is_bisimulation: "is_bisimulation bisimilar"
  apply (auto simp add: is_bisimulation_def bisimilar_def)
   apply (fact bisimilar_symp)
  apply blast
  done

  lemma bisimilar_transp: "transp bisimilar"
  apply (rule transpI)
  apply (subst bisimilar_def)

  apply (rule_tac x="bisimilar OO bisimilar" in exI)
  apply auto
  apply (thin_tac ?P)+
  apply (auto simp add: is_bisimulation_def)
    apply (auto simp add: symp_def)[1]
    apply (metis bisimilar_symp relcompp.simps sympE)
   apply (metis bisimilar_def is_bisimulation_def)
  apply (rename_tac B \<alpha> P')

  -- \<open>rename~@{term "\<langle>\<alpha>,P'\<rangle>"} to avoid~@{term B}, without touching~@{term Q}\<close>
  apply (subgoal_tac "\<exists>p. (p \<bullet> bn \<alpha>) \<sharp>* B \<and> supp (\<langle>\<alpha>,P'\<rangle>, Q) \<sharp>* p")
   prefer 2
   apply (rule at_set_avoiding2)
      apply (rule bn_finite)
     apply (rule finite_supp)
    apply (simp add: supp_abs_residual_pair supp_Pair)
    apply (metis finite_Diff finite_Un finite_supp)
   apply (metis bn_abs_residual_fresh fresh_star_Pair)
  apply (clarsimp simp add: bn_eqvt supp_Pair fresh_star_Un)

  apply (subgoal_tac "\<langle>p \<bullet> \<alpha>, p \<bullet> P'\<rangle> = \<langle>\<alpha>,P'\<rangle>")
   prefer 2
   apply (simp add: residual.abs_eq_iff Abs_eq_iff)
   apply (rule_tac x="-p" in exI)
   apply (simp add: alphas bn_eqvt)
   apply (rule context_conjI)
    apply (metis abs_residual_pair_eqvt supp_abs_residual_pair supp_perm_eq_test)
   apply (metis fresh_minus_perm fresh_star_def supp_abs_residual_pair)

  apply (subgoal_tac "\<exists>pB'. B \<rightarrow> \<langle>p \<bullet> \<alpha>, pB'\<rangle> \<and> (p \<bullet> P') \<sim>\<cdot> pB'")
   prefer 2
   apply (metis (full_types) bisimilar_is_bisimulation is_bisimulation_def)
  apply clarify

  apply (subgoal_tac "bn (p \<bullet> \<alpha>) \<sharp>* Q")
   prefer 2
   apply (metis bn_eqvt fresh_star_permute_iff supp_perm_eq_test)

  apply (subgoal_tac "\<exists>pQ'. Q \<rightarrow> \<langle>p \<bullet> \<alpha>, pQ'\<rangle> \<and> pB' \<sim>\<cdot> pQ'")
   prefer 2
   apply (metis (full_types) bisimilar_is_bisimulation is_bisimulation_def)
  apply clarify

  apply (rule_tac x="-p \<bullet> pQ'" in exI)
  apply (rule conjI)
   apply (metis permute_minus_cancel(2) supp_perm_eq_test transition_eqvt')
  apply (metis (mono_tags) bisimilar_eqvt permute_minus_cancel(2) relcompp.relcompI)
  done

  lemma bisimilar_equivp: "equivp bisimilar"
  by (metis bisimilar_reflp bisimilar_symp bisimilar_transp equivp_reflp_symp_transp)

  lemma bisimilar_simulation_step:
    assumes "P \<sim>\<cdot> Q" and "bn \<alpha> \<sharp>* Q" and "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
    obtains Q' where "Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>" and "P' \<sim>\<cdot> Q'"
  using assms by (metis (poly_guards_query) bisimilar_is_bisimulation is_bisimulation_def)

end

end

