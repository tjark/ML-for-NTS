theory Bisimilarity_Implies_Equivalence
imports
  Logical_Equivalence
begin

section \<open>Bisimilarity Implies Logical Equivalence\<close>

lemma finite_supp_permute [simp]: "finite (supp (p \<bullet> x)) = finite (supp x)"
by (metis permute_finite supp_eqvt)

context indexed_nominal_ts
begin

  theorem bisimilarity_implies_equivalence: assumes "P \<sim>\<cdot> Q" shows "P =\<cdot> Q"
  unfolding logically_equivalent_def proof
    fix x :: "('idx, 'pred, 'act) formula"
    from assms show "P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    proof (induction x arbitrary: P Q)
      case (Conj xset) then show ?case
        by simp
    next
      case Not then show ?case
        by simp
    next
      case Pred then moreover have "Q \<sim>\<cdot> P"
        by (metis bisimilar_symp sympE)
      ultimately show ?case
        by (auto simp add: bisimilar_def is_bisimulation_def)
    next
      case (Act \<alpha> x) then show ?case
      apply (auto simp add: valid_Act)
      (*1*)
       apply (subgoal_tac "\<exists>q. (q \<bullet> bn \<alpha>') \<sharp>* Q \<and> supp (Act \<alpha>' x', \<langle>\<alpha>', P'\<rangle>) \<sharp>* q")
        prefer 2
        apply (rule at_set_avoiding2)
           apply (metis bn_finite)
          apply (metis finite_supp)
         apply (metis finite_UnI finite_supp finite_supp_abs_residual_pair supp_Pair)
        apply (auto simp add: fresh_star_def fresh_def supp_Pair supp_abs_residual_pair)[1]
       apply auto[1]
       apply (rule_tac x="q \<bullet> \<alpha>'" in exI)
       apply (rule_tac x="q \<bullet> x'" in exI)
       apply (rule conjI)
        apply (metis Act_eqvt fresh_star_Un supp_Pair supp_perm_eq_test)
       apply (subgoal_tac "\<langle>\<alpha>',P'\<rangle> = \<langle>q \<bullet> \<alpha>',q \<bullet> P'\<rangle>")
        prefer 2
        apply (metis abs_residual_pair_eqvt fresh_star_Un supp_Pair supp_perm_eq_test)
       apply simp
       apply (erule_tac \<alpha>="q \<bullet> \<alpha>'" and P'="q \<bullet> P'" in bisimilar_simulation_step)
         apply (metis bn_eqvt)
        apply assumption
       apply (rule_tac x=Q' in exI)
       apply (rule conjI)
        apply assumption
       apply (auto simp add: Act_eq_iff Act\<^sub>\<alpha>_eq_iff alphas)[1]
       apply (rename_tac p')
       apply (subgoal_tac "p' \<bullet> x = x'")
        apply (metis bisimilar_eqvt permute_minus_cancel(2) valid_eqvt)  -- \<open>patience\<close>
       apply (metis Rep_formula_inverse Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep permute_Tree\<^sub>\<alpha>.abs_eq permute_formula.rep_eq)
      (*2*)
      apply (subgoal_tac "\<exists>q. (q \<bullet> bn \<alpha>') \<sharp>* P \<and> supp (Act \<alpha>' x', \<langle>\<alpha>', P'\<rangle>) \<sharp>* q")
       prefer 2
       apply (rule at_set_avoiding2)
          apply (metis bn_finite)
         apply (metis finite_supp)
        apply (metis finite_UnI finite_supp finite_supp_abs_residual_pair supp_Pair)
       apply (auto simp add: fresh_star_def fresh_def supp_Pair supp_abs_residual_pair)[1]
      apply auto[1]
      apply (rule_tac x="q \<bullet> \<alpha>'" in exI)
      apply (rule_tac x="q \<bullet> x'" in exI)
      apply (rule conjI)
       apply (metis Act_eqvt fresh_star_Un supp_Pair supp_perm_eq_test)
      apply (subgoal_tac "\<langle>\<alpha>',P'\<rangle> = \<langle>q \<bullet> \<alpha>',q \<bullet> P'\<rangle>")
       prefer 2
       apply (metis abs_residual_pair_eqvt fresh_star_Un supp_Pair supp_perm_eq_test)
      apply simp
      apply (subgoal_tac "Q \<sim>\<cdot> P")
       prefer 2
       apply (metis bisimilar_symp sympE)
      apply (thin_tac "P \<sim>\<cdot> Q")
      apply (erule_tac \<alpha>="q \<bullet> \<alpha>'" and P'="q \<bullet> P'" in bisimilar_simulation_step)
        apply (metis bn_eqvt)
       apply assumption
      apply (rule_tac x=Q' in exI)
      apply (rule conjI)
       apply assumption
      apply (auto simp add: Act_eq_iff Act\<^sub>\<alpha>_eq_iff alphas)[1]
      apply (rename_tac p')
      apply (subgoal_tac "x' = p' \<bullet> x")
       apply (metis bisimilar_eqvt permute_minus_cancel(2) valid_eqvt)   -- \<open>patience\<close>
      apply (metis Rep_formula_inverse Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep permute_Tree\<^sub>\<alpha>.abs_eq permute_formula.rep_eq)
      done
    qed
  qed

end

end

