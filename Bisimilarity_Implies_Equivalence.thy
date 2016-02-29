theory Bisimilarity_Implies_Equivalence
imports
  Logical_Equivalence
begin

section \<open>Bisimilarity Implies Logical Equivalence\<close>

lemma finite_supp_permute [simp]: "finite (supp (p \<bullet> x)) = finite (supp x)"
by (metis permute_finite supp_eqvt)

context indexed_nominal_ts
begin

  lemma bisimilarity_implies_equivalence_Act:
    assumes "\<And>P Q. P \<sim>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x"
    and "P \<sim>\<cdot> Q"
    and "P \<Turnstile> Act \<alpha> x"
    shows "Q \<Turnstile> Act \<alpha> x"
  proof -
    from `P \<Turnstile> Act \<alpha> x` obtain \<alpha>' x' P' where eq: "Act \<alpha> x = Act \<alpha>' x'" and trans: "P \<rightarrow> \<langle>\<alpha>',P'\<rangle>" and valid: "P' \<Turnstile> x'"
      unfolding valid_Act by metis
    from eq obtain p where 1: "x' = p \<bullet> x"
      by (auto simp add: Act_eq_iff Act\<^sub>\<alpha>_eq_iff alphas) (metis Rep_formula_inverse Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep permute_Tree\<^sub>\<alpha>.abs_eq permute_formula.rep_eq)
    -- \<open>rename~@{term "Act \<alpha>' x'"} to avoid~@{term Q}, without touching~@{term "\<langle>\<alpha>',P'\<rangle>"}\<close>
    obtain q where 2: "(q \<bullet> bn \<alpha>') \<sharp>* Q" and 3: "supp (Act \<alpha>' x', \<langle>\<alpha>',P'\<rangle>) \<sharp>* q"
      proof (rule at_set_avoiding2[of "bn \<alpha>'" Q "(Act \<alpha>' x', \<langle>\<alpha>',P'\<rangle>)", THEN exE])
        show "finite (bn \<alpha>')" by (fact bn_finite)
      next
        show "finite (supp Q)" by (fact finite_supp)
      next
        show "finite (supp (Act \<alpha>' x', \<langle>\<alpha>',P'\<rangle>))" by (simp add: finite_supp supp_Pair)
      next
        show "bn \<alpha>' \<sharp>* (Act \<alpha>' x', \<langle>\<alpha>',P'\<rangle>)"
          by (metis (no_types, lifting) Diff_iff bn_abs_residual_fresh fresh_def fresh_star_Pair fresh_star_def supp_Act)
      qed metis
    from eq and 3 have eq': "Act \<alpha> x = Act (q \<bullet> \<alpha>') (q \<bullet> x')"
      using fresh_star_supp_conv perm_supp_eq by fastforce
    from 3 have "\<langle>\<alpha>',P'\<rangle> = \<langle>q \<bullet> \<alpha>',q \<bullet> P'\<rangle>"
      by (metis abs_residual_pair_eqvt fresh_star_Un supp_Pair supp_perm_eq)
    with `P \<sim>\<cdot> Q` and 2 and trans obtain Q' where trans': "Q \<rightarrow> \<langle>q \<bullet> \<alpha>',Q'\<rangle>" and "(q \<bullet> P') \<sim>\<cdot> Q'"
      by (metis bisimilar_simulation_step bn_eqvt)
    then have "(-p \<bullet> P') \<sim>\<cdot> (-p \<bullet> -q \<bullet> Q')"
      by (metis bisimilar_eqvt permute_minus_cancel(1))
    moreover from 1 and valid have "-p \<bullet> P' \<Turnstile> x"
      by (metis permute_minus_cancel(1) valid_eqvt)
    ultimately have "Q' \<Turnstile> q \<bullet> x'"
      using 1 and `\<And>P Q. P \<sim>\<cdot> Q \<Longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x` by (metis permute_minus_cancel(2) valid_eqvt)
    with eq' and trans' show "Q \<Turnstile> Act \<alpha> x"
      unfolding valid_Act by metis
  qed

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
      case Pred then show ?case
        by (metis bisimilar_is_bisimulation is_bisimulation_def symp_def valid_Pred)
    next
      case (Act \<alpha> x) then show ?case
        by (metis bisimilar_symp bisimilarity_implies_equivalence_Act sympE)
    qed
  qed

end

end

