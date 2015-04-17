theory Equivalence_Implies_Bisimilarity
imports
  Logical_Equivalence
begin

section \<open>Theorem 10: Logical Equivalence Implies Bisimilarity\<close>

context indexed_nominal_ts
begin

  definition distinguishing_formula :: "('idx, 'pred, 'act) formula \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    ("_ distinguishes _ from _" [100,100,100] 100)
  where
    "x distinguishes P from Q \<equiv> P \<Turnstile> x \<and> \<not> Q \<Turnstile> x"

  lemma distinguishing_formula_eqvt [eqvt]:
    assumes "x distinguishes P from Q" shows "(p \<bullet> x) distinguishes (p \<bullet> P) from (p \<bullet> Q)"
  using assms unfolding distinguishing_formula_def
  by (metis permute_minus_cancel(2) valid_eqvt)

  lemma equivalent_iff_not_distinguished: "(P =\<cdot> Q) \<longleftrightarrow> \<not>(\<exists>x. x distinguishes P from Q)"
  by (metis (full_types) distinguishing_formula_def logically_equivalent_def valid_Not)

  text \<open>Lemma~9.\<close>

  lemma distinguished_bounded_support:
    assumes "x distinguishes P from Q"
    obtains y where "supp y \<subseteq> supp P" and "y distinguishes P from Q"
  proof -
    let ?B = "{p \<bullet> x|p. supp P \<sharp>* p}"
    have "supp P supports ?B"
      apply (auto simp add: supports_def)
       apply (rename_tac p)
       apply (rule_tac x="p + (a \<rightleftharpoons> b)" in exI)
       apply (rule conjI)
        apply (metis permute_plus)
       apply (metis fresh_perm fresh_star_def fresh_star_plus supp_eqvt swap_atom_simps(3) swap_set_not_in)
      apply (rule_tac x="p + (a \<rightleftharpoons> b)" in exI)
      apply (rule conjI)
       apply (metis permute_plus permute_swap_cancel)
      apply (metis fresh_perm fresh_star_def fresh_star_plus supp_eqvt swap_atom_simps(3) swap_set_not_in)
      done
    then have supp_B_subset_supp_P: "supp ?B \<subseteq> supp P"
      by (metis (erased, lifting) finite_supp supp_is_subset)
    then have finite_supp_B: "finite (supp ?B)"
      using finite_supp rev_finite_subset by blast
    have "?B \<subseteq> (\<lambda>p. p \<bullet> x) ` UNIV"
      by auto
    then have "|?B| \<le>o |UNIV :: perm set|"
      by (rule surj_imp_ordLeq)
    also have "|UNIV :: perm set| <o |UNIV :: 'idx set|"
      by (metis card_idx_perm)
    also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
      by (metis Cnotzero_UNIV ordLeq_csum2)
    finally have card_B: "|?B| <o natLeq +c |UNIV :: 'idx set|" .
    let ?y = "Conj (Abs_bset ?B) :: ('idx, 'pred, 'act) formula"
    from finite_supp_B and card_B and supp_B_subset_supp_P have "supp ?y \<subseteq> supp P"
      by simp
    moreover have "?y distinguishes P from Q"
      unfolding distinguishing_formula_def proof
        from assms show "P \<Turnstile> ?y"
          by (auto simp add: card_B finite_supp_B) (metis distinguishing_formula_def supp_perm_eq valid_eqvt)
      next
        from assms show "\<not> Q \<Turnstile> ?y"
          by (auto simp add: card_B finite_supp_B) (metis distinguishing_formula_def permute_zero fresh_star_zero)
      qed
    ultimately show ?thesis ..
  qed

  lemma equivalence_is_bisimulation: "is_bisimulation logically_equivalent"
  proof -
    have "symp logically_equivalent"
      by (metis logically_equivalent_def sympI)
    moreover
    {
      fix P Q \<phi> assume "P =\<cdot> Q" then have "P \<turnstile> \<phi> = Q \<turnstile> \<phi>"
        by (metis logically_equivalent_def valid_Pred)
    }
    moreover
    {
      fix P Q \<alpha> P' assume "P =\<cdot> Q" and "bn \<alpha> \<sharp>* Q" and "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
      then have "\<exists>Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> P' =\<cdot> Q'"
        proof -
          {
            let ?Q' = "{Q'. Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>}"
            assume "\<forall>Q'\<in>?Q'. \<not> P' =\<cdot> Q'"
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act) formula. x distinguishes P' from Q'"
              by (metis equivalent_iff_not_distinguished)
            then have "\<forall>Q'\<in>?Q'. \<exists>x :: ('idx, 'pred, 'act) formula. supp x \<subseteq> supp P' \<and> x distinguishes P' from Q'"
              by (metis distinguished_bounded_support)
            then obtain f :: "'state \<Rightarrow> ('idx, 'pred, 'act) formula" where
              *: "\<forall>Q'\<in>?Q'. supp (f Q') \<subseteq> supp P' \<and> (f Q') distinguishes P' from Q'"
              by metis
            have "supp P' supports (f ` ?Q')"
              apply (auto simp add: supports_def image_def)
               apply (rename_tac abQ')
               apply (rule_tac x="(a \<rightleftharpoons> b) \<bullet> abQ'" in exI)
               apply (rule context_conjI)
                apply (metis abs_residual_pair_eqvt permute_swap_cancel transition_eqvt)
               apply (subgoal_tac "supp (f ((a \<rightleftharpoons> b) \<bullet> abQ')) \<subseteq> supp P'")
                prefer 2
                apply (metis "*" mem_Collect_eq)
               apply (subgoal_tac "(a \<rightleftharpoons> b) \<bullet> f ((a \<rightleftharpoons> b) \<bullet> abQ') = f ((a \<rightleftharpoons> b) \<bullet> abQ')")
                prefer 2
                apply (metis contra_subsetD supp_supports supports_def)
               apply (metis eqvt_lambda minus_swap unpermute_def)
              apply (rename_tac Q')
              apply (rule_tac x="(a \<rightleftharpoons> b) \<bullet> Q'" in exI)
              apply (rule conjI)
               apply (metis abs_residual_pair_eqvt transition_eqvt)
              apply (subgoal_tac "(a \<rightleftharpoons> b) \<bullet> f Q' = f Q'")
               prefer 2
               apply (metis "*" contra_subsetD mem_Collect_eq supp_supports supports_def)
              apply (metis eqvt_bound eqvt_lambda permute_minus_cancel(2))
              done
            then have supp_image_subset_supp_P': "supp (f ` ?Q') \<subseteq> supp P'"
              by (metis (erased, lifting) finite_supp supp_is_subset)
            then have finite_supp_image: "finite (supp (f ` ?Q'))"
              using finite_supp rev_finite_subset by blast
            have "|f ` ?Q'| \<le>o |UNIV :: 'state set|"
              by (metis card_of_UNIV card_of_image ordLeq_transitive)
            also have "|UNIV :: 'state set| <o |UNIV :: 'idx set|"
              by (metis card_idx_state)
            also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
              by (metis Cnotzero_UNIV ordLeq_csum2)
            finally have card_image: "|f ` ?Q'| <o natLeq +c |UNIV :: 'idx set|" .
            let ?y = "Conj (Abs_bset (f ` ?Q')) :: ('idx, 'pred, 'act) formula"
            have "P \<Turnstile> Act \<alpha> ?y"
              apply (simp add: valid_Act)
              apply (rule_tac x=\<alpha> in exI)
              apply (rule_tac x="?y" in exI)
              apply simp
              apply (rule_tac x=P' in exI)
              apply (rule conjI)
               apply (fact `P \<rightarrow> \<langle>\<alpha>,P'\<rangle>`)
              apply (auto simp add: finite_supp_image card_image)
              apply (metis "*" distinguishing_formula_def mem_Collect_eq)
              done
            moreover have "\<not> Q \<Turnstile> Act \<alpha> ?y"
              apply (auto simp add: `bn \<alpha> \<sharp>* Q` valid_Act_fresh)
              apply (auto simp add: finite_supp_image card_image)
              apply (metis "*" distinguishing_formula_def mem_Collect_eq)
              done
            ultimately have False
              by (metis `P =\<cdot> Q` logically_equivalent_def)
          }
          then show ?thesis by auto
        qed
    }
    ultimately show ?thesis
      unfolding is_bisimulation_def by metis
  qed

  theorem equivalence_implies_bisimilarity: assumes "P =\<cdot> Q" shows "P \<sim>\<cdot> Q"
  using assms by (metis bisimilar_def equivalence_is_bisimulation)

end

end

