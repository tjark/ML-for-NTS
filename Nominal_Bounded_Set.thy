theory Nominal_Bounded_Set
imports
  Nominal2
  Bounded_Set
begin

section \<open>Bounded Sets Equipped With a Permutation Action\<close>

text \<open>Bounded sets are equipped with a permutation action, provided their elements are.\<close>

instantiation bset :: (pt,type) pt
begin

  lift_definition permute_bset :: "perm \<Rightarrow> 'a set['b] \<Rightarrow> 'a set['b]" is
    permute
  proof -
    fix p and A :: "'a set"
    have "|p \<bullet> A| \<le>o |A|" by (simp add: permute_set_eq_image)
    also assume "|A| <o natLeq +c |UNIV :: 'b set|"
    finally show "|p \<bullet> A| <o natLeq +c |UNIV :: 'b set|" .
  qed

  instance
  by default (transfer, simp)+

end

lemma Abs_bset_eqvt [simp]:
  assumes "|A| <o natLeq +c |UNIV :: 'k set|"
  shows "p \<bullet> (Abs_bset A :: 'a::pt set['k]) = Abs_bset (p \<bullet> A)"
by (simp add: permute_bset_def map_bset_def image_def permute_set_def) (metis (no_types, lifting) Abs_bset_inverse' assms)

lemma supp_Abs_bset [simp]:
  assumes "|A| <o natLeq +c |UNIV :: 'k set|"
  shows "supp (Abs_bset A :: 'a::pt set['k]) = supp A"
proof -
  from assms have "\<And>p. p \<bullet> (Abs_bset A :: 'a::pt set['k]) \<noteq> Abs_bset A \<longleftrightarrow> p \<bullet> A \<noteq> A"
    by simp (metis map_bset.rep_eq permute_set_eq_image set_bset_inverse set_bset_to_set_bset)
  then show ?thesis
    unfolding supp_def by simp
qed

lemma map_bset_permute: "p \<bullet> B = map_bset (permute p) B"
by transfer (auto simp add: image_def permute_set_def)

lemma set_bset_eqvt [eqvt]:
  "p \<bullet> set_bset B = set_bset (p \<bullet> B)"
by transfer simp

lemma map_bset_eqvt [eqvt]:
  "p \<bullet> map_bset f B = map_bset (p \<bullet> f) (p \<bullet> B)"
by transfer simp

end

