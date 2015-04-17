theory Formula
imports
  Nominal_Bounded_Set
  Nominal_Wellfounded
  Residual
begin

section \<open>Definition 3: Infinitary Formulae\<close>

subsection \<open>Infinitely branching trees\<close>

text \<open>First, we define a type of trees, with a constructor~@{term tConj} that maps (potentially
infinite) sets of trees into trees. To avoid paradoxes (note that there is no injection from the
powerset of trees into the set of trees), the cardinality of the argument set must be bounded.\<close>

datatype_new ('idx,'pred,'act) Tree =
    tConj "('idx,'pred,'act) Tree set['idx]"  -- \<open>potentially infinite sets of trees\<close>
  | tNot "('idx,'pred,'act) Tree"
  | tPred 'pred
  | tAct 'act "('idx,'pred,'act) Tree"

text \<open>The (automatically generated) induction principle for trees allows us to prove that the
following relation over trees is well-founded. This will be useful for termination proofs when we
define functions by recursion over trees.\<close>

inductive_set Tree_wf :: "('idx,'pred,'act) Tree rel" where
  "t \<in> set_bset tset \<Longrightarrow> (t, tConj tset) \<in> Tree_wf"
| "(t, tNot t) \<in> Tree_wf"
| "(t, tAct \<alpha> t) \<in> Tree_wf"

lemma wf_Tree_wf: "wf Tree_wf"
unfolding wf_def
proof (rule allI, rule impI, rule allI)
  fix P :: "('idx,'pred,'act) Tree \<Rightarrow> bool" and t
  assume "\<forall>x. (\<forall>y. (y, x) \<in> Tree_wf \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P t"
    proof (induction t)
      case tConj then show ?case
        by (metis Tree.distinct(2) Tree.distinct(5) Tree.inject(1) Tree_wf.cases)
    next
      case tNot then show ?case
        by (metis Tree.distinct(1) Tree.distinct(9) Tree.inject(2) Tree_wf.cases)
    next
      case tPred then show ?case
        by (metis Tree.distinct(11) Tree.distinct(3) Tree.distinct(7) Tree_wf.cases)
    next
      case tAct then show ?case
        by (metis Tree.distinct(10) Tree.distinct(6) Tree.inject(4) Tree_wf.cases)
    qed
qed

text \<open>We define a permutation operation on the type of trees.\<close>

instantiation Tree :: (type, pt, pt) pt
begin

  primrec permute_Tree :: "perm \<Rightarrow> (_,_,_) Tree \<Rightarrow> (_,_,_) Tree" where
    "p \<bullet> (tConj tset) = tConj (map_bset (permute p) tset)"  -- \<open>neat trick to get around the fact that~@{term tset} is not of permutation type yet\<close>
  | "p \<bullet> (tNot t) = tNot (p \<bullet> t)"
  | "p \<bullet> (tPred \<phi>) = tPred (p \<bullet> \<phi>)"
  | "p \<bullet> (tAct \<alpha> t) = tAct (p \<bullet> \<alpha>) (p \<bullet> t)"

  instance
  proof
    fix t :: "(_,_,_) Tree"
    show "0 \<bullet> t = t"
    proof (induction t)
      case tConj then show ?case
        by (simp, transfer) (auto simp: image_def)
    qed simp_all
  next
    fix p q :: perm and t :: "(_,_,_) Tree"
    show "(p + q) \<bullet> t = p \<bullet> q \<bullet> t"
      proof (induction t)
        case tConj then show ?case
          by (simp, transfer) (auto simp: image_def)
      qed simp_all
  qed

end

text \<open>Now that the type of trees---and hence the type of (bounded) sets of trees---is a permutation
type, we can massage the definition of~@{term "p \<bullet> tConj tset"} into its more usual form.\<close>

lemma permute_Tree_tConj [simp]: "p \<bullet> tConj tset = tConj (p \<bullet> tset)"
by (simp add: map_bset_permute)

declare permute_Tree.simps(1) [simp del]

text \<open>The relation~@{const Tree_wf} is equivariant.\<close>

lemma Tree_wf_eqvt_aux:
  assumes "(t1, t2) \<in> Tree_wf" shows "(p \<bullet> t1, p \<bullet> t2) \<in> Tree_wf"
using assms proof (induction rule: Tree_wf.induct)
  fix t :: "('a,'b,'c) Tree" and tset :: "('a,'b,'c) Tree set['a]"
  assume "t \<in> set_bset tset" then show "(p \<bullet> t, p \<bullet> tConj tset) \<in> Tree_wf"
    by (metis Tree_wf.intros(1) mem_permute_iff permute_Tree_tConj set_bset_eqvt)
next
  fix t :: "('a,'b,'c) Tree"
  show "(p \<bullet> t, p \<bullet> tNot t) \<in> Tree_wf"
    by (metis Tree_wf.intros(2) permute_Tree.simps(2))
next
  fix t :: "('a,'b,'c) Tree" and \<alpha>
  show "(p \<bullet> t, p \<bullet> tAct \<alpha> t) \<in> Tree_wf"
    by (metis Tree_wf.intros(3) permute_Tree.simps(4))
qed

lemma Tree_wf_eqvt [eqvt, simp]: "p \<bullet> Tree_wf = Tree_wf"
apply (auto simp add: permute_set_def)
 apply (metis Tree_wf_eqvt_aux)
apply (metis Tree_wf_eqvt_aux permute_minus_cancel(1))
done

lemma Tree_wf_eqvt': "eqvt Tree_wf"
by (metis Tree_wf_eqvt eqvtI)

text \<open>The definition of~@{const permute} for trees gives rise to the usual notion of support. The
following lemmas, one for each constructor, describe the support of trees.\<close>

lemma supp_tConj [simp]: "supp (tConj tset) = supp tset"
unfolding supp_def by simp

lemma supp_tNot [simp]: "supp (tNot t) = supp t"
unfolding supp_def by simp

lemma supp_tPred [simp]: "supp (tPred \<phi>) = supp \<phi>"
unfolding supp_def by simp

lemma supp_tAct [simp]: "supp (tAct \<alpha> t) = supp \<alpha> \<union> supp t"
unfolding supp_def by (simp add: Collect_imp_eq Collect_neg_eq)


subsection \<open>Trees modulo \<alpha>-equivalence\<close>

text \<open>We generalize the notion of support, which considers whether a permuted element is
\emph{equal} to itself, to arbitrary endorelations.\<close>

definition Supp :: "('a\<Colon>pt \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> atom set" where
  "Supp R x = {a. infinite {b. \<not> R ((a \<rightleftharpoons> b) \<bullet> x) x}}"

lemma Supp_eqvt [eqvt]:
  "p \<bullet> Supp R x = Supp (p \<bullet> R) (p \<bullet> x)"
by (simp add: Supp_def)

text \<open>Usually, the definition of \<alpha>-equivalence presupposes a notion of free variables. Here, to
obtain the correct notion of free variables for infinitary conjunctions, we define \<alpha>-equivalence and
free variables via mutual recursion.

I conjecture that the concept of ``free variables'' is not needed at all: we could directly use the
support modulo \<alpha>-equivalence instead. Working out the details (which might simplify the mutually
recursive definition below) is left for another time.\<close>

text \<open>The following lemmas and constructions are used to prove termination of our mutually recursive
definition.\<close>

lemma Supp_cong [fundef_cong]:
  "\<lbrakk> x=x'; \<And>a b. R ((a \<rightleftharpoons> b) \<bullet> x') x' \<longleftrightarrow> R' ((a \<rightleftharpoons> b) \<bullet> x') x' \<rbrakk> \<Longrightarrow> Supp R x = Supp R' x'"
by (simp add: Supp_def)

lemma rel_bset_cong [fundef_cong]:
  "\<lbrakk> x=x'; y=y'; \<And>a b. a \<in> set_bset x' \<Longrightarrow> b \<in> set_bset y' \<Longrightarrow> R a b \<longleftrightarrow> R' a b \<rbrakk> \<Longrightarrow> rel_bset R x y \<longleftrightarrow> rel_bset R' x' y'"
by (simp add: rel_bset_def rel_set_def)

lemma alpha_set_cong [fundef_cong]:
  "\<lbrakk> bs=bs'; x=x'; R (p' \<bullet> x') y' \<longleftrightarrow> R' (p' \<bullet> x') y'; f x' = f' x'; f y' = f' y'; p=p'; cs=cs'; y=y' \<rbrakk> \<Longrightarrow>
    alpha_set (bs, x) R f p (cs, y) \<longleftrightarrow> alpha_set (bs', x') R' f' p' (cs', y')"
by (simp add: alpha_set)

quotient_type
  ('idx,'pred,'act) Tree\<^sub>p = "('idx,'pred\<Colon>pt,'act\<Colon>bn) Tree" / "hull_relp"
  by (fact hull_relp_equivp)

lemma abs_Tree\<^sub>p_eq [simp]: "abs_Tree\<^sub>p (p \<bullet> t) = abs_Tree\<^sub>p t"
by (metis hull_relp.simps Tree\<^sub>p.abs_eq_iff)

lemma permute_rep_abs_Tree\<^sub>p:
  obtains p where "rep_Tree\<^sub>p (abs_Tree\<^sub>p t) = p \<bullet> t"
by (metis Quotient3_Tree\<^sub>p Tree\<^sub>p.abs_eq_iff rep_abs_rsp hull_relp.simps)

lift_definition Tree_wf\<^sub>p :: "('idx,'pred\<Colon>pt,'act\<Colon>bn) Tree\<^sub>p rel" is
  Tree_wf .

lemma Tree_wf\<^sub>pI [simp]:
  assumes "(a, b) \<in> Tree_wf"
  shows "(abs_Tree\<^sub>p (p \<bullet> a), abs_Tree\<^sub>p b) \<in> Tree_wf\<^sub>p"
using assms by (metis (erased, lifting) Tree\<^sub>p.abs_eq_iff Tree_wf\<^sub>p.abs_eq hull_relp.intros map_prod_simp rev_image_eqI)

lemma Tree_wf\<^sub>p_trivialI [simp]:
  assumes "(a, b) \<in> Tree_wf"
  shows "(abs_Tree\<^sub>p a, abs_Tree\<^sub>p b) \<in> Tree_wf\<^sub>p"
using assms by (metis Tree_wf\<^sub>pI permute_zero)

lemma Tree_wf\<^sub>pE:
  assumes "(a\<^sub>p, b\<^sub>p) \<in> Tree_wf\<^sub>p"
  obtains a b where "a\<^sub>p = abs_Tree\<^sub>p a" and "b\<^sub>p = abs_Tree\<^sub>p b" and "(a,b) \<in> Tree_wf"
using assms by (metis Pair_inject Tree_wf\<^sub>p.abs_eq prod_fun_imageE)

lemma wf_Tree_wf\<^sub>p: "wf Tree_wf\<^sub>p"
apply (rule wf_subset[of "inv_image (hull_rel O Tree_wf) rep_Tree\<^sub>p"])
 apply (metis Tree_wf_eqvt' wf_Tree_wf wf_hull_rel_relcomp wf_inv_image)
apply (auto elim!: Tree_wf\<^sub>pE)
apply (rename_tac t1 t2)
apply (rule_tac t=t1 in permute_rep_abs_Tree\<^sub>p)
apply (rule_tac t=t2 in permute_rep_abs_Tree\<^sub>p)
apply (rename_tac p1 p2)
apply (subgoal_tac "(p2 \<bullet> t1, p2 \<bullet> t2) \<in> Tree_wf")
 apply (subgoal_tac "(p1 \<bullet> t1, p2 \<bullet> t1) \<in> hull_rel")
  apply (metis relcomp.relcompI)
 apply (metis hull_rel.simps permute_minus_cancel(2) permute_plus)
apply (metis Tree_wf_eqvt_aux)
done

fun alpha_Tree_termination :: "('a, 'b, 'c) Tree \<times> ('a, 'b, 'c) Tree + ('a, 'b, 'c) Tree \<Rightarrow> ('a, 'b\<Colon>pt, 'c\<Colon>bn) Tree\<^sub>p set \<times> bool" where
  "alpha_Tree_termination (Inl (t1, t2)) = ({abs_Tree\<^sub>p t1, abs_Tree\<^sub>p t2}, False)"
| "alpha_Tree_termination (Inr t) = ({abs_Tree\<^sub>p t}, True)"

text \<open>Here it comes \ldots\<close>

function (sequential)
  alpha_Tree :: "('idx,'pred\<Colon>pt,'act\<Colon>bn) Tree \<Rightarrow> ('idx,'pred,'act) Tree \<Rightarrow> bool" (infix "=\<^sub>\<alpha>" 50)
  and fv_Tree :: "('idx,'pred,'act) Tree \<Rightarrow> atom set" where
-- \<open>@{const alpha_Tree}\<close>
  alpha_tConj: "tConj tset1 =\<^sub>\<alpha> tConj tset2 \<longleftrightarrow> rel_bset alpha_Tree tset1 tset2"
| alpha_tNot: "tNot t1 =\<^sub>\<alpha> tNot t2 \<longleftrightarrow> t1 =\<^sub>\<alpha> t2"
| alpha_tPred: "tPred \<phi>1 =\<^sub>\<alpha> tPred \<phi>2 \<longleftrightarrow> \<phi>1 = \<phi>2"
-- \<open>the action may have binding names\<close>
| alpha_tAct: "tAct \<alpha>1 t1 =\<^sub>\<alpha> tAct \<alpha>2 t2 \<longleftrightarrow>
    (\<exists>p. (bn \<alpha>1, t1) \<approx>set alpha_Tree fv_Tree p (bn \<alpha>2, t2) \<and> (bn \<alpha>1, \<alpha>1) \<approx>set (op=) supp p (bn \<alpha>2, \<alpha>2))"
| alpha_other: "_ =\<^sub>\<alpha> _ \<longleftrightarrow> False"
-- \<open>@{const fv_Tree}\<close>
-- \<open>the free variables in a conjunction are the support of its \<alpha>-equivalence class\<close>
| fv_tConj: "fv_Tree (tConj tset) = Supp alpha_Tree (tConj tset)"
| fv_tNot: "fv_Tree (tNot t) = fv_Tree t"
| fv_tPred: "fv_Tree (tPred \<phi>) = supp \<phi>"
| fv_tAct: "fv_Tree (tAct \<alpha> t) = (supp \<alpha> \<union> fv_Tree t) - bn \<alpha>"
-- \<open>352 subgoals (!)\<close>
by pat_completeness auto
termination proof
  let ?R = "inv_image (max_ext Tree_wf\<^sub>p <*lex*> less_bool_rel) alpha_Tree_termination"
  {
    show "wf ?R"
      by (metis max_ext_wf wf_Tree_wf\<^sub>p wf_inv_image wf_less_bool_rel wf_lex_prod)
  next
    fix t1 t2 and tset1 tset2 :: "('a, 'b, 'c) Tree set['a]"
    assume "t1 \<in> set_bset tset1" and "t2 \<in> set_bset tset2"
    then show "(Inl (t1, t2), Inl (tConj tset1, tConj tset2)) \<in> ?R"
      by (auto simp add: max_ext.simps Tree_wf.simps)
  next
    fix t1 t2 :: "('a, 'b, 'c) Tree"
    show "(Inl (t1, t2), Inl (tNot t1, tNot t2)) \<in> ?R"
      by (auto simp add: max_ext.simps Tree_wf.simps)
  next
    fix \<alpha>1 \<alpha>2 :: 'c and t1 t2 :: "('a, 'b, 'c) Tree" and p
    show "(Inl (p \<bullet> t1, t2), Inl (tAct \<alpha>1 t1, tAct \<alpha>2 t2)) \<in> ?R"
      by (auto simp add: max_ext.simps Tree_wf.simps)
  next
    fix \<alpha>1 \<alpha>2 :: 'c and t1 t2 :: "('a, 'b, 'c) Tree"
    show "(Inr t1, Inl (tAct \<alpha>1 t1, tAct \<alpha>2 t2)) \<in> ?R"
      by (auto simp add: max_ext.simps Tree_wf.simps)
  next
    fix \<alpha>1 \<alpha>2 :: 'c and t1 t2 :: "('a, 'b, 'c) Tree"
    show "(Inr t2, Inl (tAct \<alpha>1 t1, tAct \<alpha>2 t2)) \<in> ?R"
      by (auto simp add: max_ext.simps Tree_wf.simps)
  next
    fix tset :: "('a, 'b, 'c) Tree set['a]" and a b
    show "(Inl ((a \<rightleftharpoons> b) \<bullet> tConj tset, tConj tset), Inr (tConj tset)) \<in> ?R"
      by (auto simp add: max_ext.simps Tree_wf.simps simp del: permute_Tree_tConj)
  next
    fix t :: "('a, 'b, 'c) Tree"
    show "(Inr t, Inr (tNot t)) \<in> ?R"
      by (auto simp add: max_ext.simps Tree_wf.simps)
  next
    fix \<alpha> :: 'c and t :: "('a, 'b, 'c) Tree"
    show "(Inr t, Inr (tAct \<alpha> t)) \<in> ?R"
      by (auto simp add: max_ext.simps Tree_wf.simps)
  }
qed

text \<open>We provide more descriptive case names for the automatically generated induction principle,
and specialize it to an induction rule for \<alpha>-equivalence.\<close>

lemmas alpha_Tree_fv_Tree_induct = alpha_Tree_fv_Tree.induct[case_names alpha_tConj alpha_tNot
  alpha_tPred alpha_tAct "alpha_other(1)" "alpha_other(2)" "alpha_other(3)" "alpha_other(4)"
  "alpha_other(5)" "alpha_other(6)" "alpha_other(7)" "alpha_other(8)" "alpha_other(9)"
  "alpha_other(10)" "alpha_other(11)" "alpha_other(12)" "alpha_other(13)" "alpha_other(14)"
  "alpha_other(15)" "alpha_other(16)" "alpha_other(17)" "alpha_other(18)" fv_tConj fv_tNot fv_tPred
  fv_tAct]

lemma alpha_Tree_induct[case_names tConj tNot tPred tAct, consumes 1]:
  assumes "t1 =\<^sub>\<alpha> t2"
  and "\<And>tset1 tset2. (\<And>a b. a \<in> set_bset tset1 \<Longrightarrow> b \<in> set_bset tset2 \<Longrightarrow> a =\<^sub>\<alpha> b \<Longrightarrow> P a b) \<Longrightarrow>
            rel_bset op =\<^sub>\<alpha> tset1 tset2 \<Longrightarrow> P (tConj tset1) (tConj tset2)"
  and "\<And>t1 t2. t1 =\<^sub>\<alpha> t2 \<Longrightarrow> P t1 t2 \<Longrightarrow> P (tNot t1) (tNot t2)"
  and "\<And>\<phi>. P (tPred \<phi>) (tPred \<phi>)"
  and "\<And>\<alpha>1 t1 \<alpha>2 t2. (\<And>p. p \<bullet> t1 =\<^sub>\<alpha> t2 \<Longrightarrow> P (p \<bullet> t1) t2) \<Longrightarrow>
            (\<exists>p. (bn \<alpha>1, t1) \<approx>set (op =\<^sub>\<alpha>) fv_Tree p (bn \<alpha>2, t2) \<and> (bn \<alpha>1, \<alpha>1) \<approx>set (op =) supp p (bn \<alpha>2, \<alpha>2)) \<Longrightarrow>
            P (tAct \<alpha>1 t1) (tAct \<alpha>2 t2)"
  shows "P t1 t2"
using assms by (induction t1 t2 rule: alpha_Tree_fv_Tree_induct(1)[where Q="\<lambda>x. True"]) simp_all

text \<open>\<alpha>-equivalence and the free-variables function are equivariant.\<close>

lemma
  fixes t1 t2 t :: "('a,'b::pt,'c::bn) Tree"
  shows alpha_Tree_eqvt': "t1 =\<^sub>\<alpha> t2 \<longleftrightarrow> p \<bullet> t1 =\<^sub>\<alpha> p \<bullet> t2"
  and fv_Tree_eqvt [eqvt]: "p \<bullet> fv_Tree t = fv_Tree (p \<bullet> t)"
proof (induction t1 t2 and t rule: alpha_Tree_fv_Tree_induct)
  case alpha_tConj then show ?case
apply simp
apply transfer
apply (rule iffI)
-- \<open> (1) \<close>
 apply (rule rel_setI)
  apply (subgoal_tac "-p \<bullet> x \<in> tset1")
   prefer 2
   apply (metis mem_permute_iff permute_minus_cancel(1))
  apply (drule rel_setD1)
   apply assumption
  apply clarify
  apply (rule_tac x="p \<bullet> y" in bexI)
   apply (metis permute_minus_cancel(1))
  apply (metis mem_permute_iff)
 apply (subgoal_tac "-p \<bullet> y \<in> tset2")
  prefer 2
  apply (metis mem_permute_iff permute_minus_cancel(1))
 apply (drule rel_setD2)
  apply assumption
 apply clarify
 apply (rule_tac x="p \<bullet> x" in bexI)
  apply (metis permute_minus_cancel(1))
 apply (metis mem_permute_iff)
-- \<open> (2) \<close>
apply (rule rel_setI)
 apply (subgoal_tac "p \<bullet> x \<in> p \<bullet> tset1")
  prefer 2
  apply (metis mem_permute_iff)
 apply (drule rel_setD1)
  apply assumption
 apply clarify
 apply (rule_tac x="-p \<bullet> y" in bexI)
  apply (metis (no_types, lifting) mem_permute_iff permute_minus_cancel(1))
 apply (metis mem_permute_iff permute_minus_cancel(1))
apply (subgoal_tac "p \<bullet> y \<in> p \<bullet> tset2")
 prefer 2
 apply (metis mem_permute_iff)
apply (drule rel_setD2)
 apply assumption
apply clarify
apply (rule_tac x="-p \<bullet> x" in bexI)
 apply (metis (no_types, lifting) mem_permute_iff permute_minus_cancel(1))
apply (metis mem_permute_iff permute_minus_cancel(1))
done
next
  case alpha_tAct then show ?case
apply auto
-- \<open> (1) \<close>
 apply (rule_tac x="p + pa - p" in exI)
 apply (simp add: alpha_set)
 apply clarsimp
 apply (rule conjI)
   apply (metis (no_types, hide_lams) Diff_eqvt bn_eqvt)
  apply (smt2 Diff_eqvt bn_eqvt fresh_star_permute_iff permute_minus_cancel(2) permute_perm_def supp_eqvt)
-- \<open> (2) \<close>
apply (rule_tac x="-p + pa + p" in exI)
apply (simp add: alpha_set)
apply clarsimp
apply (rule conjI)
 apply (metis Diff_eqvt bn_eqvt permute_eq_iff)
apply auto
          apply (metis (erased, hide_lams) Diff_eqvt bn_eqvt diff_add_cancel diff_conv_add_uminus fresh_star_permute_iff permute_minus_cancel(1) permute_perm_def)
         apply (metis (erased, hide_lams) permute_eqvt permute_minus_cancel(1))
        apply (metis bn_eqvt permute_minus_cancel(2))
       apply (metis bn_eqvt permute_minus_cancel(2))
      apply (metis (no_types) Diff_eqvt Diff_iff bn_eqvt permute_minus_cancel(2) supp_eqvt)
     apply (metis (no_types) Diff_eqvt Diff_iff bn_eqvt permute_minus_cancel(2) supp_eqvt)
    apply (metis (no_types) Diff_eqvt Diff_iff bn_eqvt permute_minus_cancel(2) supp_eqvt)
   apply (metis (no_types) Diff_eqvt Diff_iff bn_eqvt permute_minus_cancel(2) supp_eqvt)
  apply (metis (erased, hide_lams) Diff_eqvt bn_eqvt diff_minus_eq_add fresh_star_permute_iff permute_minus_cancel(2) permute_perm_def supp_eqvt)
 apply (metis bn_eqvt permute_minus_cancel(2))
apply (metis bn_eqvt permute_minus_cancel(2))
done
next
  case (fv_tConj tset) then show ?case
apply (simp add: Supp_def)
apply (subgoal_tac "\<And>a. infinite {b. \<not> rel_bset op =\<^sub>\<alpha> ((a \<rightleftharpoons> b) \<bullet> tset) tset} = infinite {b. \<not> rel_bset op =\<^sub>\<alpha> (((p \<bullet> a) \<rightleftharpoons> b) \<bullet> p \<bullet> tset) (p \<bullet> tset)}")
 apply (auto simp add: permute_set_def)[1]
 apply (metis eqvt_bound)
apply auto
 apply (rule inj_on_finite[where f="unpermute p"])
   prefer 3 apply assumption
  apply (metis (no_types, lifting) inj_on_def permute_eq_iff unpermute_def)
 apply auto[1]
 apply (metis (erased, lifting) eqvt_bound permute_eqvt swap_eqvt)
apply (rule inj_on_finite[where f="permute p"])
  prefer 3 apply assumption
 apply (metis (no_types, lifting) inj_on_def permute_eq_iff)
apply auto
apply (metis permute_eqvt swap_eqvt)
done
next
  case fv_tAct then show ?case
    by (simp add: bn_eqvt Diff_eqvt union_eqvt)
qed simp_all

lemma alpha_Tree_eqvt [eqvt]: "t1 =\<^sub>\<alpha> t2 \<Longrightarrow> p \<bullet> t1 =\<^sub>\<alpha> p \<bullet> t2"
by (metis alpha_Tree_eqvt')

text \<open>@{const alpha_Tree} is an equivalence relation.\<close>

lemma alpha_Tree_reflp: "reflp alpha_Tree"
proof (rule reflpI)
  fix t :: "('a,'b,'c) Tree"
  show "t =\<^sub>\<alpha> t"
  proof (induction t)
    case tConj then show ?case by (metis alpha_tConj rel_bset.rep_eq rel_setI)
  next
    case tNot then show ?case by (metis alpha_tNot)
  next
    case tPred show ?case by (metis alpha_tPred)
  next
    case tAct then show ?case by (metis (mono_tags) alpha_tAct alpha_refl(1))
  qed
qed

lemma alpha_Tree_symp: "symp alpha_Tree"
proof (rule sympI)
  fix x y :: "('a,'b,'c) Tree"
  assume "x =\<^sub>\<alpha> y" then show "y =\<^sub>\<alpha> x"
  proof (induction x y rule: alpha_Tree_induct)
    case tConj then show ?case
      by (simp add: rel_bset_def rel_set_def) metis
  next
    case tAct then show ?case
apply auto
apply (rule_tac x="- p" in exI)
apply (simp add: alpha_set)
apply clarsimp
apply (rule conjI)
 apply (metis fresh_minus_perm fresh_star_def)
apply (rule conjI)
 apply (metis alpha_Tree_eqvt permute_minus_cancel(1))
apply (metis fresh_minus_perm fresh_star_def permute_minus_cancel(2))
done
  qed simp_all
qed

lemma alpha_Tree_transp: "transp alpha_Tree"
proof (rule transpI)
  fix x y z:: "('a,'b,'c) Tree"
  assume "x =\<^sub>\<alpha> y" and "y =\<^sub>\<alpha> z"
  then show "x =\<^sub>\<alpha> z"
  proof (induction x y arbitrary: z rule: alpha_Tree_induct)
    case tConj then show ?case
apply (cases z) apply simp_all
apply (simp add: rel_bset_def rel_set_def)
apply metis
done
  next
    case tNot then show ?case
      by (cases z) simp_all
  next
    case tPred then show ?case
      by simp
  next
    case tAct then show ?case
apply (cases z) apply auto
apply (rule_tac x="pa + p" in exI)
apply (simp add: alpha_set)
apply clarsimp
apply (rule conjI)
 apply (metis fresh_star_plus)
apply (metis (erased, hide_lams) alpha_Tree_eqvt' fresh_star_plus permute_minus_cancel(1))
done
  qed
qed

lemma alpha_Tree_equivp: "equivp alpha_Tree"
by (auto intro: equivpI alpha_Tree_reflp alpha_Tree_symp alpha_Tree_transp)

text \<open>\<alpha>-equivalent trees have the same set of free variables.\<close>

lemma alpha_Tree_fv_Tree:
  assumes "t1 =\<^sub>\<alpha> t2"
  shows "fv_Tree t1 = fv_Tree t2"
using assms proof (induction rule: alpha_Tree_induct)
  case (tConj tset1 tset2) then show ?case
apply simp
apply (subst Supp_def)
apply (subst Supp_def)
apply simp
apply (subgoal_tac "\<And>a b. rel_bset op =\<^sub>\<alpha> ((a \<rightleftharpoons> b) \<bullet> tset1) tset1 \<longleftrightarrow> rel_bset op =\<^sub>\<alpha> ((a \<rightleftharpoons> b) \<bullet> tset2) tset2")
 apply simp
apply (subgoal_tac "rel_bset op =\<^sub>\<alpha> ((a \<rightleftharpoons> b) \<bullet> tset1) ((a \<rightleftharpoons> b) \<bullet> tset2)")
 prefer 2
 apply (metis Formula.alpha_tConj alpha_Tree_eqvt permute_Tree_tConj)
apply (subgoal_tac "rel_bset op =\<^sub>\<alpha> ((a \<rightleftharpoons> b) \<bullet> tset2) ((a \<rightleftharpoons> b) \<bullet> tset1)")
 prefer 2
 apply (metis rel_bset_symp alpha_Tree_symp sympE)
apply (rule iffI)
 apply (metis rel_bset_transp alpha_Tree_transp transpE)
apply (subgoal_tac "rel_bset op =\<^sub>\<alpha> tset2 tset1")
 prefer 2
 apply (metis rel_bset_symp alpha_Tree_symp sympE)
apply (metis rel_bset_transp alpha_Tree_transp transpE)
done
next
  case tAct then show ?case
   by (clarsimp simp add: alphas alphas_abs) (metis Un_Diff)
qed simp_all

text \<open>@{const tAct} preserves \<alpha>-equivalence.\<close>

lemma alpha_Tree_tAct:
  assumes "t1 =\<^sub>\<alpha> t2"
  shows "tAct \<alpha> t1 =\<^sub>\<alpha> tAct \<alpha> t2"
proof (simp)
  have "(bn \<alpha>, t1) \<approx>set (op =\<^sub>\<alpha>) fv_Tree 0 (bn \<alpha>, t2)" (is "?P 0")
    using assms by (simp add: alpha_Tree_fv_Tree alphas(1) fresh_star_zero)
  moreover have "(bn \<alpha>, \<alpha>) \<approx>set (op =) supp 0 (bn \<alpha>, \<alpha>)" (is "?Q 0")
    by (metis (full_types) alpha_refl(1))
  ultimately show "\<exists>p. ?P p \<and> ?Q p"
    by auto
qed

text \<open>We define the type of (infinitely branching) trees quotiented by \<alpha>-equivalence.\<close>

(* FIXME: No map function defined. No relator found. *)
quotient_type
  ('idx,'pred,'act) Tree\<^sub>\<alpha> = "('idx,'pred\<Colon>pt,'act\<Colon>bn) Tree" / "alpha_Tree"
  by (fact alpha_Tree_equivp)

lemma Tree\<^sub>\<alpha>_abs_rep [simp]: "abs_Tree\<^sub>\<alpha> (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>) = t\<^sub>\<alpha>"
by (metis Quotient_Tree\<^sub>\<alpha> Quotient_abs_rep)

lemma Tree\<^sub>\<alpha>_rep_abs [simp]: "rep_Tree\<^sub>\<alpha> (abs_Tree\<^sub>\<alpha> t) =\<^sub>\<alpha> t"
by (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)

text \<open>The permutation operation is lifted from trees.\<close>

instantiation Tree\<^sub>\<alpha> :: (type, pt, bn) pt
begin

  lift_definition permute_Tree\<^sub>\<alpha> :: "perm \<Rightarrow> ('a,'b,'c) Tree\<^sub>\<alpha> \<Rightarrow> ('a,'b,'c) Tree\<^sub>\<alpha>"
    is permute
  by (fact alpha_Tree_eqvt)

  instance
  proof
    fix t\<^sub>\<alpha> :: "(_,_,_) Tree\<^sub>\<alpha>"
    show "0 \<bullet> t\<^sub>\<alpha> = t\<^sub>\<alpha>"
      by transfer (metis alpha_Tree_equivp equivp_reflp permute_zero)
  next
    fix p q :: perm and t\<^sub>\<alpha> :: "(_,_,_) Tree\<^sub>\<alpha>"
    show "(p + q) \<bullet> t\<^sub>\<alpha> = p \<bullet> q \<bullet> t\<^sub>\<alpha>"
      by transfer (metis alpha_Tree_equivp equivp_reflp permute_plus)
  qed

end

text \<open>The abstraction function from trees to trees modulo \<alpha>-equivalence is equivariant. The
representation function is equivariant modulo \<alpha>-equivalence.\<close>

lemmas permute_Tree\<^sub>\<alpha>.abs_eq [eqvt, simp]

lemma alpha_Tree_permute_rep_commute [simp]: "p \<bullet> rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha> =\<^sub>\<alpha> rep_Tree\<^sub>\<alpha> (p \<bullet> t\<^sub>\<alpha>)"
by (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep permute_Tree\<^sub>\<alpha>.abs_eq)


subsection \<open>Constructors for trees modulo \<alpha>-equivalence\<close>

text \<open>The constructors are lifted from trees.\<close>

lift_definition Conj\<^sub>\<alpha> :: "('idx,'pred,'act) Tree\<^sub>\<alpha> set['idx] \<Rightarrow> ('idx,'pred\<Colon>pt,'act\<Colon>bn) Tree\<^sub>\<alpha>" is
  tConj
by simp

lemma map_bset_abs_rep_Tree\<^sub>\<alpha>: "map_bset abs_Tree\<^sub>\<alpha> (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>) = tset\<^sub>\<alpha>"
by (metis (full_types) Quotient_Tree\<^sub>\<alpha> Quotient_abs_rep bset_quot_map)

lemma Conj\<^sub>\<alpha>_def': "Conj\<^sub>\<alpha> tset\<^sub>\<alpha> = abs_Tree\<^sub>\<alpha> (tConj (map_bset rep_Tree\<^sub>\<alpha> tset\<^sub>\<alpha>))"
by (metis Conj\<^sub>\<alpha>.abs_eq map_bset_abs_rep_Tree\<^sub>\<alpha>)

lift_definition Not\<^sub>\<alpha> :: "('idx,'pred,'act) Tree\<^sub>\<alpha> \<Rightarrow> ('idx,'pred\<Colon>pt,'act\<Colon>bn) Tree\<^sub>\<alpha>" is
  tNot
by simp

lift_definition Pred\<^sub>\<alpha> :: "'pred \<Rightarrow> ('idx,'pred\<Colon>pt,'act\<Colon>bn) Tree\<^sub>\<alpha>" is
  tPred
.

lift_definition Act\<^sub>\<alpha> :: "'act \<Rightarrow> ('idx,'pred,'act) Tree\<^sub>\<alpha> \<Rightarrow> ('idx,'pred\<Colon>pt,'act\<Colon>bn) Tree\<^sub>\<alpha>" is
  tAct
by (fact alpha_Tree_tAct)

text \<open>The lifted constructors are equivariant.\<close>

lemma Conj\<^sub>\<alpha>_eqvt [eqvt, simp]: "p \<bullet> Conj\<^sub>\<alpha> tset\<^sub>\<alpha> = Conj\<^sub>\<alpha> (p \<bullet> tset\<^sub>\<alpha>)"
unfolding Conj\<^sub>\<alpha>_def'
apply (simp add: Tree\<^sub>\<alpha>.abs_eq_iff)
apply transfer
apply (auto simp add: rel_set_def)
 apply (rule_tac x="abs_Tree\<^sub>\<alpha> x" in bexI)
  apply (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)
 apply (auto simp add: image_def permute_set_def)[1]
 apply (rename_tac t\<^sub>\<alpha>)
 apply (rule_tac x=t\<^sub>\<alpha> in exI)
 apply (metis Tree\<^sub>\<alpha>_abs_rep permute_Tree\<^sub>\<alpha>.abs_eq)
apply (rename_tac t\<^sub>\<alpha>)
apply (rule_tac x="p \<bullet> rep_Tree\<^sub>\<alpha> (-p \<bullet> t\<^sub>\<alpha>)" in bexI)
 apply (metis alpha_Tree_permute_rep_commute permute_minus_cancel(1))
apply (auto simp add: image_def permute_set_def)
done

lemma Not\<^sub>\<alpha>_eqvt [eqvt, simp]: "p \<bullet> Not\<^sub>\<alpha> t\<^sub>\<alpha> = Not\<^sub>\<alpha> (p \<bullet> t\<^sub>\<alpha>)"
by (induct t\<^sub>\<alpha>) (simp add: Not\<^sub>\<alpha>.abs_eq)

lemma Pred\<^sub>\<alpha>_eqvt [eqvt, simp]: "p \<bullet> Pred\<^sub>\<alpha> \<phi> = Pred\<^sub>\<alpha> (p \<bullet> \<phi>)"
by (simp add: Pred\<^sub>\<alpha>.abs_eq)

lemma Act\<^sub>\<alpha>_eqvt [eqvt, simp]: "p \<bullet> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> (p \<bullet> \<alpha>) (p \<bullet> t\<^sub>\<alpha>)"
by (induct t\<^sub>\<alpha>) (simp add: Act\<^sub>\<alpha>.abs_eq)

text \<open>The lifted constructors are injective (except for~@{const Act\<^sub>\<alpha>}).\<close>

lemma Conj\<^sub>\<alpha>_eq_iff [simp]: "Conj\<^sub>\<alpha> tset1\<^sub>\<alpha> = Conj\<^sub>\<alpha> tset2\<^sub>\<alpha> \<longleftrightarrow> tset1\<^sub>\<alpha> = tset2\<^sub>\<alpha>"
proof
  assume "Conj\<^sub>\<alpha> tset1\<^sub>\<alpha> = Conj\<^sub>\<alpha> tset2\<^sub>\<alpha>"
  then have "tConj (map_bset rep_Tree\<^sub>\<alpha> tset1\<^sub>\<alpha>) =\<^sub>\<alpha> tConj (map_bset rep_Tree\<^sub>\<alpha> tset2\<^sub>\<alpha>)"
    by (metis Conj\<^sub>\<alpha>_def' Tree\<^sub>\<alpha>.abs_eq_iff)
  then have "rel_bset alpha_Tree (map_bset rep_Tree\<^sub>\<alpha> tset1\<^sub>\<alpha>) (map_bset rep_Tree\<^sub>\<alpha> tset2\<^sub>\<alpha>)"
    by (auto elim: alpha_Tree.cases)
  then show "tset1\<^sub>\<alpha> = tset2\<^sub>\<alpha>"
apply transfer
apply (auto simp add: rel_set_def image_def)
 apply (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)
apply (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)
done
next
  assume "tset1\<^sub>\<alpha> = tset2\<^sub>\<alpha>" then show "Conj\<^sub>\<alpha> tset1\<^sub>\<alpha> = Conj\<^sub>\<alpha> tset2\<^sub>\<alpha>"
    by simp
qed

lemma Not\<^sub>\<alpha>_eq_iff [simp]: "Not\<^sub>\<alpha> t1\<^sub>\<alpha> = Not\<^sub>\<alpha> t2\<^sub>\<alpha> \<longleftrightarrow> t1\<^sub>\<alpha> = t2\<^sub>\<alpha>"
proof
  assume "Not\<^sub>\<alpha> t1\<^sub>\<alpha> = Not\<^sub>\<alpha> t2\<^sub>\<alpha>"
  then have "tNot (rep_Tree\<^sub>\<alpha> t1\<^sub>\<alpha>) =\<^sub>\<alpha> tNot (rep_Tree\<^sub>\<alpha> t2\<^sub>\<alpha>)"
    by (metis Not\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)
  then have "rep_Tree\<^sub>\<alpha> t1\<^sub>\<alpha> =\<^sub>\<alpha> rep_Tree\<^sub>\<alpha> t2\<^sub>\<alpha>"
    using alpha_Tree.cases by auto
  then show "t1\<^sub>\<alpha> = t2\<^sub>\<alpha>"
    by (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)
next
  assume "t1\<^sub>\<alpha> = t2\<^sub>\<alpha>" then show "Not\<^sub>\<alpha> t1\<^sub>\<alpha> = Not\<^sub>\<alpha> t2\<^sub>\<alpha>"
    by simp
qed

lemma Pred\<^sub>\<alpha>_eq_iff [simp]: "Pred\<^sub>\<alpha> \<phi>1 = Pred\<^sub>\<alpha> \<phi>2 \<longleftrightarrow> \<phi>1 = \<phi>2"
proof
  assume "Pred\<^sub>\<alpha> \<phi>1 = Pred\<^sub>\<alpha> \<phi>2"
  then have "(tPred \<phi>1 :: ('d, 'b, 'e) Tree) =\<^sub>\<alpha> tPred \<phi>2"  -- \<open>note the unrelated type\<close>
    by (metis Pred\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff)
  then show "\<phi>1 = \<phi>2"
    using alpha_Tree.cases by auto
next
  assume "\<phi>1 = \<phi>2" then show "Pred\<^sub>\<alpha> \<phi>1 = Pred\<^sub>\<alpha> \<phi>2"
    by simp
qed

text \<open>The lifted constructors are quasi-free.\<close>

lemma Tree\<^sub>\<alpha>_free [simp]:
  shows "Conj\<^sub>\<alpha> tset\<^sub>\<alpha> \<noteq> Not\<^sub>\<alpha> t\<^sub>\<alpha>"
  and "Conj\<^sub>\<alpha> tset\<^sub>\<alpha> \<noteq> Pred\<^sub>\<alpha> \<phi>"
  and "Conj\<^sub>\<alpha> tset\<^sub>\<alpha> \<noteq> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>"
  and "Not\<^sub>\<alpha> t\<^sub>\<alpha> \<noteq> Pred\<^sub>\<alpha> \<phi>"
  and "Not\<^sub>\<alpha> t1\<^sub>\<alpha> \<noteq> Act\<^sub>\<alpha> \<alpha> t2\<^sub>\<alpha>"
  and "Pred\<^sub>\<alpha> \<phi> \<noteq> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>"
apply auto
     apply (metis Conj\<^sub>\<alpha>_def' Not\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep alpha_Tree.simps(5))
    apply (metis Conj\<^sub>\<alpha>_def' Pred\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff alpha_Tree.simps(17))
   apply (metis Conj\<^sub>\<alpha>_def' Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep alpha_Tree.simps(11))
  apply (metis Not\<^sub>\<alpha>.abs_eq Pred\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep alpha_Tree.simps(6))
 apply (metis Act\<^sub>\<alpha>_def Not\<^sub>\<alpha>_def Tree\<^sub>\<alpha>.abs_eq_iff alpha_Tree.simps(7) map_fun_apply)
apply (metis Act\<^sub>\<alpha>.abs_eq Pred\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep alpha_Tree.simps(10))
done

text \<open>The following lemmas describe the support of constructed trees modulo \<alpha>-equivalence.
For~@{term "Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>"}, we merely prove that it is finitely supported, provided~@{term t\<^sub>\<alpha>} has
finite support.\<close>

lemma supp_Conj\<^sub>\<alpha> [simp]: "supp (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>) = supp tset\<^sub>\<alpha>"
unfolding supp_def by simp

lemma supp_Not\<^sub>\<alpha> [simp]: "supp (Not\<^sub>\<alpha> t\<^sub>\<alpha>) = supp t\<^sub>\<alpha>"
unfolding supp_def by simp

lemma supp_Pred\<^sub>\<alpha> [simp]: "supp (Pred\<^sub>\<alpha> \<phi>) = supp \<phi>"
unfolding supp_def by simp

lemma finite_supp_implies_finite_supp_Act\<^sub>\<alpha> [simp]:
  assumes "finite (supp t\<^sub>\<alpha>)"
  shows "finite (supp (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>))"
proof -
  have "(supp t\<^sub>\<alpha> \<union> supp \<alpha>) supports Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>"
    unfolding supports_def by simp (metis fresh_def swap_fresh_fresh)
  then show ?thesis
    using assms by (metis finite_UnI finite_supp supports_finite)
qed


subsection \<open>Induction over trees modulo \<alpha>-equivalence\<close>

lemma Tree\<^sub>\<alpha>_induct [case_names Conj\<^sub>\<alpha> Not\<^sub>\<alpha> Pred\<^sub>\<alpha> Act\<^sub>\<alpha> Env\<^sub>\<alpha>, induct type: Tree\<^sub>\<alpha>]:
  fixes t\<^sub>\<alpha>
  assumes "\<And>tset\<^sub>\<alpha>. (\<And>x. x \<in> set_bset tset\<^sub>\<alpha> \<Longrightarrow> P x) \<Longrightarrow> P (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>)"
    and "\<And>t\<^sub>\<alpha>. P t\<^sub>\<alpha> \<Longrightarrow> P (Not\<^sub>\<alpha> t\<^sub>\<alpha>)"
    and "\<And>pred. P (Pred\<^sub>\<alpha> pred)"
    and "\<And>act t\<^sub>\<alpha>. P t\<^sub>\<alpha> \<Longrightarrow> P (Act\<^sub>\<alpha> act t\<^sub>\<alpha>)"
  shows "P t\<^sub>\<alpha>"
proof (rule Tree\<^sub>\<alpha>.abs_induct)
  fix t show "P (abs_Tree\<^sub>\<alpha> t)"
    proof (induction t)
      case (tConj tset) then show ?case
        using assms(1)
apply (simp add: Conj\<^sub>\<alpha>_def')
apply (drule_tac x="map_bset abs_Tree\<^sub>\<alpha> tset" in meta_spec)
apply (subgoal_tac "abs_Tree\<^sub>\<alpha> (tConj (map_bset rep_Tree\<^sub>\<alpha> (map_bset abs_Tree\<^sub>\<alpha> tset))) = abs_Tree\<^sub>\<alpha> (tConj tset)")
 prefer 2
 apply (metis Conj\<^sub>\<alpha>.abs_eq Conj\<^sub>\<alpha>_def')
apply (auto simp add: bset.set_map)
done
    next
      case tNot then show ?case
        using assms(2) by (metis Not\<^sub>\<alpha>.abs_eq)
    next
      case tPred show ?case
        using assms(3) by (metis Pred\<^sub>\<alpha>.abs_eq)
    next
      case tAct then show ?case
        using assms(4) by (metis Act\<^sub>\<alpha>.abs_eq)
    qed
qed

text \<open>There is no (obvious) strong induction principle for trees modulo \<alpha>-equivalence: since their
support may be infinite, we may not be able to rename bound variables without also renaming free
variables.\<close>


subsection \<open>Hereditarily finitely supported trees\<close>

text \<open>We cannot obtain the type of infinitary formulae simply as the sub-type of all trees (modulo
\<alpha>-equivalence) that are finitely supported: since an infinite set of trees may be finitely supported
even though its members are not (and thus, would not be formulae), the sub-type of \emph{all}
finitely supported trees does not validate the induction principle that we desire for formulae.

Instead, we define \emph{hereditarily} finitely supported trees. We require that environments and
state predicates are finitely supported.\<close>

inductive hereditarily_fs :: "('idx,'pred\<Colon>fs,'act\<Colon>bn) Tree\<^sub>\<alpha> \<Rightarrow> bool" where
  Conj\<^sub>\<alpha>: "finite (supp tset\<^sub>\<alpha>) \<Longrightarrow> (\<And>t\<^sub>\<alpha>. t\<^sub>\<alpha> \<in> set_bset tset\<^sub>\<alpha> \<Longrightarrow> hereditarily_fs t\<^sub>\<alpha>) \<Longrightarrow> hereditarily_fs (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>)"
| Not\<^sub>\<alpha>: "hereditarily_fs t\<^sub>\<alpha> \<Longrightarrow> hereditarily_fs (Not\<^sub>\<alpha> t\<^sub>\<alpha>)"
| Pred\<^sub>\<alpha>: "hereditarily_fs (Pred\<^sub>\<alpha> \<phi>)"
| Act\<^sub>\<alpha>: "hereditarily_fs t\<^sub>\<alpha> \<Longrightarrow> hereditarily_fs (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>)"

text \<open>@{const hereditarily_fs} is equivariant.\<close>

lemma hereditarily_fs_eqvt [eqvt]:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "hereditarily_fs (p \<bullet> t\<^sub>\<alpha>)"
using assms proof (induction rule: hereditarily_fs.induct)
  case Conj\<^sub>\<alpha> then show ?case
    by (metis (erased, hide_lams) Conj\<^sub>\<alpha>_eqvt hereditarily_fs.Conj\<^sub>\<alpha> mem_permute_iff permute_finite permute_minus_cancel(1) set_bset_eqvt supp_eqvt)
next
  case Not\<^sub>\<alpha> then show ?case
    by (metis Not\<^sub>\<alpha>_eqvt hereditarily_fs.Not\<^sub>\<alpha>)
next
  case Pred\<^sub>\<alpha> then show ?case
    by (metis Pred\<^sub>\<alpha>_eqvt hereditarily_fs.Pred\<^sub>\<alpha>)
next
  case Act\<^sub>\<alpha> then show ?case
    by (metis Act\<^sub>\<alpha>_eqvt hereditarily_fs.Act\<^sub>\<alpha>)
qed

text \<open>@{const hereditarily_fs} is preserved under \<alpha>-renaming.\<close>

lemma hereditarily_fs_alpha_renaming:
  assumes "Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> = Act\<^sub>\<alpha> \<alpha>' t\<^sub>\<alpha>'"
  shows "hereditarily_fs t\<^sub>\<alpha> \<longleftrightarrow> hereditarily_fs t\<^sub>\<alpha>'"
using assms
apply (auto simp add: Act\<^sub>\<alpha>_def Tree\<^sub>\<alpha>.abs_eq_iff alphas)
 apply (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep hereditarily_fs_eqvt permute_Tree\<^sub>\<alpha>.abs_eq)
apply (metis Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep hereditarily_fs_eqvt permute_Tree\<^sub>\<alpha>.abs_eq permute_minus_cancel(2))
done

text \<open>Hereditarily finitely supported trees have finite support.\<close>

lemma hereditarily_fs_implies_finite_supp:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "finite (supp t\<^sub>\<alpha>)"
using assms by (induction rule: hereditarily_fs.induct) (simp_all add: finite_supp)


subsection \<open>Infinitary formulae\<close>

text \<open>Now, infinitary formulae are simply the sub-type of hereditarily finitely supported trees.\<close>

typedef ('idx,'pred::fs,'act::bn) formula = "{t\<^sub>\<alpha>::('idx,'pred,'act) Tree\<^sub>\<alpha>. hereditarily_fs t\<^sub>\<alpha>}"
by (metis hereditarily_fs.Pred\<^sub>\<alpha> mem_Collect_eq)

text \<open>We set up Isabelle's lifting infrastructure so that we can lift definitions from the type of
trees modulo \<alpha>-equivalence to the sub-type of formulas.\<close>

(* FIXME: No relator found. *)
setup_lifting type_definition_formula

lemma Abs_formula_inverse [simp]:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "Rep_formula (Abs_formula t\<^sub>\<alpha>) = t\<^sub>\<alpha>"
using assms by (metis Abs_formula_inverse mem_Collect_eq)

lemma Rep_formula' [simp]: "hereditarily_fs (Rep_formula x)"
by (metis Rep_formula mem_Collect_eq)

text \<open>Now we lift the permutation operation.\<close>

instantiation formula :: (type, fs, bn) pt
begin

  lift_definition permute_formula :: "perm \<Rightarrow> ('a,'b,'c) formula \<Rightarrow> ('a,'b,'c) formula"
    is permute
  by (fact hereditarily_fs_eqvt)

  instance
  by default (transfer, simp)+

end

text \<open>The abstraction and representation functions for formulae are equivariant, and they preserve
support.\<close>

lemma Abs_formula_eqvt [simp]:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "p \<bullet> Abs_formula t\<^sub>\<alpha> = Abs_formula (p \<bullet> t\<^sub>\<alpha>)"
by (metis assms eq_onp_same_args permute_formula.abs_eq)

lemma supp_Abs_formula [simp]:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "supp (Abs_formula t\<^sub>\<alpha>) = supp t\<^sub>\<alpha>"
proof -
  {
    fix p :: perm
    have "p \<bullet> Abs_formula t\<^sub>\<alpha> = Abs_formula (p \<bullet> t\<^sub>\<alpha>)"
      using assms by (metis Abs_formula_eqvt)
    moreover have "hereditarily_fs (p \<bullet> t\<^sub>\<alpha>)"
      using assms by (metis hereditarily_fs_eqvt)
    ultimately have "p \<bullet> Abs_formula t\<^sub>\<alpha> = Abs_formula t\<^sub>\<alpha> \<longleftrightarrow> p \<bullet> t\<^sub>\<alpha> = t\<^sub>\<alpha>"
      using assms by (metis Abs_formula_inverse)
  }
  then show ?thesis unfolding supp_def by simp
qed

lemmas Rep_formula_eqvt [eqvt, simp] = permute_formula.rep_eq[symmetric]

lemma supp_Rep_formula [simp]: "supp (Rep_formula x) = supp x"
by (metis Rep_formula' Rep_formula_inverse supp_Abs_formula)

lemma supp_map_bset_Rep_formula [simp]: "supp (map_bset Rep_formula xset) = supp xset"
proof
  have "eqvt (map_bset Rep_formula)"
    unfolding eqvt_def by (simp add: ext)
  then show "supp (map_bset Rep_formula xset) \<subseteq> supp xset"
    by (fact supp_fun_app_eqvt)
next
  {
    fix a :: atom
    have "inj (map_bset Rep_formula)"
      by (metis inj_map_bset Rep_formula_inject injI)
    then have "\<And>x y. x \<noteq> y \<Longrightarrow> map_bset Rep_formula x \<noteq> map_bset Rep_formula y"
      by (metis inj_eq)
    then have "{b. (a \<rightleftharpoons> b) \<bullet> xset \<noteq> xset} \<subseteq> {b. (a \<rightleftharpoons> b) \<bullet> map_bset Rep_formula xset \<noteq> map_bset Rep_formula xset}" (is "?S \<subseteq> ?T")
      by auto
    then have "infinite ?S \<Longrightarrow> infinite ?T"
      by (metis infinite_super)
  }
  then show "supp xset \<subseteq> supp (map_bset Rep_formula xset)"
    unfolding supp_def by auto
qed

text \<open>Formulae are in fact finitely supported.\<close>

instance formula :: (type, fs, bn) fs
by default (metis Rep_formula' hereditarily_fs_implies_finite_supp supp_Rep_formula)


subsection \<open>Constructors for infinitary formulae\<close>

text \<open>We lift the constructors for trees (modulo \<alpha>-equivalence) to infinitary formulae.
Since~@{const Conj\<^sub>\<alpha>} does not necessarily yield a (hereditarily) finitely supported tree when
applied to a (potentially infinite) set of (hereditarily) finitely supported trees, we cannot use
Isabelle's {\bf lift\_definition} to define~@{term Conj}. Instead, theorems about terms of the
form~@{term "Conj xset"} will usually carry an assumption that~@{term xset} is finitely supported.\<close>

definition Conj :: "('idx,'pred,'act) formula set['idx] \<Rightarrow> ('idx,'pred\<Colon>fs,'act\<Colon>bn) formula" where
  "Conj xset = Abs_formula (Conj\<^sub>\<alpha> (map_bset Rep_formula xset))"

lemma finite_supp_implies_hereditarily_fs_Conj\<^sub>\<alpha> [simp]:
  assumes "finite (supp xset)"
  shows "hereditarily_fs (Conj\<^sub>\<alpha> (map_bset Rep_formula xset))"
proof (rule hereditarily_fs.Conj\<^sub>\<alpha>)
  show "finite (supp (map_bset Rep_formula xset))"
    using assms by (metis supp_map_bset_Rep_formula)
next
  fix t\<^sub>\<alpha> assume "t\<^sub>\<alpha> \<in> set_bset (map_bset Rep_formula xset)"
  then show "hereditarily_fs t\<^sub>\<alpha>"
    by (auto simp add: bset.set_map)
qed

lemma Conj_rep_eq:
  assumes "finite (supp xset)"
  shows "Rep_formula (Conj xset) = Conj\<^sub>\<alpha> (map_bset Rep_formula xset)"
using assms unfolding Conj_def by simp

lift_definition Not :: "('idx,'pred,'act) formula \<Rightarrow> ('idx,'pred\<Colon>fs,'act\<Colon>bn) formula" is
  Not\<^sub>\<alpha>
by (fact hereditarily_fs.Not\<^sub>\<alpha>)

lift_definition Pred :: "'pred \<Rightarrow> ('idx,'pred\<Colon>fs,'act\<Colon>bn) formula" is
  Pred\<^sub>\<alpha>
by (fact hereditarily_fs.Pred\<^sub>\<alpha>)

lift_definition Act :: "'act \<Rightarrow> ('idx,'pred,'act) formula \<Rightarrow> ('idx,'pred\<Colon>fs,'act\<Colon>bn) formula" is
  Act\<^sub>\<alpha>
by (fact hereditarily_fs.Act\<^sub>\<alpha>)

text \<open>The lifted constructors are equivariant (in the case of~@{const Conj}, on finitely supported
arguments).\<close>

lemma Conj_eqvt [simp]:
  assumes "finite (supp xset)"
  shows "p \<bullet> Conj xset = Conj (p \<bullet> xset)"
using assms unfolding Conj_def by simp

lemma Not_eqvt [eqvt, simp]: "p \<bullet> Not x = Not (p \<bullet> x)"
by transfer simp

lemma Pred_eqvt [eqvt, simp]: "p \<bullet> Pred \<phi> = Pred (p \<bullet> \<phi>)"
by transfer simp

lemma Act_eqvt [eqvt, simp]: "p \<bullet> Act \<alpha> x = Act (p \<bullet> \<alpha>) (p \<bullet> x)"
by transfer simp

text \<open>The following lemmas describe the support of constructed formulae.\<close>

lemma supp_Conj [simp]:
  assumes "finite (supp xset)"
  shows "supp (Conj xset) = supp xset"
using assms unfolding Conj_def by simp

lemma supp_Not [simp]: "supp (Not x) = supp x"
by (metis Not.rep_eq supp_Not\<^sub>\<alpha> supp_Rep_formula)

lemma supp_Pred [simp]: "supp (Pred \<phi>) = supp \<phi>"
by (metis Pred.rep_eq supp_Pred\<^sub>\<alpha> supp_Rep_formula)

text \<open>The lifted constructors are injective (except for @{const Act}).\<close>

lemma Conj_eq_iff [simp]:
  assumes "finite (supp xset1)" and "finite (supp xset2)"
  shows "Conj xset1 = Conj xset2 \<longleftrightarrow> xset1 = xset2"
using assms
by (metis (erased, hide_lams) Conj\<^sub>\<alpha>_eq_iff Conj_rep_eq Rep_formula_inverse injI inj_eq inj_map_bset)

lemma Not_eq_iff [simp]: "Not x1 = Not x2 \<longleftrightarrow> x1 = x2"
by (metis Not.rep_eq Not\<^sub>\<alpha>_eq_iff Rep_formula_inverse)

lemma Pred_eq_iff [simp]: "Pred \<phi>1 = Pred \<phi>2 \<longleftrightarrow> \<phi>1 = \<phi>2"
by (metis Pred.rep_eq Pred\<^sub>\<alpha>_eq_iff)

text \<open>The lifted constructors are quasi-free.\<close>

lemma Tree_free [simp]:
  shows "finite (supp xset) \<Longrightarrow> Conj xset \<noteq> Not x"
  and "finite (supp xset) \<Longrightarrow> Conj xset \<noteq> Pred \<phi>"
  and "finite (supp xset) \<Longrightarrow> Conj xset \<noteq> Act \<alpha> x"
  and "Not x \<noteq> Pred \<phi>"
  and "Not x1 \<noteq> Act \<alpha> x2"
  and "Pred \<phi> \<noteq> Act \<alpha> x"
apply auto
     apply (metis Conj_rep_eq Not.rep_eq Tree\<^sub>\<alpha>_free(1))
    apply (metis Conj_rep_eq Pred.rep_eq Tree\<^sub>\<alpha>_free(2))
   apply (metis Conj_rep_eq Act.rep_eq Tree\<^sub>\<alpha>_free(3))
  apply (metis Not.rep_eq Pred.rep_eq Tree\<^sub>\<alpha>_free(4))
 apply (metis Not.rep_eq Act.rep_eq Tree\<^sub>\<alpha>_free(5))
apply (metis Pred.rep_eq Act.rep_eq Tree\<^sub>\<alpha>_free(6))
done


subsection \<open>Induction over infinitary formulae\<close>

lemma formula_induct [case_names Conj Not Pred Act, induct type: formula]:
  fixes x
  assumes "\<And>xset. finite (supp xset) \<Longrightarrow> (\<And>x. x \<in> set_bset xset \<Longrightarrow> P x) \<Longrightarrow> P (Conj xset)"
    and "\<And>formula. P formula \<Longrightarrow> P (Not formula)"
    and "\<And>pred. P (Pred pred)"
    and "\<And>act formula. P formula \<Longrightarrow> P (Act act formula)"
  shows "P x"
proof (induction x)
  fix t\<^sub>\<alpha> :: "('a,'b,'c) Tree\<^sub>\<alpha>"
  assume "t\<^sub>\<alpha> \<in> {t\<^sub>\<alpha>. hereditarily_fs t\<^sub>\<alpha>}"
  then have "hereditarily_fs t\<^sub>\<alpha>"
    by simp
  then show "P (Abs_formula t\<^sub>\<alpha>)"
    proof (induction t\<^sub>\<alpha>)
      case (Conj\<^sub>\<alpha> tset\<^sub>\<alpha>)
        then show ?case
          using assms(1)
apply (simp add: Conj_def)
apply (drule_tac x="map_bset Abs_formula tset\<^sub>\<alpha>" in meta_spec)
apply (subgoal_tac "map_bset Rep_formula (map_bset Abs_formula tset\<^sub>\<alpha>) = tset\<^sub>\<alpha>")
 apply simp
 apply (drule meta_mp)
  apply (metis supp_map_bset_Rep_formula)
 apply (erule meta_mp)
 apply (subgoal_tac "Rep_formula x \<in> set_bset tset\<^sub>\<alpha>")
  apply (metis Rep_formula_inverse)
 apply (auto simp add: bset.set_map)[1]
apply (simp add: bset.map_comp)
apply (subgoal_tac "set_bset (map_bset (Rep_formula \<circ> Abs_formula) tset\<^sub>\<alpha>) = set_bset tset\<^sub>\<alpha>")
 apply (metis set_bset_inject)
apply (auto simp add: bset.set_map image_def)
done
    next
      case Not\<^sub>\<alpha> then show ?case
        using assms(2) by (metis Formula.Abs_formula_inverse Not.rep_eq Rep_formula_inverse)
    next
      case Pred\<^sub>\<alpha> show ?case
        using assms(3) by (metis Pred.abs_eq)
    next
      case Act\<^sub>\<alpha> then show ?case
        using assms(4) by (metis Formula.Abs_formula_inverse Act.rep_eq Rep_formula_inverse)
    qed
qed


subsection \<open>Strong induction over infinitary formulae\<close>

text \<open>The following lemmas are needed to prove strong induction. Nonetheless, they should perhaps be
moved to earlier sections.\<close>

lemma supp_abs_Tree\<^sub>\<alpha>_eq_Supp_alpha_Tree: "supp (abs_Tree\<^sub>\<alpha> t) = Supp (op =\<^sub>\<alpha>) t"
by (simp add: Supp_def supp_def Tree\<^sub>\<alpha>.abs_eq_iff)

lemma Act_eq_iff: "Act \<alpha>1 x1 = Act \<alpha>2 x2 \<longleftrightarrow> Act\<^sub>\<alpha> \<alpha>1 (Rep_formula x1) = Act\<^sub>\<alpha> \<alpha>2 (Rep_formula x2)"
by (metis Act.rep_eq Rep_formula_inverse)

lemma Act\<^sub>\<alpha>_eq_iff: "Act\<^sub>\<alpha> \<alpha>1 t1 = Act\<^sub>\<alpha> \<alpha>2 t2 \<longleftrightarrow> tAct \<alpha>1 (rep_Tree\<^sub>\<alpha> t1) =\<^sub>\<alpha> tAct \<alpha>2 (rep_Tree\<^sub>\<alpha> t2)"
by (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep)

lemma infinite_mono: "infinite S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> x \<in> T) \<Longrightarrow> infinite T"
by (metis infinite_super subsetI)

lemma fv_Tree_rep_Tree\<^sub>\<alpha>_eq_supp:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "fv_Tree (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>) = supp t\<^sub>\<alpha>"
using assms proof (induction rule: hereditarily_fs.induct)
  case Conj\<^sub>\<alpha> then show ?case
    by (metis Conj\<^sub>\<alpha>_def' fv_tConj Tree\<^sub>\<alpha>_rep_abs alpha_Tree_fv_Tree supp_abs_Tree\<^sub>\<alpha>_eq_Supp_alpha_Tree)
next
  case Not\<^sub>\<alpha> then show ?case
    by (metis Not\<^sub>\<alpha>.abs_eq fv_tNot Tree\<^sub>\<alpha>_abs_rep Tree\<^sub>\<alpha>_rep_abs alpha_Tree_fv_Tree supp_Not\<^sub>\<alpha>)
next
  case Pred\<^sub>\<alpha> show ?case
    by (metis Pred\<^sub>\<alpha>.abs_eq fv_tPred Tree\<^sub>\<alpha>_rep_abs alpha_Tree_fv_Tree supp_Pred\<^sub>\<alpha>)
next
  case (Act\<^sub>\<alpha> t\<^sub>\<alpha> \<alpha>) then show ?case
apply (subgoal_tac "fv_Tree (rep_Tree\<^sub>\<alpha> (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>)) = fv_Tree (tAct \<alpha> (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>))")
 prefer 2
 apply (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep alpha_Tree_fv_Tree)
apply simp
apply (drule hereditarily_fs_implies_finite_supp)
apply auto
-- \<open>4 subgoals\<close>
   apply (subgoal_tac "infinite {b. (x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha>}")
    prefer 2
    apply (simp add: supp_def)
   apply (subgoal_tac "infinite ({b. (x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha>} - supp \<alpha>)")
    prefer 2
    apply (metis Diff_infinite_finite finite_supp)
   apply (thin_tac "infinite {b. (x \<rightleftharpoons> b) \<bullet> \<alpha> \<noteq> \<alpha>}")
   apply (subst supp_def)
   apply (rule CollectI)
   apply (erule infinite_mono)
   apply (rename_tac b)
   apply (clarsimp simp add: Act\<^sub>\<alpha>_eq_iff)
   apply (thin_tac "(bn ((x \<rightleftharpoons> b) \<bullet> \<alpha>), rep_Tree\<^sub>\<alpha> ((x \<rightleftharpoons> b) \<bullet> t\<^sub>\<alpha>)) \<approx>set op =\<^sub>\<alpha> fv_Tree p (bn \<alpha>, rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>)")
   apply (auto simp add: alphas_abs alphas)[1]
   apply (smt2 Diff_eqvt Diff_iff bn_eqvt permute_zero supp_eqvt swap_different_sorts swap_set_in)
-- \<open>3 subgoals\<close>
  apply (subgoal_tac "infinite {b. (x \<rightleftharpoons> b) \<bullet> t\<^sub>\<alpha> \<noteq> t\<^sub>\<alpha>}")
   prefer 2
   apply (simp add: supp_def)
  apply (subgoal_tac "infinite ({b. (x \<rightleftharpoons> b) \<bullet> t\<^sub>\<alpha> \<noteq> t\<^sub>\<alpha>} - supp t\<^sub>\<alpha>)")
   prefer 2
   apply (metis Diff_infinite_finite)
  apply (thin_tac "infinite {b. (x \<rightleftharpoons> b) \<bullet> t\<^sub>\<alpha> \<noteq> t\<^sub>\<alpha>}")
  apply (subst supp_def)
  apply (rule CollectI)
  apply (erule infinite_mono)
  apply (rename_tac b)
  apply (clarsimp simp add: Act\<^sub>\<alpha>_eq_iff)
  apply (thin_tac "(bn ((x \<rightleftharpoons> b) \<bullet> \<alpha>), (x \<rightleftharpoons> b) \<bullet> \<alpha>) \<approx>set (op =) supp p (bn \<alpha>, \<alpha>)")
  apply (auto simp add: alphas)[1]
  apply (subgoal_tac "fv_Tree (rep_Tree\<^sub>\<alpha> ((x \<rightleftharpoons> b) \<bullet> t\<^sub>\<alpha>)) = (x \<rightleftharpoons> b) \<bullet> fv_Tree (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>)")
   prefer 2
   apply (metis alpha_Tree_fv_Tree alpha_Tree_permute_rep_commute fv_Tree_eqvt)
  apply (metis DiffD1 DiffI mem_permute_iff permute_zero swap_atom swap_different_sorts)
-- \<open>2 subgoals\<close>
 apply (subgoal_tac "supp (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>) \<subseteq> supp \<alpha> \<union> supp t\<^sub>\<alpha>")
  apply blast
 apply (subgoal_tac "(supp \<alpha> \<union> supp t\<^sub>\<alpha>) supports Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>")
  apply (metis finite_UnI finite_supp supp_is_subset)
 apply (simp add: supports_def)
 apply (metis fresh_def swap_fresh_fresh)
-- \<open>1 subgoal\<close>
apply (subgoal_tac "infinite {b. (x \<rightleftharpoons> b) \<bullet> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> \<noteq> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>}")
 prefer 2
 apply (simp add: supp_def)
apply (subgoal_tac "infinite ({b. (x \<rightleftharpoons> b) \<bullet> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> \<noteq> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>} - supp \<alpha> - supp t\<^sub>\<alpha>)")
 prefer 2
 apply (metis Diff_infinite_finite finite_supp)
apply (thin_tac "infinite {b. (x \<rightleftharpoons> b) \<bullet> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> \<noteq> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>}")
apply (subgoal_tac "\<exists>b. b \<in> {b. (x \<rightleftharpoons> b) \<bullet> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> \<noteq> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>} - supp \<alpha> - supp t\<^sub>\<alpha>")
 prefer 2
 apply (metis infinite_mono)
apply (thin_tac "infinite ({b. (x \<rightleftharpoons> b) \<bullet> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha> \<noteq> Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>} - supp \<alpha> - supp t\<^sub>\<alpha>)")
apply (auto simp add: Act\<^sub>\<alpha>_eq_iff)
apply (drule_tac x="(x \<rightleftharpoons> b)" in spec)
apply auto
 prefer 2
 apply (erule notE) back back
 apply (simp add: alphas)
 apply (rule context_conjI)
  apply (metis (erased, hide_lams) Diff_eqvt Diff_iff bn_eqvt supp_eqvt swap_set_not_in)
 apply (rule conjI)
  apply (metis DiffD2 Diff_subset contra_subsetD fresh_perm fresh_star_def swap_atom)
 apply (metis bn_eqvt permute_swap_cancel)
apply (erule notE) back back
apply (simp add: alphas)
apply (subgoal_tac "supp ((x \<rightleftharpoons> b) \<bullet> \<alpha>) - bn ((x \<rightleftharpoons> b) \<bullet> \<alpha>) = supp \<alpha> - bn \<alpha>")
 prefer 2
 apply (metis (erased, hide_lams) Diff_eqvt Diff_iff bn_eqvt supp_eqvt swap_set_not_in)
apply (rule context_conjI)
 apply (subgoal_tac "fv_Tree ((x \<rightleftharpoons> b) \<bullet> rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>) = fv_Tree (rep_Tree\<^sub>\<alpha> ((x \<rightleftharpoons> b) \<bullet> t\<^sub>\<alpha>))")
  prefer 2
  apply (metis alpha_Tree_fv_Tree alpha_Tree_permute_rep_commute)
 apply (metis (mono_tags, hide_lams) Diff_eqvt Diff_iff bn_eqvt fv_Tree_eqvt swap_set_not_in)
apply (rule conjI)
 apply (metis DiffD2 Diff_subset contra_subsetD fresh_perm fresh_star_def swap_atom)
apply (rule conjI)
 apply (metis alpha_Tree_permute_rep_commute permute_swap_cancel)
apply (metis bn_eqvt permute_swap_cancel)
done
qed

lemma supp_Act\<^sub>\<alpha> [simp]:
  assumes "hereditarily_fs t\<^sub>\<alpha>"
  shows "supp (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>) = supp \<alpha> \<union> supp t\<^sub>\<alpha> - bn \<alpha>"
using assms
apply (subst fv_Tree_rep_Tree\<^sub>\<alpha>_eq_supp[symmetric])
 apply (metis Act\<^sub>\<alpha>)
apply (subgoal_tac "fv_Tree (rep_Tree\<^sub>\<alpha> (Act\<^sub>\<alpha> \<alpha> t\<^sub>\<alpha>)) = fv_Tree (tAct \<alpha> (rep_Tree\<^sub>\<alpha> t\<^sub>\<alpha>))")
 prefer 2
 apply (metis Act\<^sub>\<alpha>.abs_eq Tree\<^sub>\<alpha>_abs_rep Tree\<^sub>\<alpha>_rep_abs alpha_Tree_fv_Tree)
apply (metis Formula.fv_tAct fv_Tree_rep_Tree\<^sub>\<alpha>_eq_supp)
done

lemma supp_Act [simp]: "supp (Act \<alpha> x) = supp \<alpha> \<union> supp x - bn \<alpha>"
by (metis Act.rep_eq Rep_formula' supp_Act\<^sub>\<alpha> supp_Rep_formula)

lemma formula_strong_induct_aux:
  fixes x
  assumes "\<And>xset c. finite (supp xset) \<Longrightarrow> (\<And>x. x \<in> set_bset xset \<Longrightarrow> (\<And>c. P c x)) \<Longrightarrow> P c (Conj xset)"
    and "\<And>formula c. (\<And>c. P c formula) \<Longrightarrow> P c (Not formula)"
    and "\<And>pred c. P c (Pred pred)"
    and "\<And>act formula c. bn act \<sharp>* c \<Longrightarrow> (\<And>c. P c formula) \<Longrightarrow> P c (Act act formula)"
  shows "\<And>(c :: 'd\<Colon>fs) p. P c (p \<bullet> x)"
proof (induction x)
  case (Conj xset)
    then moreover have "finite (supp (p \<bullet> xset))"
      by (metis permute_finite supp_eqvt)
    moreover have "(\<And>x c. x \<in> set_bset (p \<bullet> xset) \<Longrightarrow> P c x)"
      by (metis (full_types) Conj.IH eqvt_bound mem_permute_iff set_bset_eqvt)
    ultimately show ?case
      using assms(1) by simp
next
  case Not then show ?case
    using assms(2) by simp
next
  case Pred show ?case
    using assms(3) by simp
next
  case (Act \<alpha> x) then show ?case
    using assms(4)
apply simp
apply (subgoal_tac "finite ((supp (p \<bullet> \<alpha>) \<union> supp (p \<bullet> x)) - bn (p \<bullet> \<alpha>))")
 prefer 2
 apply (metis finite_Diff finite_UnI finite_supp)
apply (subgoal_tac "\<exists>q. (q \<bullet> bn (p \<bullet> \<alpha>)) \<sharp>* c \<and> supp ((supp (p \<bullet> \<alpha>) \<union> supp (p \<bullet> x)) - bn (p \<bullet> \<alpha>)) \<sharp>* q")
 prefer 2
 apply (rule at_set_avoiding2)
    apply (metis bn_finite)
   apply (metis finite_supp)
  apply (metis supp_finite_atom_set)
 apply (metis DiffE fresh_def fresh_star_def supp_finite_atom_set)
apply (subgoal_tac "supp (supp (p \<bullet> \<alpha>) \<union> supp (p \<bullet> x) - bn (p \<bullet> \<alpha>)) = supp (p \<bullet> \<alpha>) \<union> supp (p \<bullet> x) - bn (p \<bullet> \<alpha>)")
 prefer 2
 apply (metis supp_finite_atom_set)
apply simp
apply (thin_tac "supp (supp (p \<bullet> \<alpha>) \<union> supp (p \<bullet> x) - bn (p \<bullet> \<alpha>)) = supp (p \<bullet> \<alpha>) \<union> supp (p \<bullet> x) - bn (p \<bullet> \<alpha>)")
apply (auto simp add: bn_eqvt)
apply (drule_tac x="q \<bullet> p \<bullet> \<alpha>" in meta_spec)
apply (drule_tac x="c" in meta_spec) back
apply (drule_tac x="q \<bullet> p \<bullet> x" in meta_spec)
apply (drule meta_mp)
 apply assumption
apply (drule meta_mp)
 apply (metis permute_plus)
apply (subgoal_tac "Act (q \<bullet> p \<bullet> \<alpha>) (q \<bullet> p \<bullet> x) = Act (p \<bullet> \<alpha>) (p \<bullet> x)")
 apply simp
apply (thin_tac "\<And>c p. P c (p \<bullet> x)")
apply (simp add: Act_eq_iff Act\<^sub>\<alpha>_eq_iff)
apply (rule_tac x="- q" in exI)
apply (simp add: alphas fv_Tree_rep_Tree\<^sub>\<alpha>_eq_supp bn_eqvt)
apply (rule context_conjI)
 apply (metis (erased, lifting) Diff_eqvt Un_Diff atom_set_perm_eq bn_eqvt fresh_star_Un supp_eqvt)
apply (rule conjI)
 apply (metis Un_Diff fresh_minus_perm fresh_star_Un fresh_star_def)
apply (rule conjI)
 apply (metis (no_types, hide_lams) Tree\<^sub>\<alpha>.abs_eq_iff Tree\<^sub>\<alpha>_abs_rep permute_Tree\<^sub>\<alpha>.abs_eq permute_formula.rep_eq permute_minus_cancel(2))
apply (rule context_conjI)
 apply (metis (erased, lifting) Diff_eqvt Un_Diff atom_set_perm_eq bn_eqvt fresh_star_Un supp_eqvt)
apply (metis Un_Diff fresh_minus_perm fresh_star_Un fresh_star_def)
done
qed

lemmas formula_strong_induct = formula_strong_induct_aux[where p=0, simplified]
declare formula_strong_induct [case_names Conj Not Pred Act Env]

end

