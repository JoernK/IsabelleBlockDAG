theory Scratch
  imports Main Utils
begin

locale uni =
  fixes A::"'a set"
  assumes uni_uni: "\<And> x. x \<in> A"

lemma (in uni) linear_linorder:
  assumes  "linear_order_on A R" 
  shows "class.linorder (\<lambda>x y. (x,y) \<in> R) (\<lambda>x y. (x,y) \<in> R \<and> x \<noteq> y)"
proof 
  fix x y z 
  have x_in: "x \<in> A" and y_in: "y \<in> A" and z_in: "z \<in> A" using uni_uni by auto
  thus "((x, y) \<in> R \<and> x \<noteq> y) = ((x, y) \<in> R \<and> (y, x) \<notin> R)" 
    using assms unfolding linear_order_on_def partial_order_on_def antisym_def by auto
  with x_in show "(x, x) \<in> R" using assms
    unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def by auto
  with x_in y_in show "(x, y) \<in> R \<or> (y, x) \<in> R" 
    using assms unfolding linear_order_on_def total_on_def by auto
  show "(x, y) \<in> R \<Longrightarrow> (y, x) \<in> R \<Longrightarrow> x = y" using assms unfolding 
  linear_order_on_def partial_order_on_def  antisym_def by auto
  show "(x, y) \<in> R \<Longrightarrow> (y, z) \<in> R \<Longrightarrow> (x, z) \<in> R" using assms unfolding 
  linear_order_on_def partial_order_on_def preorder_on_def trans_def by metis
qed

fun rel_to_list ::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a list" 
  where "rel_to_list R A= linorder.sorted_list_of_set (\<lambda>x y. (x,y) \<in> R) A" 

lemma (in uni) rel_to_list_sorted:
  assumes "linear_order_on A R" 
  shows "linorder.sorted (\<lambda>x y. (x,y) \<in> R) (rel_to_list R A)"
  unfolding  rel_to_list.simps 
  using assms  linear_linorder linorder.sorted_list_of_set(2) by blast


text\<open>Casting\<close>

fun is_PR :: "('b \<times> 'a rel \<times> 'a set) \<Rightarrow> bool"
  where "is_PR (P,R,A) = ((Field R = A) \<and> (finite A) \<and> (linear_order_on A R))" 

typedef ('a,'b) PR = "{x::('b \<times>'a rel \<times> 'a set). is_PR x}" 
proof(simp) 
  let ?a = "{}"
  have "Field ?a = {}" by auto
  then have "finite (Field ?a)" by auto
  moreover have "Linear_order ?a" by auto 
  ultimately show "\<exists>a. finite (Field a) \<and> Linear_order a" by metis
qed

lemma "\<forall> D:: ('a,'b) PR .\<exists> A B C. Abs_PR (A,B,C) = D"
  by (metis Rep_PR_inverse prod.collapse) 

lemma "\<forall> D:: ('a,'b) PR .\<exists> A B C. Rep_PR D  = (A,B,C)"
  by (metis prod.collapse) 

fun is_PL :: "('b \<times> 'a list \<times> 'a set) \<Rightarrow> bool"
  where "is_PL (P,L,A) = ((set L = A) \<and> (finite A) \<and> distinct L)" 

typedef ('a,'b) PL = "{x::('b \<times>'a list \<times> 'a set). is_PL x}"
  by auto


setup_lifting PL.type_definition_PL  
context begin

qualified definition abs_PL  :: "('a,'b) PR \<Rightarrow> ('a,'b) PL"
  where "abs_PL = Abs_PL o (\<lambda> (B,R,S). (B, rel_to_list R S, S)) o Rep_PR"

definition PR_of_PL ::  "('a,'b) PL  \<Rightarrow> ('a,'b) PR"
where "PR_of_PL = Abs_PR o (\<lambda> (B,L,S). (B, list_to_rel L, S)) o Rep_PL"

qualified definition PL_eq where "PL_eq = BNF_Def.vimage2p Rep_PR Rep_PR (=)"

qualified lemma equivp_dlist_eq: "equivp PL_eq"
  unfolding PL_eq_def by(rule equivp_vimage2p)(rule identity_equivp)

definition qcr_PL :: "('a,'b) PR  \<Rightarrow> ('a,'b) PL \<Rightarrow> bool" 
  where "qcr_PL x y \<longleftrightarrow> (\<lambda> (B,R,S). (B, list_to_rel R, S)) (Rep_PL y) =  Rep_PR x"

qualified lemma Quotient_PL_PR: 
  "Quotient PL_eq abs_PL PR_of_PL qcr_PL" 
  sorry

end

end

