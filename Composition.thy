(* 
    Author:     Joern Kussmaul
*)

theory Composition
  imports Main blockDAG Spectre
begin

section  \<open>Composition\<close>

locale composition = blockDAG  +
  fixes C ::"'a set"
  assumes "C \<subseteq> verts G"
  and "blockDAG (G \<restriction> C)"
  and same_rel:  "\<forall>v \<in> ((verts G)- C). 
  (\<forall>c \<in> C. (c \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v)) \<or> (\<forall>c \<in> C. (v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c)) 
   \<or> (\<forall>c \<in> C. \<not>(v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c) \<and>  \<not>(v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c)) "       

locale compositionGraph = blockDAG +
  fixes G' ::"('a set, 'b) pre_digraph"
  assumes "\<forall>C \<in> (verts G'). composition G C"
  and "\<forall> C1 \<in> (verts G'). \<forall> C2 \<in> (verts G'). C1 \<inter> C2 \<noteq> {} \<longrightarrow> C1 = C2"
  and "\<Union> (verts G') = verts G"

locale tie_break_compositionGraph = tie_breakingDAG + 
  fixes G' ::"('a::linorder set, 'b) pre_digraph"
  assumes "\<forall>C \<in> (verts G'). composition G C"
  and "\<forall> C1 \<in> (verts G'). \<forall> C2 \<in> (verts G'). C1 \<inter> C2 \<noteq> {} \<longrightarrow> C1 = C2"
  and "\<Union> (verts G') = verts G"
 
subsection  \<open>Functions and Definitions\<close>

subsection \<open>Lemmas\<close>

lemma (in blockDAG) trivialComposition: 
  assumes "C = verts G"
  shows "composition G C"
proof -
  show "composition G C"
    unfolding composition_axioms_def composition_def
  proof  
    show "blockDAG G" using blockDAG_axioms by simp
  next 
    have subset: "C \<subseteq> verts G" using assms by auto
    then have "G \<restriction> C = G" unfolding assms induce_subgraph_def
      using induce_eq_iff_induced induced_subgraph_refl assms by auto 
    then have bD: "blockDAG (G \<restriction> C)" using blockDAG_axioms by simp
    have "\<nexists>v. v \<in> (verts G) - C" using assms by simp
    then have "(\<forall>v\<in>verts G - C. (\<forall>c\<in>C. c \<rightarrow>\<^sup>+ v) \<or> (\<forall>c\<in>C. v \<rightarrow>\<^sup>+ c) \<or> (\<forall>c\<in>C. \<not> v \<rightarrow>\<^sup>+ c \<and> \<not> v \<rightarrow>\<^sup>+ c))"
      by auto
    then show "C \<subseteq> verts G \<and>
    blockDAG (G \<restriction> C) \<and>
    (\<forall>v\<in>verts G - C. (\<forall>c\<in>C. c \<rightarrow>\<^sup>+ v) \<or> (\<forall>c\<in>C. v \<rightarrow>\<^sup>+ c) \<or> (\<forall>c\<in>C. \<not> v \<rightarrow>\<^sup>+ c \<and> \<not> v \<rightarrow>\<^sup>+ c))" 
        using subset bD by simp
    qed  
  qed

lemma (in blockDAG) compositionExists:
  shows "\<exists>C. composition G C"
proof
  let ?C = "verts G" 
  show "composition G ?C" using trivialComposition by auto 
  qed

lemma (in blockDAG)  compositionGraphExists:
  shows "\<exists>G'. compositionGraph G G'"
proof -
  obtain C where c_def: "C = verts G" by auto
  then have "composition G C" using trivialComposition by simp
  obtain G'::"('a set, 'b) pre_digraph"
  where g'_def: "verts G' = {C}"
    by (metis induce_subgraph_verts) 
  have "compositionGraph G G'" unfolding compositionGraph_axioms_def compositionGraph_def
      g'_def c_def 
  proof safe
    show "blockDAG G" using blockDAG_axioms by simp
  next 
    show "composition G (verts G)" using trivialComposition by simp
  next
    fix x   
    assume "x \<in> verts G"
    then show " x \<in> \<Union> {verts G}" by simp
  qed
  then show "?thesis" by auto
qed
end