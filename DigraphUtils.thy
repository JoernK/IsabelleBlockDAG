(* 
    Author:     Joern Kussmaul
*)


theory DigraphUtils
  imports Main "Graph_Theory.Graph_Theory"
begin

section \<open>Digraph Utilities\<close>

lemma graph_equality:
  assumes "digraph G \<and> digraph C"
  assumes "verts G = verts C \<and> arcs G = arcs C \<and> head G = head C \<and> tail G = tail C"
  shows "G = C"
  by (simp add: assms(2)) 



lemma (in digraph) del_vert_not_in_graph:
  assumes "b \<notin> verts G"
  shows "(pre_digraph.del_vert G b) = G"
proof -
  have v: "verts (pre_digraph.del_vert G b) = verts G"
    using assms(1)
    by (simp add: pre_digraph.verts_del_vert) 
  have "\<forall>e \<in> arcs G. tail G e \<noteq> b \<and> head G e \<noteq> b " using digraph_axioms
      assms digraph.axioms(2) loopfree_digraph.axioms(1)
    by auto 
  then have " arcs G \<subseteq> arcs (pre_digraph.del_vert G b)"
    using assms
    by (simp add: pre_digraph.arcs_del_vert subsetI) 
  then have e: "arcs G = arcs (pre_digraph.del_vert G b)"
    by (simp add: pre_digraph.arcs_del_vert subset_antisym)
  then show ?thesis using v by (simp add: pre_digraph.del_vert_simps)
qed 

lemma del_arc_subgraph:
  assumes "subgraph H G"
  assumes "digraph G \<and> digraph H"
  shows "subgraph (pre_digraph.del_arc H e2) (pre_digraph.del_arc G e2)"
  using subgraph_def pre_digraph.del_arc_simps Diff_iff
proof -
  have f1: "\<forall>p pa. subgraph p pa = ((verts p::'a set) \<subseteq> verts pa \<and> (arcs p::'b set) \<subseteq> arcs pa \<and> 
  wf_digraph pa \<and> wf_digraph p \<and> compatible pa p)"
    using subgraph_def by blast
  have "arcs H - {e2} \<subseteq> arcs G - {e2}" using assms(1)
    by auto
  then show ?thesis
    unfolding subgraph_def 
    using f1 assms(1) by (simp add: compatible_def pre_digraph.del_arc_simps wf_digraph.wf_digraph_del_arc)
qed

lemma graph_nat_induct[consumes 0, case_names base step]: 
  assumes

cases: "\<And>V. (digraph V \<Longrightarrow> card (verts V) = 0 \<Longrightarrow> P V)"
"\<And>W c. (\<And>V. (digraph V \<Longrightarrow> card (verts V) = c \<Longrightarrow> P V)) 
  \<Longrightarrow> (digraph W \<Longrightarrow> card (verts W) = (Suc c) \<Longrightarrow> P W)"
shows "\<And>Z. digraph Z \<Longrightarrow> P Z"
proof - 
  fix Z:: "('a,'b) pre_digraph"
  assume major: "digraph Z"
  then show "P Z"
  proof (induction "card (verts Z)" arbitrary: Z)
    case 0
    then show ?case
      by (simp add: local.cases(1) major) 
  next
    case su: (Suc x)
    assume "(\<And>Z. x = card (verts Z) \<Longrightarrow> digraph Z \<Longrightarrow> P Z)"
    show ?case
      by (metis local.cases(2) su.hyps(1) su.hyps(2) su.prems)   
  qed   
qed 
end

