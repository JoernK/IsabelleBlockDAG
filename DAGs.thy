(* 
    Author:     Joern Kussmaul
*)


theory DAGs
  imports Main "Graph_Theory.Graph_Theory"
begin

section \<open>DAG\<close>


locale DAG = digraph +
  assumes cycle_free: "\<not>(v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v)" 

subsection  \<open>Functions and Definitions\<close>

fun (in DAG) direct_past:: "'a \<Rightarrow> 'a set"
  where "direct_past a = {b. (b \<in> verts G \<and> (a,b) \<in> arcs_ends G)}"

fun (in DAG) future_nodes:: "'a \<Rightarrow> 'a set"
  where "future_nodes a = {b.  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a}"

fun (in DAG) past_nodes:: "'a \<Rightarrow> 'a set"
  where "past_nodes a = {b. a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b}"

fun (in DAG) past_nodes_refl :: "'a \<Rightarrow> 'a set"
  where "past_nodes_refl a = {b. a \<rightarrow>\<^sup>*\<^bsub>G\<^esub> b}"

fun (in DAG) reduce_past:: "'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past a = induce_subgraph G (past_nodes a)"

fun (in DAG) reduce_past_refl:: "'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past_refl a = induce_subgraph G (past_nodes_refl a)"
                                          
fun (in DAG) is_tip:: " 'a \<Rightarrow> bool"
  where "is_tip a = ((a \<in> verts G) \<and>  (ALL x. \<not> x \<rightarrow>\<^sup>+ a))"

definition (in DAG) tips:: "'a set"
  where "tips = {v. is_tip v}"


subsection \<open>Lemmas\<close>
  
lemma (in DAG) unidirectional:
"u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  using cycle_free reachable1_reachable_trans by auto

subsubsection \<open>Tips\<close>

lemma (in DAG) del_tips_dag:
assumes "is_tip t"
shows "DAG (del_vert t)"
  unfolding DAG_def DAG_axioms_def
proof safe
  show "digraph (del_vert t)" using del_vert_simps DAG_axioms 
      digraph_def
    using digraph_subgraph subgraph_del_vert
    by auto 
next 
    fix v
    assume "v \<rightarrow>\<^sup>+\<^bsub>del_vert t\<^esub> v"
    then have "v \<rightarrow>\<^sup>+ v" using subgraph_del_vert
      by (meson arcs_ends_mono trancl_mono) 
    then show False
      by (simp add: cycle_free)
  qed

subsubsection \<open>Future Nodes\<close>

lemma (in DAG) future_nodes_not_refl:
  assumes "a \<in> verts G"
  shows "a \<notin> future_nodes a"
  using cycle_free future_nodes.simps reachable_def by auto

subsubsection \<open>Past Nodes\<close>

lemma (in DAG) past_nodes_not_refl:
  assumes "a \<in> verts G"
  shows "a \<notin> past_nodes a"
  using cycle_free past_nodes.simps reachable_def by auto

lemma (in DAG) past_nodes_verts: 
  shows "past_nodes a \<subseteq> verts G"
  using past_nodes.simps reachable1_in_verts by auto

lemma (in DAG) past_nodes_refl_ex:
  assumes "a \<in> verts G"
  shows "a \<in> past_nodes_refl a"
  using past_nodes_refl.simps reachable_refl assms
  by simp

lemma (in DAG) past_nodes_refl_verts: 
  shows "past_nodes_refl a \<subseteq> verts G"
  using past_nodes.simps reachable_in_verts by auto

lemma (in DAG) finite_past: "finite (past_nodes a)"
  by (metis finite_verts rev_finite_subset past_nodes_verts)

lemma (in DAG) future_nodes_verts: 
  shows "future_nodes a \<subseteq> verts G"
  using future_nodes.simps reachable1_in_verts by auto

lemma (in DAG) finite_future: "finite (future_nodes a)"
  by (metis finite_verts rev_finite_subset future_nodes_verts)

lemma (in DAG) past_future_dis[simp]: "past_nodes a \<inter> future_nodes a = {}"
proof (rule ccontr)
  assume "\<not> past_nodes a \<inter> future_nodes a = {}"
  then show False
    using past_nodes.simps future_nodes.simps unidirectional reachable1_reachable by blast
qed

subsubsection \<open>Reduce Past\<close>

lemma (in DAG) reduce_past_arcs: 
  shows "arcs (reduce_past a) \<subseteq> arcs G"
  using induce_subgraph_arcs past_nodes.simps by auto

lemma (in DAG) reduce_past_arcs2:
  "e \<in> arcs (reduce_past a) \<Longrightarrow> e \<in> arcs G"
  using reduce_past_arcs by auto

lemma (in DAG) reduce_past_induced_subgraph:
  shows "induced_subgraph (reduce_past a) G"
  using  induced_induce past_nodes_verts by auto

lemma (in DAG) reduce_past_path:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v" 
  shows " u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v"
  using assms
proof induct
  case base then show ?case
    using dominates_induce_subgraphD r_into_trancl' reduce_past.simps
    by metis
next case (step u v) show ?case
    using dominates_induce_subgraphD reachable1_reachable_trans reachable_adjI 
        reduce_past.simps step.hyps(2) step.hyps(3) by metis
     
qed


lemma (in DAG) reduce_past_pathr:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> v" 
  shows " u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  by (meson assms induced_subgraph_altdef reachable_mono reduce_past_induced_subgraph)


subsubsection \<open>Reduce Past Reflexiv\<close>

lemma (in DAG) reduce_past_refl_induced_subgraph:
  shows "induced_subgraph (reduce_past_refl a) G"
  using  induced_induce past_nodes_refl_verts by auto

lemma (in DAG) reduce_past_refl_arcs2:
  "e \<in> arcs (reduce_past_refl a) \<Longrightarrow> e \<in> arcs G"
  using reduce_past_arcs by auto

lemma (in DAG) reduce_past_refl_digraph:
  assumes "a \<in> verts G"
  shows "digraph (reduce_past_refl a)"
  using digraphI_induced reduce_past_refl_induced_subgraph reachable_mono by simp

end
