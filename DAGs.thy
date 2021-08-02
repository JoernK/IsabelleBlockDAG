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

fun  direct_past:: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "direct_past G  a = {b \<in> verts G. (a,b) \<in> arcs_ends G}"

fun future_nodes:: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "future_nodes G a = {b \<in> verts G.  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a}"

fun past_nodes:: "('a,'b) pre_digraph \<Rightarrow>'a \<Rightarrow> 'a set"
  where "past_nodes G a = {b \<in> verts G. a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b}"

fun past_nodes_refl :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "past_nodes_refl G a = {b \<in> verts G. a \<rightarrow>\<^sup>*\<^bsub>G\<^esub> b}"

fun anticone:: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "anticone G a = {b \<in> verts G. \<not>(a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b \<or>  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a \<or> a = b)}" 

fun reduce_past:: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past G a = induce_subgraph G (past_nodes G a)"

fun reduce_past_refl:: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past_refl G a = induce_subgraph G (past_nodes_refl G a)"
                                          
fun is_tip:: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_tip G a = ((a \<in> verts G) \<and>  (\<forall> x \<in> verts G. \<not> x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a))"

definition tips:: "('a,'b) pre_digraph \<Rightarrow> 'a set"
  where "tips G = {v \<in> verts G. is_tip G v}"

fun kCluster:: "('a,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> 'a set  \<Rightarrow> bool"
  where  "kCluster G k C =  (if (C \<subseteq> (verts G))
   then (\<forall>a \<in> C. card ((anticone G a) \<inter> C) \<le> k) else False)"

subsection \<open>Lemmas\<close>
  
lemma (in DAG) unidirectional:
"u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  using cycle_free reachable1_reachable_trans by auto

subsubsection \<open>Tips\<close>


lemma (in DAG) tips_not_referenced:
  assumes "is_tip G t"
  shows "\<forall>x. \<not> x \<rightarrow>\<^sup>+ t"
  using is_tip.simps assms reachable1_in_verts(1)
  by metis 

lemma (in DAG) del_tips_dag:
assumes "is_tip G t"
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

lemma (in digraph) tips_finite:
  shows "finite (tips G)"
  using tips_def fin_digraph.finite_verts digraph.axioms(1) digraph_axioms Collect_mono is_tip.simps
  by (simp add: tips_def)
  
lemma (in digraph) tips_in_verts:
  shows "tips G \<subseteq>  verts G"  unfolding tips_def
  using Collect_subset by auto

lemma tips_tips: 
  assumes "x \<in> tips G"
  shows "is_tip G x" using tips_def CollectD assms(1) by metis

subsubsection \<open>Anticone\<close>

lemma (in DAG) tips_anticone:
  assumes "a \<in> tips G"
  and "b \<in> tips G"
  and "a \<noteq> b"
  shows "a \<in> anticone G b"
proof(rule ccontr)
  assume " a \<notin> anticone G b" 
  then have k: "(a \<rightarrow>\<^sup>+ b \<or>  b \<rightarrow>\<^sup>+ a \<or> a = b)" using anticone.simps assms tips_def
    by fastforce 
  then have "\<not> (\<forall>x\<in>verts G.  x \<rightarrow>\<^sup>+ a) \<or> \<not> (\<forall>x\<in>verts G.  x \<rightarrow>\<^sup>+ b)" using  reachable1_in_verts
      assms(3) cycle_free
    by (metis) 
  then have "\<not> is_tip G a \<or> \<not> is_tip G b" using  assms(3) is_tip.simps k
    by (metis)
  then have "  \<not> a \<in> tips G \<or>  \<not>  b \<in> tips G" using tips_def CollectD by metis
  then show False using assms by auto
qed

lemma (in DAG) anticone_in_verts: 
  shows "anticone G a \<subseteq> verts G" using anticone.simps by auto

lemma (in DAG) anticon_finite:
   shows "finite (anticone G a)" using anticone_in_verts by auto

lemma (in DAG) anticon_not_refl:
   shows "a \<notin> (anticone G a)" by auto

subsubsection \<open>Future Nodes\<close>

lemma (in DAG) future_nodes_not_refl:
  assumes "a \<in> verts G"
  shows "a \<notin> future_nodes G a"
  using cycle_free future_nodes.simps reachable_def by auto

subsubsection \<open>Past Nodes\<close>

lemma (in DAG) past_nodes_not_refl:
  assumes "a \<in> verts G"
  shows "a \<notin> past_nodes G a"
  using cycle_free past_nodes.simps reachable_def by auto

lemma (in DAG) past_nodes_verts: 
  shows "past_nodes G a \<subseteq> verts G"
  using past_nodes.simps reachable1_in_verts by auto

lemma (in DAG) past_nodes_refl_ex:
  assumes "a \<in> verts G"
  shows "a \<in> past_nodes_refl G a"
  using past_nodes_refl.simps reachable_refl assms
  by simp

lemma (in DAG) past_nodes_refl_verts: 
  shows "past_nodes_refl G a \<subseteq> verts G"
  using past_nodes.simps reachable_in_verts by auto

lemma (in DAG) finite_past: "finite (past_nodes G a)"
  by (metis finite_verts rev_finite_subset past_nodes_verts)

lemma (in DAG) future_nodes_verts: 
  shows "future_nodes G a \<subseteq> verts G"
  using future_nodes.simps reachable1_in_verts by auto

lemma (in DAG) finite_future: "finite (future_nodes G a)"
  by (metis finite_verts rev_finite_subset future_nodes_verts)

lemma (in DAG) past_future_dis[simp]: "past_nodes G a \<inter> future_nodes G a = {}"
proof (rule ccontr)
  assume "\<not> past_nodes G a \<inter> future_nodes G a = {}"
  then show False
    using past_nodes.simps future_nodes.simps unidirectional reachable1_reachable by auto
qed

subsubsection \<open>Reduce Past\<close>

lemma (in DAG) reduce_past_arcs: 
  shows "arcs (reduce_past G a) \<subseteq> arcs G"
  using induce_subgraph_arcs past_nodes.simps by auto

lemma (in DAG) reduce_past_arcs2:
  "e \<in> arcs (reduce_past G a) \<Longrightarrow> e \<in> arcs G"
  using reduce_past_arcs by auto

lemma (in DAG) reduce_past_induced_subgraph:
  shows "induced_subgraph (reduce_past G a) G"
  using  induced_induce past_nodes_verts by auto

lemma (in DAG) reduce_past_path:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>reduce_past G a\<^esub> v" 
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
  assumes "u \<rightarrow>\<^sup>*\<^bsub>reduce_past G a\<^esub> v" 
  shows " u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  by (meson assms induced_subgraph_altdef reachable_mono reduce_past_induced_subgraph)


subsubsection \<open>Reduce Past Reflexiv\<close>

lemma (in DAG) reduce_past_refl_induced_subgraph:
  shows "induced_subgraph (reduce_past_refl G a) G"
  using  induced_induce past_nodes_refl_verts by auto

lemma (in DAG) reduce_past_refl_arcs2:
  "e \<in> arcs (reduce_past_refl G a) \<Longrightarrow> e \<in> arcs G"
  using reduce_past_arcs by auto

lemma (in DAG) reduce_past_refl_digraph:
  assumes "a \<in> verts G"
  shows "digraph (reduce_past_refl G a)"
  using digraphI_induced reduce_past_refl_induced_subgraph reachable_mono by simp

end
