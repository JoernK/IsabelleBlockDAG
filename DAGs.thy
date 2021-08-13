(* 
    Author:     Joern Kussmaul
*)


theory DAGs
  imports Main "Graph_Theory.Graph_Theory"
begin

section \<open>DAG\<close>


locale DAG = digraph +
  assumes cycle_free: "\<not>(v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v)" 

sublocale DAG \<subseteq> wf_digraph using DAG_def digraph_def nomulti_digraph_def DAG_axioms by auto

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

lemma (in DAG) reduce_past_path2:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v"
  and "u \<in> past_nodes G a"
  and "v \<in> past_nodes G a"
  shows "u \<rightarrow>\<^sup>+\<^bsub>reduce_past G a\<^esub> v" 
  using assms
proof(induct u v)
  case (r_into_trancl u v )
  then obtain e where e_in: " arc e (u,v)" using arc_def DAG_axioms wf_digraph_def
    by auto 
  then have e_in2: "e \<in> arcs (reduce_past G a)" unfolding reduce_past.simps induce_subgraph_arcs
    using arcE r_into_trancl.prems(1) r_into_trancl.prems(2) by blast
  then have "arc_to_ends (reduce_past G a) e = (u,v)" unfolding reduce_past.simps using e_in
  arcE arc_to_ends_def induce_subgraph_head induce_subgraph_tail
    by metis  
  
  then have  "u \<rightarrow>\<^bsub>reduce_past G a\<^esub> v" using e_in2 wf_digraph.dominatesI DAG_axioms
    by (metis reduce_past.simps wellformed_induce_subgraph)  
  then show ?case by auto
next
  case (trancl_into_trancl a2 b c)
  then have b_in: "b \<in> past_nodes G a" unfolding past_nodes.simps 
    by (metis (mono_tags, lifting) adj_in_verts(1) mem_Collect_eq
        reachable1_reachable reachable1_reachable_trans) 
  then have a2_re_b: "a2 \<rightarrow>\<^sup>+\<^bsub>reduce_past G a\<^esub> b" using trancl_into_trancl by auto
  then obtain e where e_in: " arc e (b,c)" using trancl_into_trancl 
      arc_def DAG_axioms wf_digraph_def by auto 
  then have e_in2: "e \<in> arcs (reduce_past G a)" unfolding reduce_past.simps induce_subgraph_arcs
    using arcE trancl_into_trancl
    b_in by blast 
  then have "arc_to_ends (reduce_past G a) e = (b,c)" unfolding reduce_past.simps using e_in
  arcE arc_to_ends_def induce_subgraph_head induce_subgraph_tail
    by metis  
  then have  "b \<rightarrow>\<^bsub>reduce_past G a\<^esub> c" using e_in2 wf_digraph.dominatesI DAG_axioms
    by (metis reduce_past.simps wellformed_induce_subgraph)  
  then show ?case using a2_re_b
    by (metis trancl.trancl_into_trancl) 
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


subsubsection \<open>Reachability cases\<close>

lemma (in DAG) reachable1_cases:
  obtains (nR) "\<not> a \<rightarrow>\<^sup>+ b \<and> \<not>  b \<rightarrow>\<^sup>+ a \<and> a \<noteq> b"
  | (one) "a \<rightarrow>\<^sup>+ b"
  | (two) "b \<rightarrow>\<^sup>+ a"
  | (eq) "a = b"
  using reachable_neq_reachable1 DAG_axioms
  by metis

lemma (in DAG) verts_comp:
  assumes "x \<in> tips G"
  shows " verts G = {x} \<union> (anticone G x) \<union> (verts (reduce_past G x))"
proof 
  show "verts G \<subseteq> {x} \<union> anticone G x \<union> verts (reduce_past G x)" 
  proof(rule subsetI)
    fix xa 
    assume in_V: "xa \<in> verts G"
    then show "xa \<in> {x} \<union> anticone G x \<union> verts (reduce_past G x)"
    proof( cases x xa rule: reachable1_cases)
      case nR
      then show ?thesis using anticone.simps in_V by auto 
      next
        case one
        then show ?thesis using reduce_past.simps induce_subgraph_verts past_nodes.simps in_V
          by auto
      next
        case two
        have "is_tip G x" using tips_tips assms(1) by simp
        then have "False" using  tips_not_referenced two by auto
        then show ?thesis by simp
      next
        case eq
        then show ?thesis by auto
      qed
    qed
  next 
    show "{x} \<union> anticone G x \<union> verts (reduce_past G x) \<subseteq> verts G" using digraph.tips_in_verts 
    digraph_axioms anticone_in_verts reduce_past_induced_subgraph induced_subgraph_def
    subgraph_def assms by auto
  qed

lemma (in DAG) verts_comp_dis:
  shows "{x} \<inter> (anticone G x) = {}" 
  and " {x} \<inter> (verts (reduce_past G x)) = {}"
  and "anticone G x \<inter> (verts (reduce_past G x)) = {}"
proof(simp_all, simp add: cycle_free, safe) qed
 
 
lemma (in DAG) verts_size_comp:
  assumes  "x \<in> tips G"
  shows  "card (verts G) = 1 + card (anticone G x) + card (verts (reduce_past G x))"
proof -
  have f1: "finite (verts G)" using finite_verts by simp
  have f2: "finite {x}" by auto
  have f3: "finite (anticone G x)" using anticone.simps by auto
  have f4: "finite (verts (reduce_past G x))" by auto
  have c1: "card {x} + card (anticone G x) = card ({x} \<union> (anticone G x))" using card_Un_disjoint
  verts_comp_dis by auto
  have "({x} \<union> (anticone G x)) \<inter> verts (reduce_past G x) = {}" using verts_comp_dis by auto
  then have " card ({x} \<union> (anticone G x) \<union> verts (reduce_past G x)) 
      = card {x} + card (anticone G x) + card (verts (reduce_past G x))
        " using card_Un_disjoint
    by (metis c1 f2 f3 f4 finite_UnI) 
  moreover have "card (verts G) = card ({x} \<union> (anticone G x) \<union> verts (reduce_past G x))"
    using assms verts_comp by auto
  moreover have "card {x} = 1" by simp
  ultimately show ?thesis using assms verts_comp
    by presburger  
qed

end
