(* 
    Author:     Joern Kussmaul
*)

section \<open>blockDAG\<close>

theory DAGbased
  imports Main Graph_Theory.Graph_Theory HOL.Order_Relation
begin


locale DAGbased = digraph +
  assumes cycle_free: "(u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v) \<longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  and only_new: "\<forall>e. arc e (u,v) \<longrightarrow> \<not>(u \<rightarrow>\<^sup>*\<^bsub>(del_arc e)\<^esub> v)"
  and genesis:  "\<exists>p.\<forall>r. (r \<in> verts G \<and> p \<in> verts G) \<Longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>G\<^esub> p" 

lemma (in DAGbased) no_double_edges: 
"u \<rightarrow>\<^bsub>G\<^esub> v \<longrightarrow> \<not>( v \<rightarrow>\<^bsub>G\<^esub> u)"
  using cycle_free by blast        

definition (in DAGbased) genesis_node:: "'a \<Rightarrow> bool" where
"genesis_node v \<equiv>  \<forall>u. (u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"

locale tie_breakingDAG = DAGbased + 
  fixes r 
  assumes "linear_order_on (verts G) r"

definition (in DAGbased) past_nodes:: "'a \<Rightarrow> 'a set"
  where 
  "past_nodes a = {b. (b \<in> verts G \<and> a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) }"

lemma (in DAGbased) a_not_in_past:
  assumes "a \<in> verts G"
  shows "a \<notin> past_nodes a"
proof(rule ccontr)
  assume "\<not> ?thesis"
  then have "a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a"
    using local.past_nodes_def by auto
  then show "False"
    using cycle_free by auto
qed

lemma (in DAGbased) past_subset: 
  shows "past_nodes a \<subseteq> verts G"
  using past_nodes_def by auto

definition (in DAGbased) reduce_past:: "'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past a \<equiv> induce_subgraph G (past_nodes a)"

lemma (in DAGbased) reduce_past_subarcs:
  "e \<in> arcs (reduce_past a) \<Longrightarrow> e \<in> arcs G"
  using DAGbased_axioms_def past_nodes_def reduce_past_def by auto

lemma (in DAGbased) reduce_subgraph:
  shows "induced_subgraph (reduce_past a) G"
  using reduce_past_def induced_induce past_subset by auto


lemma (in DAGbased) induced_subgraph_del_arcs:
  shows "(pre_digraph.del_arc (reduce_past a) e) = (DAGbased.reduce_past (del_arc e) a)"
proof -
  consider (part) "e \<in> arcs(reduce_past a)" | (not_part) "e \<notin> arcs(reduce_past a)" by auto
  then show ?thesis
  proof cases
    case not_part then show ?thesis
      using reduce_past_def del_arc_simps pre_digraph.equality 
      oops


lemma (in DAGbased) reduce_past_path:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v" 
  shows " u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v"
  using assms
proof induct
  case base then show ?case
    by (metis dominates_induce_subgraphD r_into_trancl' reduce_past_def)
next case (step u v) show ?case
    by (metis dominates_induce_subgraphD reduce_past_def step.hyps(2)
        step.hyps(3) step.prems trancl.trancl_into_trancl) 
qed

lemma (in DAGbased) reduce_dag:
  assumes " a \<in> verts G"
  assumes "\<not>genesis_node a"
  shows "DAGbased (reduce_past a)"
  unfolding DAGbased_def
  using digraphI_induced 
proof
  show "induced_subgraph (reduce_past a) G"
    by (simp add: induced_induce past_subset reduce_past_def)
next  
  show "DAGbased_axioms (reduce_past a)"
  proof 
    fix u v 
    show "u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v \<longrightarrow> \<not> v \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> u"
      by (metis cycle_free past_subset reachable_mono
          reduce_past_def reduce_past_path subgraph_induce_subgraphI)
  next 
    fix u v 
    show " \<forall>e. wf_digraph.arc (reduce_past a) e (u, v) \<longrightarrow>
               \<not> u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past a) e\<^esub> v"
    proof
      fix e
      show "wf_digraph.arc (reduce_past a) e (u, v) \<longrightarrow>
               \<not> u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past a) e\<^esub> v"
      proof
        assume "(wf_digraph.arc (reduce_past a) e (u, v))" 
        then have "(wf_digraph.arc G e (u, v))"
          using arc_def reduce_past_subarcs reduce_past_def subgraph_def
        proof -
          have "e \<in> arcs (reduce_past a) \<and> tail (reduce_past a) e = u \<and> head (reduce_past a) e = v"
            by (metis (no_types) \<open>wf_digraph.arc (reduce_past a) e (u, v)\<close> reduce_past_def wf_digraph.arcE wf_digraph.wellformed_induce_subgraph wf_digraph_axioms)
          then show ?thesis
            by (simp add: arc_def reduce_past_def)
        qed
        then have "\<not> u \<rightarrow>\<^sup>*\<^bsub>del_arc e\<^esub> v"
          using only_new by auto 
        then show "\<not> u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past a) e\<^esub> v"
          oops  
          


definition (in tie_breakingDAG) simple_vote:: "'a \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> bool"
  where "simple_vote a b i =
 (if i=0 then (if (a,b) \<in> r then True else False) else (i > 0))"
 

fun (in tie_breakingDAG) sum_bool :: " bool list \<Rightarrow> int"
  where "sum_bool [] = 0"
  | "sum_bool (x#xs) = (if x then 1 else -1) + sum_bool xs"


 

function (in DAGbased) vote_Spectre:: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where 
  "vote_Spectre a b c = 
  (if (a=b) then True else 
  (if (a=c) then False else
  (if (b=c) then True else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) & \<not>(a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c)) then True else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c) & \<not>(a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b)) then False else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) & (a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c)) then  False
  else False))))))"
  by auto

termination 
  

