(* 
    Author:     Joern Kussmaul
*)

section \<open>blockDAG\<close>

theory DAGbased
  imports Main Graph_Theory.Graph_Theory
begin


locale DAGbased = digraph +
  assumes cycle_free: "(u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v) \<longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  and only_new: "arc e (u,v) \<longrightarrow> \<not>(u \<rightarrow>\<^sup>*\<^bsub>(del_arc e)\<^esub> v)"
  and genesis:  "\<exists>p.\<forall>r. (r \<in> verts G \<and> p \<in> verts G) \<Longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>G\<^esub> p" 

lemma (in DAGbased) no_double_edges [simp]: 
"\<lbrakk>u \<rightarrow>\<^bsub>G\<^esub> v\<rbrakk> \<Longrightarrow> \<not>( v \<rightarrow>\<^bsub>G\<^esub> u)"
  using cycle_free by blast

definition (in DAGbased) genesis_node:: "'a \<Rightarrow> bool" where
"genesis_node v \<equiv>  \<forall>u. (u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"

locale tie_breakingDAG = DAGbased + 
  fixes tie_break :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes asymmetric: "(a \<noteq> b) \<Longrightarrow> tie_break a b \<equiv> \<not> (tie_break b a)"
  assumes transitive: "tie_break a b & tie_break b c \<Longrightarrow> tie_break a c"

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
  
definition (in DAGbased) reduce_past:: "'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past a = induce_subgraph G (past_nodes a)"

lemma (in DAGbased) reduce_past_subarcs:
  "\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> e \<in> arcs G"
  using DAGbased_axioms_def past_nodes_def reduce_past_def by auto

lemma (in DAGbased) reduce_past_path:
  "\<And>u v. u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v \<Longrightarrow> u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v"
  using past_nodes_def reduce_past_def
  by (smt (verit, ccfv_threshold) adj_not_same cycle_free 
      dominates_induce_subgraphD reachable_adjI 
      reachable_neq_reachable1 reachable_trans
      rtrancl_trancl_trancl tranclD trancl_trans_induct)

lemma (in DAGbased) reduce_dag:
  assumes " a \<in> verts G"
  assumes "\<not>genesis_node a"
  shows "DAGbased (reduce_past a)"
proof 
  show "finite (verts (reduce_past a))"
    using DAGbased_axioms_def past_nodes_def reduce_past_def by auto
  next
  show "finite (arcs (reduce_past a))"
    using DAGbased_axioms_def past_nodes_def reduce_past_def by auto
  next
  show "\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> tail (reduce_past a) e \<in> verts (reduce_past a)"
    using DAGbased_axioms_def past_nodes_def reduce_past_def by auto
  next
  show "\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> head (reduce_past a) e \<in> verts (reduce_past a)"
    using DAGbased_axioms_def past_nodes_def reduce_past_def by auto
  next
  show "\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> tail (reduce_past a) e \<noteq> head (reduce_past a) e"
    using past_nodes_def reduce_past_def reduce_past_subarcs
    by (metis induce_subgraph_head induce_subgraph_tail no_loops) 
  next
  show "\<And>e1 e2.
       e1 \<in> arcs (reduce_past a) \<Longrightarrow>
       e2 \<in> arcs (reduce_past a) \<Longrightarrow>
       arc_to_ends (reduce_past a) e1 = arc_to_ends (reduce_past a) e2 \<Longrightarrow> e1 = e2"
    using past_nodes_def reduce_past_def reduce_past_subarcs
     by (metis \<open>\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> e \<in> arcs G\<close> induce_subgraph_ends no_multi_arcs)
 next 
   show "\<And>u v. u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v \<longrightarrow> \<not> v \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> u"
   proof 
     fix a u v 
     assume "u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v"
       have "u \<rightarrow>\<^sup>+ v"
         by (smt (z3) \<open>u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v\<close> adj_in_verts(2) adj_not_same dominates_induce_subgraphD reachable_adjI reachable_conv' reachable_neq_reachable1 reachable_trans reduce_past_def rtrancl_trancl_trancl tranclD trancl_rtrancl_trancl trancl_trans_induct)
       then have "\<not>v \<rightarrow>\<^sup>* u"
         using cycle_free
         by auto
     then show "\<not> v \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> u"
       using reduce_past_path
       by (meson \<open>u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v\<close> cycle_free reachable1_in_verts(1)
           reachable_refl reachable_rtranclI trancl_rtrancl_trancl)
   qed
 next
   show "\<And>e u v.
       wf_digraph.arc (reduce_past a) e (u, v) \<longrightarrow>
       \<not> u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past a) e\<^esub> v"
   proof 
     fix e u v
     assume "wf_digraph.arc (reduce_past a) e (u, v)"
     then show "\<not> u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past a) e\<^esub> v"
       oops        
    
   
  
definition (in tie_breakingDAG) simple_vote:: "'a \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> bool" 
  where "simple_vote a b i = (if i=0 then (tie_break a b) else (i > 0))"
 

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


