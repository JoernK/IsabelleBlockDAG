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
  "reduce_past a = \<lparr>verts = past_nodes a, 
  arcs = {b. (b \<in> arcs G  \<and> ((head G b) \<in> past_nodes a) \<and> ((tail G b) \<in> past_nodes a)) }, tail = tail G, 
  head = head G\<rparr>
 "
  
lemma (in DAGbased) reduce_dag:
  assumes " a \<in> verts G"
  assumes "\<not>genesis_node a"
  shows "DAGbased (reduce_past a)"
proof 
  have "finite (verts (reduce_past a))"
    using DAGbased_axioms_def past_nodes_def reduce_past_def by auto
  have "finite (arcs (reduce_past a))"
    using DAGbased_axioms_def past_nodes_def reduce_past_def by auto
  have "\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> tail (reduce_past a) e \<in> verts (reduce_past a)"
    using DAGbased_axioms_def past_nodes_def reduce_past_def by auto
  have "\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> head (reduce_past a) e \<in> verts (reduce_past a)"
    using DAGbased_axioms_def past_nodes_def reduce_past_def by auto
  have "\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> e \<in> arcs G"
    using DAGbased_axioms_def past_nodes_def reduce_past_def by auto
  then have "\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> tail (reduce_past a) e \<noteq> head (reduce_past a) e"
    using past_nodes_def reduce_past_def
    by (metis (no_types, lifting) no_loops pre_digraph.ext_inject pre_digraph.surjective) 
  have " \<And>e1 e2.
       e1 \<in> arcs (reduce_past a) \<Longrightarrow>
       e2 \<in> arcs (reduce_past a) \<Longrightarrow> arc_to_ends (reduce_past a) e1 = arc_to_ends (reduce_past a) e2 \<Longrightarrow> e1 = e2"
    using past_nodes_def reduce_past_def
    by (metis (no_types, lifting) \<open>\<And>e. e \<in> arcs (reduce_past a) \<Longrightarrow> e \<in> arcs G\<close>
        arc_to_ends_def no_multi_arcs pre_digraph.select_convs(3) pre_digraph.select_convs(4)) 
  have " \<And>u v. u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v \<longrightarrow> \<not> v \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> u"
    using digraphI_induced
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


