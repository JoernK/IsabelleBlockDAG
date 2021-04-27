(* 
    Author:     Joern Kussmaul
*)

section \<open>DAG\<close>

theory SecondAttempt
  imports Main Graph_Theory.Graph_Theory
begin


locale DAGbased = digraph +
  assumes cycle_free: "(u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v) \<longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  and only_new: "arc e (u,v) \<longrightarrow> \<not>(u \<rightarrow>\<^sup>*\<^bsub>(del_arc e)\<^esub> v)"
  and genesis:  "\<exists>p.\<forall>r. (r \<rightarrow>\<^sup>*\<^bsub>G\<^esub> p)" 

locale transitiveDAGbased = digraph +
  assumes transitive [simp]:
 "u \<rightarrow>\<^bsub>G\<^esub> v \<longleftrightarrow> (u, v) \<in> (arcs_ends G)\<^sup>+"
  and genesis: "\<exists>!u. (v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)" 
(* digraph is loop_free such that transitivity implies cycle-free *)


lemma (in transitiveDAGbased) no_double_edges [simp]: 
"\<lbrakk>u \<rightarrow>\<^bsub>G\<^esub> v\<rbrakk> \<Longrightarrow> \<not>( v \<rightarrow>\<^bsub>G\<^esub> u)"
  by (meson adj_not_same local.transitive reachable_adjI reachable_reachable1_trans)
   

lemma (in DAGbased) no_double_edges [simp]: 
"\<lbrakk>u \<rightarrow>\<^bsub>G\<^esub> v\<rbrakk> \<Longrightarrow> \<not>( v \<rightarrow>\<^bsub>G\<^esub> u)"
  using cycle_free by blast


lemma (in transitiveDAGbased) no_cycles [simp]:
"(u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v) \<Longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  by (meson adj_not_same local.transitive reachable1_reachable_trans) 

definition (in transitiveDAGbased) genesis_node:: "'a \<Rightarrow> bool" where
"genesis_node v \<equiv>  \<forall>u. (u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"

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
  
   
definition (in DAGbased) reduce_past:: "'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past a = \<lparr>verts = past_nodes a, 
  arcs = {b. (b \<in> arcs G  \<and> ((head G b) \<in> past_nodes a) \<and> ((tail G b) \<in> past_nodes a)) }, tail = tail G, 
  head = head G\<rparr>
 "
  
lemma (in DAGbased) reduce_dag:
  assumes "\<not>genesis_node a"
  shows "DAGbased (reduce_past a)"
  nitpick


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


