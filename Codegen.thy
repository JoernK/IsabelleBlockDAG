(* 
    Author:     Joern Kussmaul
*)


theory Codegen
  imports blockDAG Spectre
begin

section \<open>Code Generation\<close>

fun arcAlt::  "('a,'b) pre_digraph \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool"
  where "arcAlt G e uv = (e \<in> arcs G \<and> tail G e = fst uv \<and> head G e = snd uv)"

lemma (in DAG) arcAlt_eq:
  shows "arcAlt G e uv = wf_digraph.arc G e uv"
  unfolding arc_def arcAlt.simps by simp
  
lemma [code]: "blockDAG G = ((\<exists>p. (p\<in> verts G \<and> (\<forall>r. r \<in> verts G  \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>G\<^esub> p))) \<and>
 (\<forall>e u v. arcAlt G e (u,v) \<longrightarrow> \<not>(u \<rightarrow>\<^sup>*\<^bsub>(pre_digraph.del_arc G  e)\<^esub> v)) \<and> DAG G)"
  unfolding blockDAG_axioms_def blockDAG_def
  using DAG.arcAlt_eq by metis

lemma [code]: "DAG G = (digraph G \<and> (\<forall>v. \<not>(v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v)))"
  unfolding DAG_axioms_def DAG_def by auto

lemma [code]: "digraph G = (fin_digraph G \<and> loopfree_digraph G \<and> nomulti_digraph G)"
  unfolding digraph_def by auto
                
lemma [code]: "fin_digraph G =  (wf_digraph G \<and> finite (verts G) \<and> finite (arcs G))"
  unfolding fin_digraph_axioms_def fin_digraph_def by simp

lemma [code]: "wf_digraph G = (
 (\<forall>e.   e \<in> arcs G \<longrightarrow> tail G e \<in> verts G) \<and>
 (\<forall>e. e \<in> arcs G \<longrightarrow> head G e \<in> verts G))"
  using wf_digraph_def by auto

lemma [code]: "nomulti_digraph G = (wf_digraph G \<and> 
  (\<forall>e1 e2. e1 \<in> arcs G \<and> e2 \<in> arcs G \<and>
     arc_to_ends G e1 = arc_to_ends G e2 \<longrightarrow> e1 = e2))"
  unfolding nomulti_digraph_def nomulti_digraph_axioms_def by auto

lemma [code]: "loopfree_digraph G = (wf_digraph G \<and> (\<forall>e.  e \<in> arcs G \<longrightarrow> tail G e \<noteq> head G e))"
  unfolding loopfree_digraph_def loopfree_digraph_axioms_def by auto

lemma [code]: "pre_digraph.del_arc G a =
 \<lparr> verts = verts G, arcs = arcs G - {a}, tail = tail G, head = head G \<rparr>"
  by (simp add: pre_digraph.del_arc_def)

(**DAG.future_nodes, DAG.reduce_past, DAG.past_nodes
**)

fun future_nodesAlt:: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set" 
  where "future_nodesAlt G a = {b. b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a}"

declare rtrancl_on_def [code]
declare rtrancl_onp.simps [code]

export_code vote_Spectre in Haskell module_name Spectre
end
