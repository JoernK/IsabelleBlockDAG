(* 
    Author:     Joern Kussmaul
*)


theory Codegen
  imports blockDAG Spectre Ghostdag ExtendblockDAG
begin

section \<open>Code Generation\<close>

fun arcAlt::  "('a,'b) pre_digraph \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool"
  where "arcAlt G e uv = (e \<in> arcs G \<and> tail G e = fst uv \<and> head G e = snd uv)"

fun iterate:: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where  "iterate S P = Finite_Set.fold (\<lambda> r A. S r \<and> A) False P "

lemma (in DAG) arcAlt_eq:                     
  shows "arcAlt G e uv = wf_digraph.arc G e uv"
  unfolding arc_def arcAlt.simps by simp
  
lemma [code]: "blockDAG G = (DAG G \<and> ((\<exists> p \<in> verts G. ((\<forall>r \<in> verts G. (r \<rightarrow>\<^sup>+\<^bsub>G\<^esub> p \<or> r = p)))) \<and>
 (\<forall>e \<in> (arcs G). \<forall> u \<in> verts G. \<forall> v \<in> verts G. 
(u \<rightarrow>\<^sup>+\<^bsub>(pre_digraph.del_arc G  e)\<^esub> v) \<longrightarrow> \<not> arcAlt G e (u,v))))" 
  using  DAG.arcAlt_eq  wf_digraph_def DAG.axioms(1)
    digraph.axioms(1) fin_digraph.axioms(1) wf_digraph.arcE blockDAG_axioms_def blockDAG_def 
  by metis
     
lemma [code]: "DAG G = (digraph G \<and> (\<forall>v \<in> verts G. \<not>(v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v)))"
  unfolding DAG_axioms_def DAG_def
  by (metis digraph.axioms(1) fin_digraph.axioms(1) wf_digraph.reachable1_in_verts(1)) 

lemma [code]: "digraph G = (fin_digraph G \<and> loopfree_digraph G \<and> nomulti_digraph G)"
  unfolding digraph_def by auto

lemma [code]: "wf_digraph G = (
 (\<forall>e \<in> arcs G. tail G e \<in> verts G) \<and>
 (\<forall>e \<in> arcs G. head G e \<in> verts G))"
  using wf_digraph_def by auto

lemma [code]: "nomulti_digraph G = (wf_digraph G \<and> 
  (\<forall>e1 \<in> arcs G. \<forall> e2 \<in> arcs G .
     arc_to_ends G e1 = arc_to_ends G e2 \<longrightarrow> e1 = e2))"
  unfolding nomulti_digraph_def nomulti_digraph_axioms_def by auto

lemma [code]: "loopfree_digraph G = (wf_digraph G \<and> (\<forall>e \<in> arcs G.  tail G e \<noteq> head G e))"
  unfolding loopfree_digraph_def loopfree_digraph_axioms_def by auto

lemma [code]: "pre_digraph.del_arc G a =
 \<lparr> verts = verts G, arcs = arcs G - {a}, tail = tail G, head = head G \<rparr>"
  by (simp add: pre_digraph.del_arc_def)


lemma [code]: "fin_digraph G = (wf_digraph G \<and> (card (verts G) > 0 \<or> verts G = {})
   \<and> ((card (arcs G) > 0 \<or> arcs G = {})))" 
  using card_ge_0_finite fin_digraph_def fin_digraph_axioms_def
  by (metis card_gt_0_iff finite.emptyI)


fun vote_Spectre_Int:: "(integer, integer\<times>integer) pre_digraph \<Rightarrow>
 integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer"
  where "vote_Spectre_Int V a b c = integer_of_int (vote_Spectre V a b c)"

fun SpectreOrder_Int:: "(integer, integer\<times>integer) pre_digraph \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> bool"
  where "SpectreOrder_Int G = Spectre_Order G"

fun OrderDAG_Int::  "(integer, integer\<times>integer) pre_digraph \<Rightarrow>
 integer \<Rightarrow> (integer set \<times> integer list)" 
 where " OrderDAG_Int V a =  (OrderDAG V (nat_of_integer a))"
 

export_code top_sort anticone set blockDAG pre_digraph_ext snd fst vote_Spectre_Int
 SpectreOrder_Int OrderDAG_Int
 in Haskell module_name DAGS file "code/" 

notepad begin
  let ?G = "\<lparr>verts = {1::int,2,3,4,5,6,7,8,9,10}, arcs = {(2,1),(3,1),(4,1),
  (5,2),(6,3),(7,4),(8,5),(8,3),(9,6),(9,4),(10,7),(10,2)}, tail = fst, head = snd\<rparr>"
  let ?a = "2"
  let ?b = "3"
  let ?c = "4"
  value "blockDAG ?G"
  value "Spectre_Order ?G ?a ?b \<and> Spectre_Order ?G ?b ?c \<and> \<not> Spectre_Order ?G ?a ?c"
end


subsection \<open>Extend Graph\<close>

  
declare  pre_digraph.del_vert_def [code]
declare Append_One_axioms_def [code] 
declare Honest_Append_One_axioms_def[code] 
declare Append_One_def [code] 
declare Honest_Append_One_def [code] 
declare Append_One_Honest_Dishonest_axioms_def [code]
declare Append_One_Honest_Dishonest_def [code]




end
