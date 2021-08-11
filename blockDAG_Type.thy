(* 
    Author:     Joern Kussmaul
*)

theory blockDAG_Type      
  imports blockDAG 
begin

typedef ('a,'b) BlockDAG = "{x. blockDAG x}::('a,'b) pre_digraph set"
  morphisms BlockDAG pre_digraph_ext
proof
  fix a::'a
  let ?x = "\<lparr>verts = {a}, arcs = {}, tail = \<lambda>x. a, head =  \<lambda>x. a\<rparr>" 
  have "blockDAG ?x" unfolding blockDAG_def blockDAG_axioms_def DAG_def DAG_axioms_def 
  digraph_def loopfree_digraph_def loopfree_digraph_axioms_def nomulti_digraph_def 
  nomulti_digraph_axioms_def wf_digraph_def fin_digraph_def fin_digraph_axioms_def 
  pre_digraph.del_arc_simps
  proof(safe,simp_all, simp add: arcs_ends_def)
    fix u::'a fix  v::'a fix e::'d
    have "\<not>  u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc ?x e\<^esub> v " 
      by (simp add: arcs_ends_def pre_digraph.del_arc_in) 
    then show "u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc ?x e\<^esub> v 
    \<Longrightarrow> wf_digraph.arc ?x e (u, v) \<Longrightarrow> False" by auto
  qed
  then show "?x \<in> {x. blockDAG x}" by simp
qed

declare [[coercion BlockDAG]]

lemma
  "blockDAG (A::('a,'b) BlockDAG)" using BlockDAG by auto

end