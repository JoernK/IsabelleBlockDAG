theory TransitiveDAG
  imports Main Graph_Theory.Graph_Theory
begin


locale transitiveDAGbased = digraph +
  assumes transitive [simp]:
 "u \<rightarrow>\<^bsub>G\<^esub> v \<longleftrightarrow> (u, v) \<in> (arcs_ends G)\<^sup>+"
  and genesis: "\<exists>!u. (v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)" 
(* digraph is loop_free such that transitivity implies cycle-free *)


lemma (in transitiveDAGbased) no_double_edges [simp]: 
"\<lbrakk>u \<rightarrow>\<^bsub>G\<^esub> v\<rbrakk> \<Longrightarrow> \<not>( v \<rightarrow>\<^bsub>G\<^esub> u)"
  by (meson adj_not_same local.transitive reachable_adjI reachable_reachable1_trans)
   

lemma (in transitiveDAGbased) no_cycles [simp]:
"(u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v) \<Longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  by (meson adj_not_same local.transitive reachable1_reachable_trans) 

definition (in transitiveDAGbased) genesis_node:: "'a \<Rightarrow> bool" where
"genesis_node v \<equiv>  \<forall>u. (u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"



