(* 
    Author:     Joern Kussmaul
*)


theory DAGbased
  imports Main Graph_Theory.Graph_Theory HOL.Order_Relation
begin

section \<open>blockDAG\<close>

locale DAGbased = digraph +
  assumes cycle_free: "(u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v) \<longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  and only_new: "\<forall>e. arc e (u,v) \<longrightarrow> \<not>(u \<rightarrow>\<^sup>*\<^bsub>(del_arc e)\<^esub> v)"
  and genesis:  "\<exists>p.\<forall>r. ((r \<in> verts G \<and> p \<in> verts G) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>G\<^esub> p)"       

definition (in DAGbased) genesis_node:: "'a \<Rightarrow> bool" where
"genesis_node v \<equiv>  \<forall>u. (u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v)"

definition (in DAGbased) direct_past:: "'a \<Rightarrow> 'a set"
  where "direct_past a = {b. (b \<in> verts G \<and> (a,b) \<in> arcs_ends G)}"

definition (in DAGbased) future_nodes:: "'a \<Rightarrow> 'a set"
  where "future_nodes a = {b. (b \<in> verts G \<and> b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) }"

definition (in DAGbased) past_nodes:: "'a \<Rightarrow> 'a set"
  where "past_nodes a = {b. (b \<in> verts G \<and> a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) }"

definition (in DAGbased) reduce_past:: "'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past a \<equiv> induce_subgraph G (past_nodes a)"

lemma (in DAGbased) no_double_edges: 
"u \<rightarrow>\<^bsub>G\<^esub> v \<longrightarrow> \<not>( v \<rightarrow>\<^bsub>G\<^esub> u)"
  using cycle_free by blast  

lemma (in DAGbased) past_nodes_ex:
  assumes "a \<in> verts G"
  shows "a \<notin> past_nodes a"
  using cycle_free past_nodes_def by auto

lemma (in DAGbased) past_nodes_verts: 
  shows "past_nodes a \<subseteq> verts G"
  using past_nodes_def by auto


lemma (in DAGbased) reduce_past_arcs: 
  shows "arcs (reduce_past a) \<subseteq> arcs G"
  using induce_subgraph_arcs reduce_past_def past_nodes_def by auto

lemma (in DAGbased) reduce_past_arcs2:
  "e \<in> arcs (reduce_past a) \<Longrightarrow> e \<in> arcs G"
  using reduce_past_arcs by auto

lemma (in DAGbased) reduce_past_induced_subgraph:
  shows "induced_subgraph (reduce_past a) G"
  using reduce_past_def induced_induce past_nodes_verts by auto

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


lemma del_arc_subgraph:
  assumes "subgraph H G"
  assumes "digraph G \<and> digraph H"
  shows "subgraph (pre_digraph.del_arc H e2) (pre_digraph.del_arc G e2)"
  using subgraph_def pre_digraph.del_arc_simps Diff_iff
proof -
  have f1: "\<forall>p pa. subgraph p pa = ((verts p::'a set) \<subseteq> verts pa \<and> (arcs p::'b set) \<subseteq> arcs pa \<and> 
  wf_digraph pa \<and> wf_digraph p \<and> compatible pa p)"
  using subgraph_def by blast
  have f2: "verts H \<subseteq> verts G \<and> arcs H \<subseteq> arcs G \<and> wf_digraph G \<and> wf_digraph H \<and> compatible G H"
    using assms(1) by blast
  then have "arcs H - {e2} \<subseteq> arcs G - {e2}"
by blast
  then show ?thesis
    using f2 f1 by (simp add: compatible_def pre_digraph.del_arc_simps wf_digraph.wf_digraph_del_arc)
qed


lemma (in DAGbased) reduce_past_pathr:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> v" 
  shows " u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  by (meson assms induced_subgraph_altdef reachable_mono reduce_past_induced_subgraph)

lemma not_reachable_subgraph:
  assumes "subgraph H G"
  shows " \<not> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longrightarrow> \<not> u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v"
  by (meson assms pre_digraph.reachable_mono)

lemma (in DAGbased) reduce_past_dagbased:
  assumes " a \<in> verts G"
  assumes "\<not>genesis_node a"
  shows "DAGbased (reduce_past a)"
  unfolding DAGbased_def
  using digraphI_induced 
proof
  show "induced_subgraph (reduce_past a) G"
    by (simp add: induced_induce past_nodes_verts reduce_past_def)
next  
  show "DAGbased_axioms (reduce_past a)"
  proof 
    fix u v 
    show "u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v \<longrightarrow> \<not> v \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> u"
      by (metis cycle_free past_nodes_verts reachable_mono
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
        assume e_in: "(wf_digraph.arc (reduce_past a) e (u, v))" 
        then have "(wf_digraph.arc G e (u, v))"
          using assms reduce_past_arcs2 reduce_past_def induced_subgraph_def arc_def
        proof -
          have "wf_digraph (reduce_past a)"
            by (metis reduce_past_def subgraph_def subgraph_refl wf_digraph.wellformed_induce_subgraph)
          then have "e \<in> arcs (reduce_past a) \<and> tail (reduce_past a) e = u \<and> head (reduce_past a) e = v"
            by (metis (no_types) \<open>wf_digraph.arc (reduce_past a) e (u, v)\<close> wf_digraph.arcE)
          then show ?thesis
            using arc_def reduce_past_def by auto
        qed    
        then have "\<not> u \<rightarrow>\<^sup>*\<^bsub>del_arc e\<^esub> v"
          using only_new by auto        
        then show "\<not> u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past a) e\<^esub> v"
          by (metis DAGbased.past_nodes_verts DAGbased.reduce_past_def DAGbased_axioms
               del_arc_subgraph digraph.digraph_subgraph digraph_axioms 
               not_reachable_subgraph subgraph_induce_subgraphI)
      qed
    qed
  next
    
    show "\<exists>p. \<forall>r. (r \<in> verts (reduce_past a) \<and> p \<in> verts (reduce_past a)
           \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> p)"
      by (metis DAGbased.past_nodes_ex DAGbased.reduce_past_def
          DAGbased_axioms assms(1) induce_subgraph_verts)
  qed
qed


subsection \<open>Spectre\<close>

locale tie_breakingDAG = DAGbased + 
  fixes r 
  assumes "linear_order_on (verts G) r"

subsection \<open>Basics\<close>
 

definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"

lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)

subsection \<open>Spectre_Definition\<close>

definition (in tie_breakingDAG) tie_break_int:: "'a \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int"
  where "tie_break_int a b i =
 (if i=0 then (if (a,b) \<in> r then 1 else -1) else 
              (if i > 0 then 1 else -1))"

fun (in tie_breakingDAG) sumlist_acc :: "'a \<Rightarrow>'a \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int"
  where "sumlist_acc a b s [] = tie_break_int a b s"
  | "sumlist_acc a b s (x#xs) = sumlist_acc a b (s + x) xs"

fun (in tie_breakingDAG) sumlist :: "'a \<Rightarrow>'a \<Rightarrow> int list \<Rightarrow> int"
  where "sumlist a b s = sumlist_acc a b 0 s"

lemma (in DAGbased) past_future_dis[simp]: "past_nodes a \<inter> future_nodes a = {}"
proof (rule ccontr)
  assume "\<not> past_nodes a \<inter> future_nodes a = {}"
  then show False
    using past_nodes_def future_nodes_def cycle_free reachable1_reachable by blast
qed

lemma (in DAGbased) finite_past[simp]: "finite (past_nodes a)"
  by (metis (full_types) Collect_subset digraphI_induced digraph_def fin_digraph.finite_verts 
past_nodes_def induce_subgraph_verts induced_induce)

lemma (in DAGbased) finite_future[simp]: "finite (future_nodes a)"
  by (metis (full_types) Collect_subset digraphI_induced digraph_def fin_digraph.finite_verts 
future_nodes_def induce_subgraph_verts induced_induce)

function (in tie_breakingDAG)  vote_Spectre:: " ('a,'b) pre_digraph \<Rightarrow>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> int"
  where 
 "vote_Spectre G a b c = 
  (if (a=b) then 1 else 
  (if (a=c) then -1  else
  (if (b=c) then 1 else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c)) then 1  else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b)) then -1  else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c)) then 
   sumlist b c (map (\<lambda>i.
 (vote_Spectre (DAGbased.reduce_past G a) i  b c)) (set_to_list ((direct_past a)))) 
  else sumlist b c (map (\<lambda>i.
   (vote_Spectre G i b c)) (set_to_list (future_nodes a)))))))))"



