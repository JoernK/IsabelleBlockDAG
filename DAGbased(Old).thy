(* 
    Author:     Joern Kussmaul
*)


theory DAGbased
  imports Main Graph_Theory.Graph_Theory PSL.PSL
begin

section \<open>blockDAG\<close>



locale DAG = digraph +
  assumes cycle_free: "\<not>(v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v)"
  


locale blockDAG = DAG  +
  assumes only_new: "\<forall>e. arc e (u,v) \<longrightarrow> \<not>(u \<rightarrow>\<^sup>*\<^bsub>(del_arc e)\<^esub> v)"
  and genesis:  "\<exists>p. (p\<in> verts G \<and> (\<forall>r. r \<in> verts G  \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>G\<^esub> p))"       

locale tie_breakingDAG = blockDAG +
  fixes r 
  assumes "linear_order_on (verts G) r"

fun set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"

lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list.simps by (metis (mono_tags) finite_list some_eq_ex)

fun (in blockDAG) direct_past:: "'a \<Rightarrow> 'a set"
  where "direct_past a = {b. (b \<in> verts G \<and> (a,b) \<in> arcs_ends G)}"

fun (in blockDAG) future_nodes:: "'a \<Rightarrow> 'a set"
  where "future_nodes a = {b. (b \<in> verts G \<and> b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) }"

fun (in blockDAG) past_nodes:: "'a \<Rightarrow> 'a set"
  where "past_nodes a = {b. (b \<in> verts G \<and> a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) }"

fun (in blockDAG) reduce_past:: "'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past a = induce_subgraph G (past_nodes a)"
                                       
fun (in blockDAG) iterate_nodes:: "('a \<Rightarrow> bool) \<Rightarrow> 'a list\<Rightarrow> bool"
  where "iterate_nodes f [] = True" 
  | "iterate_nodes f (x#xs) = (f x \<and> (iterate_nodes f xs))"

lemma (in blockDAG) iterate_all:  "iterate_nodes p a \<longleftrightarrow> (\<forall>x. (x \<in>  set a) \<longrightarrow> p x)"
  by (induct a) auto    

fun (in blockDAG) is_tip:: " 'a \<Rightarrow> bool"
  where "is_tip a = ((a \<in> verts G) \<and> iterate_nodes (\<lambda>x. \<not> x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) (set_to_list (verts G)))"

fun (in blockDAG) tips:: "('a,'b) pre_digraph \<Rightarrow>'a set"
  where "tips V = {v. blockDAG.is_tip V v}"

fun (in blockDAG) is_genesis_node:: "'a \<Rightarrow> bool" where
"is_genesis_node v = ((v \<in> verts G) \<and> (iterate_nodes (\<lambda>x. x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v) (set_to_list (verts G))))"


lemma (in blockDAG) genesisAlt :
 "(is_genesis_node a) \<longleftrightarrow> ((a \<in> verts G) \<and> (\<forall>r.  (r \<in> verts G) \<longrightarrow> r \<rightarrow>\<^sup>* a))"
  using is_genesis_node.simps iterate_all set_set_to_list finite_verts
  by (metis (mono_tags, lifting)) 
  
lemma (in blockDAG) genesis_existAlt:
  "\<exists>a. is_genesis_node a"
  using genesis genesisAlt blockDAG_axioms_def by presburger 

fun (in blockDAG) genesis_node:: "('a,'b) pre_digraph \<Rightarrow> 'a"
  where "genesis_node V = (SOME x. blockDAG.is_genesis_node V x)"

lemma (in blockDAG) unique_genesis: "is_genesis_node a \<and> is_genesis_node b \<longrightarrow> a = b"
proof(rule ccontr)
  assume c: "\<not>?thesis"
  then show "False"
  proof -
    have "\<exists> a b. is_genesis_node a \<and> is_genesis_node b \<and> \<not>a = b"
      using c by auto
    then have "\<exists>a. a \<rightarrow>\<^sup>+ a"
      using genesisAlt iterate_all reachable_trans 
            reachable_refl reachable_reachable1_trans reachable_neq_reachable1
      by (metis (full_types)) 
    then show False
      using cycle_free by auto
  qed
qed

lemma (in blockDAG) unidirectional:
"u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
using cycle_free reachable1_reachable_trans by auto

lemma (in blockDAG) past_nodes_ex:
  assumes "a \<in> verts G"
  shows "a \<notin> past_nodes a"
  using cycle_free past_nodes.simps by auto

lemma (in blockDAG) past_nodes_verts: 
  shows "past_nodes a \<subseteq> verts G"
  using past_nodes.simps by auto


lemma (in blockDAG) reduce_past_arcs: 
  shows "arcs (reduce_past a) \<subseteq> arcs G"
  using induce_subgraph_arcs past_nodes.simps by auto

lemma (in blockDAG) reduce_past_arcs2:
  "e \<in> arcs (reduce_past a) \<Longrightarrow> e \<in> arcs G"
  using reduce_past_arcs by auto

lemma (in blockDAG) reduce_past_induced_subgraph:
  shows "induced_subgraph (reduce_past a) G"
  using  induced_induce past_nodes_verts by auto

lemma (in blockDAG) reduce_past_path:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>reduce_past a\<^esub> v" 
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


lemma (in blockDAG) reduce_past_pathr:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> v" 
  shows " u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  by (meson assms induced_subgraph_altdef reachable_mono reduce_past_induced_subgraph)

lemma not_reachable_subgraph:
  assumes "subgraph H G"
  shows " \<not> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longrightarrow> \<not> u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v"
  by (meson assms pre_digraph.reachable_mono)

lemma (in blockDAG) reduce_past_not_empty:
  assumes " a \<in> verts G"
  and  "\<not>is_genesis_node a"
shows "(verts (reduce_past a)) \<noteq> {}"
proof -
  obtain g
    where gen: "is_genesis_node g" using genesis_existAlt by auto
  have ex: "g \<in> verts (reduce_past a)" using reduce_past.simps past_nodes.simps 
genesisAlt reachable_neq_reachable1 reachable_reachable1_trans gen assms(1) assms(2) by auto 
  then show "(verts (reduce_past a)) \<noteq> {}" using ex by auto                                                                                           
qed

lemma (in blockDAG) k:
  fixes a 
  assumes "G =  \<lparr>verts = {a}, arcs = {}, tail=t,  head=h\<rparr>"
  assumes "blockDAG G"
  shows "blockDAG.is_genesis_node G a"
  unfolding genesisAlt
proof safe
  have "verts G = {a}"
      using assms(1) by auto
    then show "a \<in> verts G" by auto
  next
    fix r 
    show "r \<in> verts G \<Longrightarrow> r \<rightarrow>\<^sup>* a"
    proof -
      assume "r \<in> verts G" 
      then have "r = a" using assms(1) by auto
      then show " r \<in> verts G \<Longrightarrow> r \<rightarrow>\<^sup>* a "  using reachable_refl by simp       
    qed
  qed


lemma (in blockDAG) reduce_past_dagbased:
  assumes "blockDAG G"
  assumes " a \<in> verts G"
  and "\<not>is_genesis_node a"
  shows "blockDAG (reduce_past a)"
  unfolding blockDAG_def DAG_def
  
proof safe
  show "digraph (reduce_past a)"
    using digraphI_induced reduce_past_induced_subgraph by auto  
next
  show "DAG_axioms (reduce_past a)"
    unfolding DAG_axioms_def
    using cycle_free reduce_past_path by metis 
next
  show "blockDAG_axioms (reduce_past a)"
  unfolding blockDAG_axioms_def
  proof safe
    fix u v e 
    assume arc: "wf_digraph.arc (reduce_past a) e (u, v)"
    then show " u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past a) e\<^esub> v \<Longrightarrow> False "
    proof -
        assume e_in: "(wf_digraph.arc (reduce_past a) e (u, v))" 
        then have "(wf_digraph.arc G e (u, v))"
          using assms reduce_past_arcs2 induced_subgraph_def arc_def 
        proof -
          have "wf_digraph (reduce_past a)"
            using reduce_past.simps subgraph_def subgraph_refl wf_digraph.wellformed_induce_subgraph
            by metis
          then have "e \<in> arcs (reduce_past a) \<and> tail (reduce_past a) e = u
                     \<and> head (reduce_past a) e = v"
            using  arc wf_digraph.arcE
            by metis 
          then show ?thesis
            using arc_def reduce_past.simps by auto
        qed    
        then have "\<not> u \<rightarrow>\<^sup>*\<^bsub>del_arc e\<^esub> v"
          using only_new by auto        
        then show "u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past a) e\<^esub> v \<Longrightarrow> False"
          using blockDAG.past_nodes_verts blockDAG.reduce_past.simps blockDAG_axioms
               del_arc_subgraph digraph.digraph_subgraph digraph_axioms 
               not_reachable_subgraph subgraph_induce_subgraphI
          by metis
      qed
    next 
      show
      "\<exists>p. p \<in> verts (reduce_past a) \<and> (\<forall>r. r \<in> verts (reduce_past a) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> p)"
      proof -
        obtain p where gen: "is_genesis_node p" using genesis_existAlt by auto
        have p: "p \<in> verts (reduce_past a) \<and> (\<forall>r. r \<in> verts (reduce_past a) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> p)"
        proof 
          show "p \<in> verts (reduce_past a)" using genesisAlt induce_reachable_preserves_paths
            reduce_past.simps past_nodes.simps reachable1_reachable induce_subgraph_verts assms(2)
            assms(3) gen mem_Collect_eq reachable_neq_reachable1
            by (metis (no_types, lifting)) 
            
        next    
          show "\<forall>r. r \<in> verts (reduce_past a) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> p" 
          proof safe
            fix r a
            assume in_past: "r \<in> verts (reduce_past a)"
            then have con: "r \<rightarrow>\<^sup>* p" using gen genesisAlt by simp  
            then show "r \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> p"
            proof -
            have f1: "r \<in> verts G \<and> a \<rightarrow>\<^sup>+ r"
            using in_past by force
            obtain aaa :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
            f2: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (aaa x0 x1 \<in> x1 \<and> aaa x0 x1 \<notin> x0)"
              by moura
            have "r \<rightarrow>\<^sup>* aaa (past_nodes a) (Collect (reachable G r))
                  \<longrightarrow> a \<rightarrow>\<^sup>+ aaa (past_nodes a) (Collect (reachable G r))"
                using f1 by (meson reachable1_reachable_trans)
              then have "aaa (past_nodes a) (Collect (reachable G r)) \<notin> Collect (reachable G r)
                         \<or> aaa (past_nodes a) (Collect (reachable G r)) \<in> past_nodes a"
                by (simp add: reachable_in_verts(2))
              then have "Collect (reachable G r) \<subseteq> past_nodes a"
                using f2 by (meson subsetI)
              then show ?thesis
                using con  induce_reachable_preserves_paths reachable_induce_ss reduce_past.simps
            by (metis (no_types))
            qed
          qed
        qed
        show 
        "\<exists>p. p \<in> verts (reduce_past a) \<and> (\<forall>r. r \<in> verts (reduce_past a) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> p)"
          using p by auto
      qed
    qed
  qed

(*
lemma (in blockDAG) reduce_past_gen:
  assumes "\<not>is_genesis_node a" 
  and "a \<in> verts G"
shows "blockDAG.is_genesis_node G b \<longleftrightarrow> blockDAG.is_genesis_node (reduce_past a) b"
proof safe
  fix a b
  show "is_genesis_node b \<Longrightarrow> blockDAG.is_genesis_node (reduce_past a) b"
*)
  

subsection \<open>Spectre\<close>


subsection \<open>Basics\<close>
 


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

lemma (in blockDAG) past_future_dis[simp]: "past_nodes a \<inter> future_nodes a = {}"
proof (rule ccontr)
  assume "\<not> past_nodes a \<inter> future_nodes a = {}"
  then show False
    using past_nodes.simps future_nodes.simps unidirectional reachable1_reachable by blast
qed

lemma (in blockDAG) finite_past: "finite (past_nodes a)"
  by (metis (full_types) Collect_subset digraphI_induced digraph_def fin_digraph.finite_verts 
past_nodes.simps induce_subgraph_verts induced_induce)

lemma (in blockDAG) finite_future: "finite (future_nodes a)"
  by (metis (full_types) Collect_subset digraphI_induced digraph_def fin_digraph.finite_verts 
future_nodes.simps induce_subgraph_verts induced_induce)

function (in tie_breakingDAG) vote_Spectre:: " ('a,'b) pre_digraph \<Rightarrow>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> int" 
 where
 "vote_Spectre V a b c = 
  (if (a=b) then 1 else 
  (if (a=c) then -1  else
  (if (b=c) then 1 else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 1  else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b)) then -1  else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 
   sumlist b c (map (\<lambda>i.
 (vote_Spectre (blockDAG.reduce_past V a) i  b c)) (set_to_list ((direct_past a)))) 
  else sumlist b c (map (\<lambda>i.
   (vote_Spectre V i b c)) (set_to_list (future_nodes a)))))))))"
  by auto

export_code tie_breakingDAG.vote_Spectre in Haskell module_name SPECTRE

end