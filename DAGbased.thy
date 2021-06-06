(* 
    Author:     Joern Kussmaul
*)


theory DAGbased
  imports Main Graph_Theory.Graph_Theory
begin

section \<open>Digraph.Components\<close>

lemma graph_equality:
  assumes "digraph A \<and> digraph B"
  shows "(A = B) \<longleftrightarrow>
 (verts A = verts B) \<and> (arcs A = arcs B) \<and>
 (tail A = tail B) \<and> (head A = head B)"
  by auto


lemma not_reachable_subgraph:
  assumes "subgraph H G"
  shows " \<not> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longrightarrow> \<not> u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v"
  by (meson assms pre_digraph.reachable_mono)

lemma del_arc_subgraph:
  assumes "subgraph H G"
  assumes "digraph G \<and> digraph H"
  shows "subgraph (pre_digraph.del_arc H e2) (pre_digraph.del_arc G e2)"
  using subgraph_def pre_digraph.del_arc_simps Diff_iff
proof -
  have f1: "\<forall>p pa. subgraph p pa = ((verts p::'a set) \<subseteq> verts pa \<and> (arcs p::'b set) \<subseteq> arcs pa \<and> 
  wf_digraph pa \<and> wf_digraph p \<and> compatible pa p)"
  using subgraph_def by blast
  have "arcs H - {e2} \<subseteq> arcs G - {e2}" using assms(1)
    by auto
  then show ?thesis
    unfolding subgraph_def 
    using f1 assms(1) by (simp add: compatible_def pre_digraph.del_arc_simps wf_digraph.wf_digraph_del_arc)
qed

lemma graph_nat_induct[consumes 1, case_names base step]: 
  assumes
 major: "digraph Z" and
 cases: "\<And>V. (digraph V \<Longrightarrow> card (verts V) = 0 \<Longrightarrow> P V)"
  "\<And>V c. ((digraph V \<Longrightarrow> card (verts V) = c \<Longrightarrow> P V) 
  \<Longrightarrow> (digraph V \<Longrightarrow> card (verts V) = (Suc c) \<Longrightarrow> P V))"
shows "P Z"
  by (metis (full_types) list_decode.cases
  cases(1) cases(2) major n_not_Suc_n) 

section \<open>Utils\<close>

(**
fun set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. set l = s)"
lemma  set_set_to_list:
   "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list.simps by (metis (mono_tags) finite_list some_eq_ex)
**)
section \<open>blockDAGs\<close>

subsection  \<open>Definitions\<close>
 
locale DAG = digraph +
  assumes cycle_free: "\<not>(v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v)"

locale blockDAG = DAG  +
  assumes only_new: "\<forall>e. arc e (u,v) \<longrightarrow> \<not>(u \<rightarrow>\<^sup>*\<^bsub>(del_arc e)\<^esub> v)"
  and genesis:  "\<exists>p. (p\<in> verts G \<and> (\<forall>r. r \<in> verts G  \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>G\<^esub> p))"       

locale tie_breakingDAG = 
  fixes G::"('c::linorder,'b) pre_digraph"
  assumes "blockDAG G"
  


subsection  \<open>Functions\<close>

fun (in                                                 
blockDAG) direct_past:: "'a \<Rightarrow> 'a set"
  where "direct_past a = {b. (b \<in> verts G \<and> (a,b) \<in> arcs_ends G)}"

fun (in blockDAG) future_nodes:: "'a \<Rightarrow> 'a set"
  where "future_nodes a = {b. (b \<in> verts G \<and> b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) }"

fun (in blockDAG) past_nodes:: "'a \<Rightarrow> 'a set"
  where "past_nodes a = {b. a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b}"

fun (in blockDAG) past_nodes_refl :: "'a \<Rightarrow> 'a set"
  where "past_nodes_refl a = {b. a \<rightarrow>\<^sup>*\<^bsub>G\<^esub> b}"

fun (in blockDAG) reduce_past:: "'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past a = induce_subgraph G (past_nodes a)"

fun (in blockDAG) reduce_past_refl:: "'a \<Rightarrow> ('a,'b) pre_digraph"
  where 
  "reduce_past_refl a = induce_subgraph G (past_nodes_refl a)"
                                          
fun (in blockDAG) is_tip:: " 'a \<Rightarrow> bool"
  where "is_tip a = ((a \<in> verts G) \<and>  (ALL x. \<not> x \<rightarrow>\<^sup>+ a))"

fun (in blockDAG) tips:: "('a,'b) pre_digraph \<Rightarrow>'a set"
  where "tips V = {v. blockDAG.is_tip V v}"

fun (in blockDAG) is_genesis_node :: "'a \<Rightarrow> bool" where
"is_genesis_node v = ((v \<in> verts G) \<and> (ALL x. (x \<in> verts G) \<longrightarrow>  x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v))"

definition (in blockDAG) genesis_node:: "'a"
  where "genesis_node = (SOME x. is_genesis_node x)"


subsection \<open>Lemmas\<close>


lemma (in blockDAG) unidirectional:
"u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<longrightarrow> \<not>( v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> u)"
  using cycle_free reachable1_reachable_trans by auto

subsection \<open>Genesis\<close>

lemma (in blockDAG) genesisAlt :
 "(is_genesis_node a) \<longleftrightarrow> ((a \<in> verts G) \<and> (\<forall>r.  (r \<in> verts G) \<longrightarrow> r \<rightarrow>\<^sup>* a))"
  by simp
  
lemma (in blockDAG) genesis_existAlt:
  "\<exists>a. is_genesis_node a"
  using genesis genesisAlt blockDAG_axioms_def by presburger 

lemma (in blockDAG) unique_genesis: "is_genesis_node a \<and> is_genesis_node b \<longrightarrow> a = b"
proof(rule ccontr)
  assume c: "\<not>?thesis"
  then show "False"
  proof -
    have "\<exists> a b. is_genesis_node a \<and> is_genesis_node b \<and> \<not>a = b"
      using c by auto
    then have "\<exists>a. a \<rightarrow>\<^sup>+ a"
      using genesisAlt reachable_trans 
            reachable_refl reachable_reachable1_trans reachable_neq_reachable1
      by (metis (full_types)) 
    then show False
      using cycle_free by auto
  qed
qed
lemma (in blockDAG) genesis_unique_exists:
  "\<exists>!a. is_genesis_node a"
  using genesis_existAlt unique_genesis by auto  

lemma (in blockDAG) genesis_in_verts:
  "genesis_node \<in> verts G"
proof -
  have "\<forall>a. (is_genesis_node a \<longrightarrow> a \<in> verts G)"
    using is_genesis_node.simps by simp
  then show ?thesis
    using genesis_node_def genesis_existAlt someI2_ex
    by metis 
qed



subsection \<open>Tips\<close>

lemma (in blockDAG) tips_exist: 
"\<exists>x. is_tip x"
  unfolding is_tip.simps
proof (rule ccontr)
  assume "\<nexists>x. x \<in> verts G \<and> (\<forall>y. \<not> y\<rightarrow>\<^sup>+x)"
  then have contr: "\<forall>x. x \<in> verts G \<longrightarrow> (\<exists>y. y\<rightarrow>\<^sup>+x)"
    by auto
  also 
  have "\<forall> x y. y\<rightarrow>\<^sup>+x \<longrightarrow> (\<forall> z. x \<rightarrow>\<^sup>+ z \<longrightarrow> \<not> z \<rightarrow>\<^sup>* y)"
    using unidirectional reachable1_reachable reachable1_reachable_trans
    by meson 
  then have "\<forall> x y. y\<rightarrow>\<^sup>+x \<longrightarrow> (\<forall> z. x \<rightarrow>\<^sup>+ z \<longrightarrow> y \<rightarrow>\<^sup>+ z)"
    by (meson trancl_trans)    
  then have "\<forall> x y. y\<rightarrow>\<^sup>+x \<longrightarrow>  {z. x \<rightarrow>\<^sup>+ z} \<subseteq> {z. y \<rightarrow>\<^sup>+ z}"
    by (meson Collect_mono) 
  then have sub: "\<forall> x y. y\<rightarrow>\<^sup>+x \<longrightarrow>  {z. x \<rightarrow>\<^sup>+ z} \<subset> {z. y \<rightarrow>\<^sup>+ z}"
    using cycle_free by auto
  have part: "\<forall> x. {z. x \<rightarrow>\<^sup>+ z} \<subseteq> verts G" 
    using reachable1_in_verts  by auto
  then have fin: "\<forall> x. finite {z. x \<rightarrow>\<^sup>+ z}"
    using finite_verts finite_subset
    by metis 
  then have trans: "\<forall> x y. y\<rightarrow>\<^sup>+x \<longrightarrow>  card {z. x \<rightarrow>\<^sup>+ z} < card {z. y \<rightarrow>\<^sup>+ z}"
    using sub psubset_card_mono by metis
  then have inf: "\<forall>y. \<exists>x. card  {z. x \<rightarrow>\<^sup>+ z} > card {z. y \<rightarrow>\<^sup>+ z}"
   using fin contr genesis past_nodes.simps psubsetI
     psubset_card_mono reachable1_in_verts(1)
   by (metis Collect_mem_eq Collect_mono)
  have all: "\<forall>k. \<exists>x. card  {z. x \<rightarrow>\<^sup>+ z} > k"
  proof 
    fix k 
    show "\<exists>x. k < card {z. x \<rightarrow>\<^sup>+ z}"
    proof(induct k)
      case 0
      then show ?case
        by (metis inf neq0_conv) 
    next
      case (Suc k)
      then show ?case
        by (metis Suc_lessI inf) 
    qed
  qed
  then have "\<exists>x.  card (verts G) < card {z. x \<rightarrow>\<^sup>+ z}" using all by simp
  then have less: "\<exists> x. \<not> card (verts G) \<ge> card {z. x \<rightarrow>\<^sup>+ z}"
    by (simp add: not_le)
  have "\<forall>x. card  {z. x \<rightarrow>\<^sup>+ z} \<le> card (verts G)" 
    using fin part finite_verts
    by (simp add: card_mono) 
  then show False
    using less by auto
qed

lemma (in blockDAG) del_tips_dag:
assumes "is_tip t"
shows "DAG (del_vert t)"
  unfolding DAG_def blockDAG_axioms_def
proof safe
  show "digraph (del_vert t)" using del_vert_simps blockDAG_axioms 
      digraph_def
    using digraph_subgraph subgraph_del_vert
    by auto 
next show "DAG_axioms (del_vert t)"
    unfolding DAG_axioms_def
  proof( rule ccontr)
    assume "\<not> (\<forall>v. (v, v) \<notin> (arcs_ends (del_vert t))\<^sup>+)"
    then obtain v where "(v, v) \<in> (arcs_ends (del_vert t))\<^sup>+" by auto
    then have "v \<rightarrow>\<^sup>+ v" using subgraph_del_vert
      by (meson arcs_ends_mono trancl_mono) 
    then show False
      by (simp add: cycle_free)
  qed
qed


lemma (in blockDAG)  del_tips_bDAG:
  assumes "is_tip t"
and " \<not>is_genesis_node t"
shows "blockDAG (del_vert t)"
  unfolding blockDAG_def blockDAG_axioms_def
proof safe
  show "DAG(del_vert t)"
    using del_tips_dag assms by simp
next 
  fix u v e 
  assume "wf_digraph.arc (del_vert t) e (u, v)"
  then have arc: "arc e (u,v)" using del_vert_simps wf_digraph.arc_def arc_def
    by (metis (no_types, lifting) mem_Collect_eq wf_digraph_del_vert)
  assume "u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (del_vert t) e\<^esub> v" 
  then have path: "u \<rightarrow>\<^sup>*\<^bsub>del_arc e\<^esub> v"
    by (meson del_arc_subgraph subgraph_del_vert digraph_axioms
        digraph_subgraph not_reachable_subgraph) 
  show False using arc path only_new by simp
next
  obtain g where gen: "is_genesis_node g" using genesisAlt genesis by auto
  then have genp: "g \<in> verts (del_vert t)"
    using assms(2) genesis del_vert_simps by auto
  have "(\<forall>r. r \<in> verts (del_vert t) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>del_vert t\<^esub> g)" 
  proof safe
  fix r
  assume in_del: "r \<in> verts (del_vert t)"
  then obtain p where path: "awalk r p g" 
    using reachable_awalk is_genesis_node.simps del_vert_simps gen by auto
  have no_head: "t \<notin> (set ( map (\<lambda>s. (head G s)) p))"
  proof (rule ccontr)
    assume "\<not> t \<notin> (set ( map (\<lambda>s. (head G s)) p))"
    then have as: "t \<in> (set ( map (\<lambda>s. (head  G s)) p))"
    by auto
    then obtain e where tl: "t = (head G e) \<and> e \<in> arcs G"
      using wf_digraph_def awalk_def path by auto
    then obtain u where hd: "u = (tail G e) \<and> u \<in> verts G"
      using wf_digraph_def tl by auto
    have "t \<in> verts G"
      using assms(1) is_tip.simps by blast 
    then have "arc_to_ends G e = (u, t)" using tl 
      by (simp add: arc_to_ends_def hd) 
    then have "reachable1 G u t"
      using dominatesI tl by blast
    then show False
      using is_tip.simps assms(1) by auto    
  qed
  have neither: "r \<noteq> t \<and> g \<noteq> t"
      using del_vert_def assms(2) gen in_del by auto
  have no_tail: "t \<notin> (set ( map (tail G) p))"
  proof(rule ccontr)
    assume as2: "\<not> t \<notin> set (map (tail G) p)"
    then have tl2: "t \<in> set (map (tail G) p)" by auto
    then have "t \<in> set (map (head G) p)"
    proof (induct rule: cas.induct)
      case (1 u v)
      then have "v \<notin> set (map (tail G) [])" by auto
      then show "v \<in> set (map (tail G) []) \<Longrightarrow> v \<in> set (map (head G) [])"
        by auto
    next
      case (2 u e es v)
      then show ?case
        using set_awalk_verts_not_Nil_cas neither awalk_def cas.simps(2) path
        by (metis UnCI tl2 awalk_verts_conv'
            cas_simp list.simps(8) no_head set_ConsD)  
    qed  
    then show False using no_head by auto
  qed
  have "pre_digraph.awalk (del_vert t) r p g" 
    unfolding pre_digraph.awalk_def
  proof safe
    show "r \<in> verts (del_vert t)" using in_del by simp   
  next
    fix x
    assume as3: "x \<in> set p"
    then have ht: "head G x \<noteq> t \<and> tail G x \<noteq> t"
      using no_head no_tail by auto
    have " x \<in> arcs G" 
      using awalk_def path subsetD as3 by auto
    then show "x \<in> arcs (del_vert t)" using del_vert_simps(2) ht by auto   
  next
    have "pre_digraph.cas G r p g" using path by auto
    then show "pre_digraph.cas (del_vert t) r p g"
    proof(induct p arbitrary:r)
      case Nil
      then have "r = g" using awalk_def cas.simps by auto
      then show ?case using pre_digraph.cas.simps(1)
        by (metis)  
    next
      case (Cons a p)
      assume pre: "\<And>r. (cas r p g \<Longrightarrow> pre_digraph.cas (del_vert t) r p g)"
      and one: "cas r (a # p) g"
      then have two: "cas (head G a) p g"
        using awalk_def  by auto
      then have t: "tail (del_vert t) a = r"
        using one cas.simps awalk_def del_vert_simps(3) by auto
      then show ?case 
        unfolding pre_digraph.cas.simps(2) t
        using pre two del_vert_simps(4) by auto
    qed
  qed
  then show "r \<rightarrow>\<^sup>*\<^bsub>del_vert t\<^esub> g" by (meson wf_digraph.reachable_awalkI  
  del_tips_dag assms(1) DAG_def digraph_def fin_digraph_def)
qed
  then show " \<exists>p. p \<in> verts (del_vert t) \<and>
        (\<forall>r. r \<in> verts (del_vert t) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>del_vert t\<^esub> p)"
    using gen genp by auto
qed

subsection \<open>past_nodes\<close>

lemma (in blockDAG) past_nodes_ex:
  assumes "a \<in> verts G"
  shows "a \<notin> past_nodes a"
  using cycle_free past_nodes.simps reachable_def by auto

lemma (in blockDAG) past_nodes_verts: 
  shows "past_nodes a \<subseteq> verts G"
  using past_nodes.simps reachable1_in_verts by auto

lemma (in blockDAG) past_nodes_refl_ex:
  assumes "a \<in> verts G"
  shows "a \<in> past_nodes_refl a"
  using past_nodes_refl.simps reachable_refl assms
  by simp

lemma (in blockDAG) past_nodes_refl_verts: 
  shows "past_nodes_refl a \<subseteq> verts G"
  using past_nodes.simps reachable_in_verts by auto

lemma (in blockDAG) finite_past: "finite (past_nodes a)"
  by (meson finite_verts rev_finite_subset
 fin_digraph.finite_verts past_nodes.simps reachable_def past_nodes_verts)

lemma (in blockDAG) finite_future: "finite (future_nodes a)"
  by (metis (full_types) Collect_subset digraphI_induced digraph_def fin_digraph.finite_verts 
future_nodes.simps induce_subgraph_verts induced_induce)


lemma (in blockDAG) past_future_dis[simp]: "past_nodes a \<inter> future_nodes a = {}"
proof (rule ccontr)
  assume "\<not> past_nodes a \<inter> future_nodes a = {}"
  then show False
    using past_nodes.simps future_nodes.simps unidirectional reachable1_reachable by blast
qed

subsection \<open>reduce_past\<close>

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


lemma (in blockDAG) reduce_past_pathr:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> v" 
  shows " u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v"
  by (meson assms induced_subgraph_altdef reachable_mono reduce_past_induced_subgraph)



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

lemma (in blockDAG) reduce_less:
  assumes "a \<in> verts G"
  and "\<not>is_genesis_node a"
  shows "card (verts (reduce_past a)) < card (verts G)"
proof -
  have "past_nodes a \<subset> verts G"
    using assms(1) past_nodes_ex past_nodes_verts by blast
  then show ?thesis
    by (simp add: psubset_card_mono)
qed 

(* unnecessary
lemma (in blockDAG) genesisGraph:
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
*)


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
        have pe: "p \<in> verts (reduce_past a) \<and> (\<forall>r. r \<in> verts (reduce_past a) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> p)"
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
            then have con: "r \<rightarrow>\<^sup>* p" using gen genesisAlt past_nodes_verts by auto  
            then show "r \<rightarrow>\<^sup>*\<^bsub>reduce_past a\<^esub> p"
            proof -
            have f1: "r \<in> verts G \<and> a \<rightarrow>\<^sup>+ r"
            using in_past past_nodes_verts by force
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
          using pe by auto
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

subsection \<open>reduce_past_refl\<close>

lemma (in blockDAG) reduce_past_refl_induced_subgraph:
  shows "induced_subgraph (reduce_past_refl a) G"
  using  induced_induce past_nodes_refl_verts by auto

lemma (in blockDAG) reduce_past_refl_arcs2:
  "e \<in> arcs (reduce_past_refl a) \<Longrightarrow> e \<in> arcs G"
  using reduce_past_arcs by auto

lemma (in blockDAG) reduce_past_refl_digraph:
  assumes "a \<in> verts G"
  shows "digraph (reduce_past_refl a)"
  using digraphI_induced reduce_past_refl_induced_subgraph reachable_mono by simp

lemma (in blockDAG) reduce_past_refl_dagbased:
  assumes "a \<in> verts G"
  shows "blockDAG (reduce_past_refl a)"
  unfolding blockDAG_def DAG_def
proof safe
  show "digraph (reduce_past_refl a)"
    using reduce_past_refl_digraph assms(1) by simp
next
  show "DAG_axioms (reduce_past_refl a)"
    unfolding DAG_axioms_def
    using cycle_free reduce_past_refl_induced_subgraph reachable_mono
    by (meson arcs_ends_mono induced_subgraph_altdef trancl_mono) 
next
  show "blockDAG_axioms (reduce_past_refl a)"
    unfolding blockDAG_axioms
  proof
    fix u v 
    show "\<forall>e. wf_digraph.arc (reduce_past_refl a) e (u, v) \<longrightarrow>
               \<not> u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past_refl a) e\<^esub> v"
    proof safe
      fix e 
      assume a: " wf_digraph.arc (reduce_past_refl a) e (u, v)"
      and b: "u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc (reduce_past_refl a) e\<^esub> v"
      have edge: "wf_digraph.arc G e (u, v)"
          using assms reduce_past_arcs2 induced_subgraph_def arc_def 
        proof -
          have "wf_digraph (reduce_past_refl a)"
            using reduce_past_refl_digraph digraph_def by auto
          then have "e \<in> arcs (reduce_past_refl a) \<and> tail (reduce_past_refl a) e = u
                     \<and> head (reduce_past_refl a) e = v"
            using wf_digraph.arcE arc_def a
            by (metis (no_types)) 
          then show "arc e (u, v)"
            using arc_def reduce_past_refl.simps by auto
        qed
      have "u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc G e\<^esub> v"
        using a b reduce_past_refl_digraph del_arc_subgraph digraph_axioms not_reachable_subgraph
        by (metis digraphI_induced past_nodes_refl_verts reduce_past_refl.simps
            reduce_past_refl_induced_subgraph subgraph_induce_subgraphI)
      then show False
        using edge only_new by simp
    qed
  next
    show "\<exists>p. p \<in> verts (reduce_past_refl a) \<and> (\<forall>r. r \<in> verts (reduce_past_refl a)
         \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past_refl a\<^esub> p)"
      proof -
        obtain p where gen: "is_genesis_node p" using genesis_existAlt by auto
        have pe: "p \<in> verts (reduce_past_refl a)"
        using genesisAlt induce_reachable_preserves_paths
            reduce_past.simps past_nodes.simps reachable1_reachable induce_subgraph_verts
            gen mem_Collect_eq reachable_neq_reachable1
            assms by force    
        have reaches: "(\<forall>r. r \<in> verts (reduce_past_refl a) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past_refl a\<^esub> p)" 
          proof safe
            fix r
            assume in_past: "r \<in> verts (reduce_past_refl a)"
            then have con: "r \<rightarrow>\<^sup>* p" using gen genesisAlt reachable_in_verts by simp
            have "a \<rightarrow>\<^sup>* r" using in_past by auto
            then have reach: "r \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {w. a \<rightarrow>\<^sup>* w}\<^esub> p"
            proof(induction)
              case base
              then show ?case
                by (simp add: con induce_reachable_preserves_paths) 
            next
              case (step x y)
              then show ?case
              proof -
                have "Collect (reachable G y) \<subseteq> Collect (reachable G x)"
                  using adj_reachable_trans step.hyps(1) by force
                then show ?thesis
                  using reachable_induce_ss step.IH by blast
              qed 
            qed
            show "r \<rightarrow>\<^sup>*\<^bsub>reduce_past_refl a\<^esub> p" using reach reduce_past_refl.simps 
            past_nodes_refl.simps by simp
          qed
          show "?thesis" using pe reaches by auto
        qed
      qed
    qed

subsection \<open>gen_graph\<close>

                                  
definition (in blockDAG) gen_graph::"('a,'b) pre_digraph" where 
"gen_graph = induce_subgraph G {blockDAG.genesis_node G}"

lemma (in blockDAG) gen_gen :"verts (gen_graph) = {genesis_node}" 
  unfolding genesis_node_def gen_graph_def by simp
   
lemma (in blockDAG) gen_graph_digraph:
  "digraph gen_graph"
using digraphI_induced induced_induce gen_graph_def 
       genesis_in_verts by simp  

lemma (in blockDAG) gen_graph_empty_arcs: 
 "arcs gen_graph = {}"
   proof(rule ccontr)
     assume "\<not> arcs gen_graph = {}"
     then have ex: "\<exists>a. a \<in> (arcs gen_graph)"
       by blast
     also have "\<forall>a. a \<in> (arcs gen_graph)\<longrightarrow> tail G a = head G a"
     proof safe
       fix a
       assume "a \<in> arcs gen_graph"
       then show "tail G a = head G a"
         using digraph_def induced_subgraph_def induce_subgraph_verts
              induced_induce gen_graph_def by simp
     qed
     then show False
       using digraph_def ex gen_graph_def gen_graph_digraph induce_subgraph_head induce_subgraph_tail 
           loopfree_digraph.no_loops
       by metis
   qed


lemma (in blockDAG) gen_graph_sound: 
  "blockDAG (gen_graph)"
  unfolding blockDAG_def DAG_def blockDAG_axioms_def
proof safe
   show "digraph gen_graph" using gen_graph_digraph by simp     
 next
   have "(arcs_ends gen_graph)\<^sup>+ = {}"
     using trancl_empty gen_graph_empty_arcs by (simp add: arcs_ends_def) 
  then show "DAG_axioms gen_graph"
    by (simp add: DAG_axioms.intro) 
next
  fix u v e 
  have "wf_digraph.arc gen_graph e (u, v) \<equiv> False"
    using wf_digraph.arc_def gen_graph_empty_arcs
    by (simp add: wf_digraph.arc_def wf_digraph_def) 
  then show "wf_digraph.arc gen_graph e (u, v) \<Longrightarrow>
       u \<rightarrow>\<^sup>*\<^bsub>pre_digraph.del_arc gen_graph e\<^esub> v \<Longrightarrow> False"
    by simp
next  
  have refl: "genesis_node \<rightarrow>\<^sup>*\<^bsub>gen_graph\<^esub> genesis_node"
    using gen_gen rtrancl_on_refl
    by (simp add: reachable_def) 
  have "\<forall>r. r \<in> verts gen_graph \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>gen_graph\<^esub> genesis_node"  
  proof safe
    fix r
    assume "r \<in> verts gen_graph"
    then have "r = genesis_node"
      using gen_gen by auto
    then show "r \<rightarrow>\<^sup>*\<^bsub>gen_graph\<^esub> genesis_node"
      by (simp add: local.refl)   
  qed
  then show " \<exists>p. p \<in> verts gen_graph \<and>
        (\<forall>r. r \<in> verts gen_graph \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>gen_graph\<^esub> p)"
    by (simp add: gen_gen)
qed 

lemma (in blockDAG) no_empty_blockDAG:
  shows "card (verts G) > 0"
proof -
  have "\<exists>p. p \<in> verts G"
    using genesis_in_verts by auto 
  then show "card (verts G) > 0"
    using card_gt_0_iff finite_verts by blast
qed

  
lemma blockDAG_nat_induct[consumes 1, case_names base step]: 
  assumes
 major: "blockDAG Z" and
 cases: "\<And>V. (blockDAG V \<Longrightarrow> card (verts V) = 1 \<Longrightarrow> P V)"
  "\<And>V c. ((blockDAG V \<Longrightarrow> card (verts V) = c \<Longrightarrow> P V) 
  \<Longrightarrow> (blockDAG V \<Longrightarrow> card (verts V) = (Suc c) \<Longrightarrow> P V))"
shows "P Z"
  using blockDAG.no_empty_blockDAG list_decode.cases
  cases(1) cases(2) major  n_not_Suc_n
  by (metis neq0_conv) 

lemma (in blockDAG) blockDAG_size_cases:
  obtains (one) "card (verts G) = 1" 
| (more) "card (verts G) > 1"
  using no_empty_blockDAG
  by linarith 

lemma (in blockDAG) blockDAG_cases_int:
  shows "(G = gen_graph) \<or> (\<exists>b H. (blockDAG H \<and> del_vert b = H))"
proof(rule blockDAG_size_cases)
  assume one: "card (verts G) = 1"
  then have "blockDAG.genesis_node G \<in> verts G"
    by (simp add: genesis_in_verts)
  then have only: "verts G = {blockDAG.genesis_node G}"
    by (metis one  card_1_singletonE insert_absorb singleton_insert_inj_eq')
  then have verts_equal: "verts G = verts (blockDAG.gen_graph G)"
    using  blockDAG_axioms one blockDAG.gen_graph_def induce_subgraph_def
      induced_induce blockDAG.genesis_in_verts
    by (simp add: blockDAG.gen_graph_def) 
  have "arcs G ={}" 
  proof (rule ccontr)
    assume not_empty: "arcs G \<noteq>{}" 
    then obtain z where part_of: "z \<in> arcs G"
      by auto
    then have tail: "tail G z \<in> verts G"
      using wf_digraph_def blockDAG_def DAG_def 
        digraph_def blockDAG_axioms nomulti_digraph.axioms(1)
      by metis
    also have head: "head G z \<in> verts G" 
        by (metis (no_types) DAG_def blockDAG_axioms blockDAG_def digraph_def
            nomulti_digraph.axioms(1) part_of wf_digraph_def)
    then have "tail G z = head G z"
    using tail only by simp
  then have "\<not> loopfree_digraph_axioms G"
    unfolding loopfree_digraph_axioms_def
      using  part_of only  DAG_def digraph_def
      by auto
    then show False
      using blockDAG_axioms blockDAG_def DAG_def digraph_def
        loopfree_digraph_def by auto
  qed                                                                          
  then have "arcs G = arcs (blockDAG.gen_graph G)"
    by (simp add: blockDAG_axioms blockDAG.gen_graph_empty_arcs)
  then show "G = gen_graph \<or> (\<exists>b H. blockDAG H \<and> del_vert b = H)"
    unfolding  blockDAG.gen_graph_def
    using verts_equal blockDAG_axioms  induce_subgraph_def graph_equality gen_graph_sound
    blockDAG.gen_graph_def by fastforce
next 
  assume b1: "1 < card (verts G)"
  obtain x where x_in: "x \<in> (verts G) \<and> is_genesis_node x" 
    using genesis genesisAlt genesis_node_def  by blast
  then have "0 < card ((verts G) - {x})" using card_Suc_Diff1 x_in finite_verts b1 by auto
  then have "((verts G) - {x}) \<noteq> {}" using card_gt_0_iff by blast
  then obtain y where y_def:"y \<in> (verts G) - {x}" by auto
  then have uneq: "y \<noteq> x" by auto
  have y_in: "y \<in> (verts G)" using y_def by simp
  then have "reachable1 G y x" using is_genesis_node.simps x_in
      reachable_neq_reachable1 uneq by simp
  then have "\<not> is_tip x" by auto
  then obtain z where z_def: "z \<in> (verts G) - {x} \<and> is_tip z" using tips_exist
  is_tip.simps by auto
  then have uneq: "z \<noteq> x" by auto
  have "\<not> is_genesis_node z"
  proof (rule ccontr, safe)
    assume "is_genesis_node z"
    then have "x = z" using unique_genesis x_in by auto
    then show False using uneq by simp
  qed
  then have "blockDAG (del_vert z)" using del_tips_bDAG z_def by simp
  then have "(\<exists>b H. blockDAG H \<and> del_vert b = H)" using z_def by auto
  then show "G = gen_graph \<or> (\<exists>b H. blockDAG H \<and> del_vert b = H)" by simp
qed

lemma (in blockDAG) blockDAG_cases:
  obtains (base) "(G = gen_graph)"
  | (more) "(\<exists>b H. (blockDAG H \<and> del_vert b = H))"
  using blockDAG_cases_int by auto

lemma (in blockDAG) blockDAG_induct[consumes 1, case_names base step]:
  assumes cases: "P (gen_graph)"
       "\<And>b H. 
   (blockDAG (pre_digraph.del_vert H b) \<Longrightarrow> P(pre_digraph.del_vert H b))
  \<Longrightarrow> (blockDAG H \<Longrightarrow> P H)"
     shows "P G"
proof(induct_tac G rule:blockDAG_nat_induct) 
  show "blockDAG G" using blockDAG_axioms by simp
next
  fix V
  assume "blockDAG V" 
  and "card (verts V) = 1"
  then have "V = blockDAG.gen_graph V"
    using genesis gen_graph
  then show "P V" using cases(1) by simp
next 
  assume "\<exists>b H. blockDAG H \<and> del_vert b = H"
  then obtain b where "\<exists>H. blockDAG H \<and> pre_digraph.del_vert G b = H" by auto
  then obtain H where "blockDAG H \<and> pre_digraph.del_vert G b = H" by auto
  then have "blockDAG (pre_digraph.del_vert G b)" by auto
  then show "P G" using cases(2) blockDAG_axioms 
section \<open>Spectre\<close>


subsection \<open>Spectre_Definition\<close>


definition (in tie_breakingDAG) tie_break_int:: "'c \<Rightarrow> 'c \<Rightarrow> int \<Rightarrow> int"
  where "tie_break_int a b i =
 (if i=0 then (if (a \<le> b) then 1 else -1) else 
              (if i > 0 then 1 else -1))"

fun (in tie_breakingDAG) sumlist_acc :: "'c \<Rightarrow>'c \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int"
  where "sumlist_acc a b s [] = tie_break_int a b s"
  | "sumlist_acc a b s (x#xs) = sumlist_acc a b (s + x) xs"

fun (in tie_breakingDAG) sumlist :: "'c \<Rightarrow>'c \<Rightarrow> int list \<Rightarrow> int"
  where "sumlist a b [] = 0"
  | "sumlist a b (x # xs) = sumlist_acc a b 0 (x # xs)"
  
datatype Spectre_cases = LeftR | RightR | BothR | NeitherR | Malformed  

fun vote_Spectre_calc_cases ::" ('c,'b) pre_digraph \<Rightarrow>'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> Spectre_cases"
  where "vote_Spectre_calc_cases V a b c = LeftR"

function vote_Spectre:: " ('c::linorder,'b) pre_digraph \<Rightarrow>'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> int" 
  where
"vote_Spectre V a b c = 
  (if (\<not> (tie_breakingDAG V) \<or> (a \<notin> (verts V)) \<or> b \<notin> verts V \<or> c \<notin> verts V) then undefined else 
  (if (b=c) then 1 else 
  (if ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c)) then 1  else 
  (if ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b)) then -1  else 
  (if ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 
   tie_breakingDAG.sumlist b c (map (\<lambda>i.
 (vote_Spectre (blockDAG.reduce_past V a) i b c)) (sorted_list_of_set ((blockDAG.past_nodes V a)))) 
  else tie_breakingDAG.sumlist b c (map (\<lambda>i.
   (vote_Spectre V i b c)) (sorted_list_of_set (blockDAG.future_nodes V a))))))))"
  by auto
termination (in tie_breakingDAG) 
proof(relation "measure (\<lambda> (V, a, b, c). card (verts V))") 
  show  "wf (measure (\<lambda>(V, a, b, c). card (verts V)))"
    by auto
next 
  fix V a b c x
  assume "\<not> (\<not> (tie_breakingDAG V) \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V)"
  and "\<not> (b = c)"
  and " \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b \<and> \<not> a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c)"
  and "\<not> (a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c \<and> \<not> a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b)"
  and " a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b \<and> \<not> a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c"
  and "x \<in> set (sorted_list_of_set (blockDAG.direct_past V a))"
  then show " ((blockDAG.reduce_past V a, x, b, c), V, a, b, c)
       \<in> measure (\<lambda>(V, a, b, c). card (verts V))"
    using reduce_less reduce_past_dagbased direct_past.simps
    oops
lemma del_arc_code [code]: "pre_digraph.del_arc G a =
 \<lparr> verts = verts G, arcs = arcs G - {a}, tail = tail G, head = head G \<rparr>"
  by (simp add: pre_digraph.del_arc_def)

export_code pre_digraph.del_arc in Haskell module_name SPECTRE

end
