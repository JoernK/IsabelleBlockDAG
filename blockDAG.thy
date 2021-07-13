(* 
    Author:     Joern Kussmaul
*)

theory blockDAG      
  imports DAGs DigraphUtils
begin

section  \<open>blockDAGs\<close>
 
locale blockDAG = DAG  +
  assumes genesis:  "\<exists>p. (p\<in> verts G \<and> (\<forall>r. r \<in> verts G  \<longrightarrow> (r \<rightarrow>\<^sup>+\<^bsub>G\<^esub> p \<or> r = p)))"       
  and only_new: "\<forall>e. (u \<rightarrow>\<^sup>+\<^bsub>(del_arc e)\<^esub> v) \<longrightarrow> \<not> arc e (u,v)"


subsection  \<open>Functions and Definitions\<close>

fun (in blockDAG) is_genesis_node :: "'a \<Rightarrow> bool" where
"is_genesis_node v = ((v \<in> verts G) \<and> (ALL x. (x \<in> verts G) \<longrightarrow>  x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v))"

definition (in blockDAG) genesis_node:: "'a"
  where "genesis_node = (SOME x. is_genesis_node x)"


subsection \<open>Lemmas\<close>
lemma subs:
  assumes "blockDAG G"
  shows "DAG G \<and> digraph G \<and> fin_digraph G \<and> wf_digraph G"
  using assms blockDAG_def DAG_def digraph_def fin_digraph_def by blast

subsubsection \<open>Genesis\<close>

lemma (in blockDAG) genesisAlt :
 "(is_genesis_node a) \<longleftrightarrow> ((a \<in> verts G) \<and> (\<forall>r.  (r \<in> verts G) \<longrightarrow> r \<rightarrow>\<^sup>* a))"
  by simp
  
lemma (in blockDAG) genesis_existAlt:
  "\<exists>a. is_genesis_node a"
  using genesis genesisAlt blockDAG_axioms_def subs wf_digraph_def
  by (metis reachable1_reachable reachable_refl)  

lemma (in blockDAG) unique_genesis: "is_genesis_node a \<and> is_genesis_node b \<longrightarrow> a = b"
      using genesisAlt reachable_trans cycle_free
            reachable_refl reachable_reachable1_trans reachable_neq_reachable1
      by (metis (full_types)) 

lemma (in blockDAG) genesis_unique_exists:
  "\<exists>!a. is_genesis_node a"
  using genesis_existAlt unique_genesis by auto  

lemma (in blockDAG) genesis_in_verts:
  "genesis_node \<in> verts G"
    using is_genesis_node.simps genesis_node_def genesis_existAlt someI2_ex
    by metis 


subsubsection \<open>Tips\<close>

lemma (in blockDAG) tips_exist: 
"\<exists>x. is_tip G x"
  unfolding is_tip.simps
proof (rule ccontr)
  assume "\<nexists>x. x \<in> verts G \<and> (\<forall>y. \<not> y\<rightarrow>\<^sup>+x)"
  then have contr: "\<forall>x. x \<in> verts G \<longrightarrow> (\<exists>y. y\<rightarrow>\<^sup>+x)"
    by auto  
  have "\<forall> x y. y\<rightarrow>\<^sup>+x \<longrightarrow>  {z. x \<rightarrow>\<^sup>+ z} \<subseteq> {z. y \<rightarrow>\<^sup>+ z}"
    using  Collect_mono trancl_trans
    by metis
  then have sub: "\<forall> x y. y\<rightarrow>\<^sup>+x \<longrightarrow>  {z. x \<rightarrow>\<^sup>+ z} \<subset> {z. y \<rightarrow>\<^sup>+ z}"
    using cycle_free by auto
  have part: "\<forall> x. {z. x \<rightarrow>\<^sup>+ z} \<subseteq> verts G" 
    using reachable1_in_verts  by auto
  then have fin: "\<forall> x. finite {z. x \<rightarrow>\<^sup>+ z}"
    using finite_verts finite_subset
    by metis 
  then have trans: "\<forall> x y. y\<rightarrow>\<^sup>+x \<longrightarrow>  card {z. x \<rightarrow>\<^sup>+ z} < card {z. y \<rightarrow>\<^sup>+ z}"
    using sub psubset_card_mono by metis
  then have inf: "\<forall>y \<in> verts G. \<exists>x. card  {z. x \<rightarrow>\<^sup>+ z} > card {z. y \<rightarrow>\<^sup>+ z}"
   using fin contr genesis 
      reachable1_in_verts(1)
   by (metis (mono_tags, lifting)) 
  have all: "\<forall>k. \<exists>x \<in> verts G. card  {z. x \<rightarrow>\<^sup>+ z} > k" 
  proof 
    fix k 
    show "\<exists>x \<in> verts G. k < card {z. x \<rightarrow>\<^sup>+ z}"
    proof(induct k)
      case 0
      then show ?case
        using inf neq0_conv
        by (metis contr genesis_in_verts local.trans reachable1_in_verts(1)) 
    next
      case (Suc k)
      then show ?case
        using Suc_lessI inf
        by (metis contr local.trans reachable1_in_verts(1)) 
    qed
  qed
  then have less: "\<exists>x \<in> verts G.  card (verts G) < card {z. x \<rightarrow>\<^sup>+ z}" by simp
  also
  have "\<forall>x. card  {z. x \<rightarrow>\<^sup>+ z} \<le> card (verts G)"
    using fin part finite_verts not_le
    by (simp add: card_mono) 
  then show False
    using less not_le by auto
qed


lemma (in blockDAG) tips_unequal_gen:
  assumes "card( verts G) > 1"
  shows "\<exists>p. p \<in> verts G \<and> is_tip G p \<and> \<not>is_genesis_node p "
proof -
  have b1: "1 < card (verts G)" using assms by linarith
  obtain x where x_in: "x \<in> (verts G) \<and> is_genesis_node x" 
    using genesis genesisAlt genesis_node_def  by blast
  then have "0 < card ((verts G) - {x})" using card_Suc_Diff1 x_in finite_verts b1 by auto
  then have "((verts G) - {x}) \<noteq> {}" using card_gt_0_iff by blast
  then obtain y where y_def:"y \<in> (verts G) - {x}" by auto
  then have uneq: "y \<noteq> x" by auto
  have y_in: "y \<in> (verts G)" using y_def by simp
  then have "reachable1 G y x" using is_genesis_node.simps x_in
      reachable_neq_reachable1 uneq by simp
  then have "\<not> is_tip G x" by auto
  then obtain z where z_def: "z \<in> (verts G) - {x} \<and> is_tip G z" using tips_exist
  is_tip.simps by auto
  then have uneq: "z \<noteq> x" by auto
  have z_in: "z \<in> verts G" using z_def by simp
  have "\<not> is_genesis_node z"
  proof (rule ccontr, safe)
    assume "is_genesis_node z"
    then have "x = z" using unique_genesis x_in by auto
    then show False using uneq by simp
  qed
  then show "?thesis" using z_def by auto
qed

lemma (in blockDAG)  del_tips_bDAG:
  assumes "is_tip G t"
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
  assume "u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc (del_vert t) e\<^esub> v" 
  then have path: "u \<rightarrow>\<^sup>+\<^bsub>del_arc e\<^esub> v"
    using  del_arc_subgraph subgraph_del_vert digraph_axioms
        digraph_subgraph 
    by (metis arcs_ends_mono trancl_mono) 
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
      using assms(1) is_tip.simps by auto 
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
        (\<forall>r. r \<in> verts (del_vert t) \<longrightarrow> (r \<rightarrow>\<^sup>+\<^bsub>del_vert t\<^esub> p \<or> r = p))"
    using gen genp
    by (metis reachable_rtranclI rtranclD) 
qed

subsection \<open>Future Nodes\<close>
lemma (in blockDAG) future_nodes_ex:
  assumes "a \<in> verts G"
  shows "a \<notin> future_nodes G a"
  using cycle_free future_nodes.simps reachable_def by auto

subsubsection \<open>Reduce Past\<close>

lemma (in blockDAG) reduce_past_not_empty:
  assumes " a \<in> verts G"
  and  "\<not>is_genesis_node a"
shows "(verts (reduce_past G a)) \<noteq> {}"
proof -
  obtain g
    where gen: "is_genesis_node g" using genesis_existAlt by auto
  have ex: "g \<in> verts (reduce_past G a)" using reduce_past.simps past_nodes.simps 
genesisAlt reachable_neq_reachable1 reachable_reachable1_trans gen assms(1) assms(2) by auto 
  then show "(verts (reduce_past G a)) \<noteq> {}" using ex by auto                                                                                           
qed

lemma (in blockDAG) reduce_less:
  assumes "a \<in> verts G"
  shows "card (verts (reduce_past G a)) < card (verts G)"
proof -
  have "past_nodes G a \<subset> verts G"
    using assms(1) past_nodes_not_refl past_nodes_verts by blast
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
  shows "blockDAG (reduce_past G a)"
  unfolding blockDAG_def DAG_def blockDAG_def
  
proof safe
  show "digraph (reduce_past G a)"
    using digraphI_induced reduce_past_induced_subgraph by auto  
next
  show "DAG_axioms (reduce_past G a)"
    unfolding DAG_axioms_def
    using cycle_free reduce_past_path by metis 
next
  show "blockDAG_axioms (reduce_past G a)"
  unfolding blockDAG_axioms_def
  proof safe
    fix u v e 
    assume arc: "wf_digraph.arc (reduce_past G a) e (u, v)"
    then show " u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc (reduce_past G a) e\<^esub> v \<Longrightarrow> False "
    proof -
        assume e_in: "(wf_digraph.arc (reduce_past G a) e (u, v))" 
        then have "(wf_digraph.arc G e (u, v))"
          using assms reduce_past_arcs2 induced_subgraph_def arc_def 
        proof -
          have "wf_digraph (reduce_past G a)"
            using reduce_past.simps subgraph_def subgraph_refl wf_digraph.wellformed_induce_subgraph
            by metis
          then have "e \<in> arcs (reduce_past G a) \<and> tail (reduce_past G a) e = u
                     \<and> head (reduce_past G a) e = v"
            using  arc wf_digraph.arcE
            by metis 
          then show ?thesis
            using arc_def reduce_past.simps by auto
        qed    
        then have "\<not> u \<rightarrow>\<^sup>+\<^bsub>del_arc e\<^esub> v"
          using only_new by auto        
        then show "u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc (reduce_past G a) e\<^esub> v \<Longrightarrow> False"
          using DAG.past_nodes_verts reduce_past.simps blockDAG_axioms subs
               del_arc_subgraph digraph.digraph_subgraph digraph_axioms 
               subgraph_induce_subgraphI
          by (metis arcs_ends_mono trancl_mono)
      qed
    next  
        obtain p where gen: "is_genesis_node p" using genesis_existAlt by auto
        have pe: "p \<in> verts (reduce_past G a) \<and> (\<forall>r. r \<in> verts (reduce_past G a) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past G a\<^esub> p)"
        proof 
          show "p \<in> verts (reduce_past G a)" using genesisAlt induce_reachable_preserves_paths
            reduce_past.simps past_nodes.simps reachable1_reachable induce_subgraph_verts assms(2)
            assms(3) gen mem_Collect_eq reachable_neq_reachable1
            by (metis (no_types, lifting)) 
            
        next    
          show "\<forall>r. r \<in> verts (reduce_past G a) \<longrightarrow> r \<rightarrow>\<^sup>*\<^bsub>reduce_past G a\<^esub> p" 
          proof safe
            fix r a
            assume in_past: "r \<in> verts (reduce_past G a)"
            then have con: "r \<rightarrow>\<^sup>* p" using gen genesisAlt past_nodes_verts by auto  
            then show "r \<rightarrow>\<^sup>*\<^bsub>reduce_past G a\<^esub> p"
            proof -
            have f1: "r \<in> verts G \<and> a \<rightarrow>\<^sup>+ r"
            using in_past past_nodes_verts by force
            obtain aaa :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
            f2: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (aaa x0 x1 \<in> x1 \<and> aaa x0 x1 \<notin> x0)"
              by moura
            have "r \<rightarrow>\<^sup>* aaa (past_nodes G a) (Collect (reachable G r))
                  \<longrightarrow> a \<rightarrow>\<^sup>+ aaa (past_nodes G a) (Collect (reachable G r))"
                using f1 by (meson reachable1_reachable_trans)
              then have "aaa (past_nodes G a) (Collect (reachable G r)) \<notin> Collect (reachable G r)
                         \<or> aaa (past_nodes G a) (Collect (reachable G r)) \<in> past_nodes G a"
                by (simp add: reachable_in_verts(2))
              then have "Collect (reachable G r) \<subseteq> past_nodes G a"
                using f2 by (meson subsetI)
              then show ?thesis
                using con  induce_reachable_preserves_paths reachable_induce_ss reduce_past.simps
            by (metis (no_types))
            qed
          qed
        qed
        show 
        "\<exists>p. p \<in> verts (reduce_past G a) \<and> (\<forall>r. r \<in> verts (reduce_past G a)
         \<longrightarrow> (r \<rightarrow>\<^sup>+\<^bsub>reduce_past G a\<^esub> p \<or> r = p))"
          using pe
          by (metis reachable_rtranclI rtranclD) 
      qed
    qed


(*
lemma (in blockDAG) reduce_past_gen:
  assumes "\<not>is_genesis_node a" 
  and "a \<in> verts G"
shows "blockDAG.is_genesis_node G b \<longleftrightarrow> blockDAG.is_genesis_node (reduce_past G a) b"
proof safe
  fix a b
  show "is_genesis_node b \<Longrightarrow> blockDAG.is_genesis_node (reduce_past G a) b"
*)

subsubsection \<open>Reduce Past Reflexiv\<close>

lemma (in blockDAG) reduce_past_refl_induced_subgraph:
  shows "induced_subgraph (reduce_past_refl G a) G"
  using  induced_induce past_nodes_refl_verts by auto

lemma (in blockDAG) reduce_past_refl_arcs2:
  "e \<in> arcs (reduce_past_refl G a) \<Longrightarrow> e \<in> arcs G"
  using reduce_past_arcs by auto

lemma (in blockDAG) reduce_past_refl_digraph:
  assumes "a \<in> verts G"
  shows "digraph (reduce_past_refl G a)"
  using digraphI_induced reduce_past_refl_induced_subgraph reachable_mono by simp

lemma (in blockDAG) reduce_past_refl_dagbased:
  assumes "a \<in> verts G"
  shows "blockDAG (reduce_past_refl G a)"
  unfolding blockDAG_def DAG_def 
proof safe
  show "digraph (reduce_past_refl G a)"
    using reduce_past_refl_digraph assms(1) by simp
next
  show "DAG_axioms (reduce_past_refl G a)"
    unfolding DAG_axioms_def
    using cycle_free reduce_past_refl_induced_subgraph reachable_mono
    by (meson arcs_ends_mono induced_subgraph_altdef trancl_mono) 
next
  show "blockDAG_axioms (reduce_past_refl G a)"
    unfolding blockDAG_axioms
  proof
    fix u v 
    show "\<forall>e. u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc (reduce_past_refl G a) e\<^esub> v
         \<longrightarrow> \<not> wf_digraph.arc (reduce_past_refl G a) e (u, v)"
    proof safe
      fix e 
      assume a: " wf_digraph.arc (reduce_past_refl G a) e (u, v)"
      and b: "u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc (reduce_past_refl G a) e\<^esub> v"
      have edge: "wf_digraph.arc G e (u, v)"
          using assms reduce_past_arcs2 induced_subgraph_def arc_def 
        proof -
          have "wf_digraph (reduce_past_refl G a)"
            using reduce_past_refl_digraph digraph_def by auto
          then have "e \<in> arcs (reduce_past_refl G a) \<and> tail (reduce_past_refl G a) e = u
                     \<and> head (reduce_past_refl G a) e = v"
            using wf_digraph.arcE arc_def a
            by (metis (no_types)) 
          then show "arc e (u, v)"
            using arc_def reduce_past_refl.simps by auto
        qed
      have "u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc G e\<^esub> v"
        using a b reduce_past_refl_digraph del_arc_subgraph digraph_axioms
         digraphI_induced past_nodes_refl_verts reduce_past_refl.simps
            reduce_past_refl_induced_subgraph subgraph_induce_subgraphI arcs_ends_mono trancl_mono
        by metis
      then show False
        using edge only_new by simp
    qed
next
        obtain p where gen: "is_genesis_node p" using genesis_existAlt by auto
        have pe: "p \<in> verts (reduce_past_refl G a)"
        using genesisAlt induce_reachable_preserves_paths
            reduce_past.simps past_nodes.simps reachable1_reachable induce_subgraph_verts
            gen mem_Collect_eq reachable_neq_reachable1
            assms by force    
      have reaches: "(\<forall>r. r \<in> verts (reduce_past_refl G a) \<longrightarrow>
             (r \<rightarrow>\<^sup>+\<^bsub>reduce_past_refl G a\<^esub> p \<or> r = p))" 
          proof safe
            fix r
            assume in_past: "r \<in> verts (reduce_past_refl G a)"
            assume une: "r \<noteq> p"
            then have con: "r \<rightarrow>\<^sup>* p" using gen genesisAlt reachable_in_verts
            reachable1_reachable
              by (metis in_past induce_subgraph_verts
                  past_nodes_refl_verts reduce_past_refl.simps subsetD)  
            have "a \<rightarrow>\<^sup>* r" using in_past by auto
            then have reach: "r \<rightarrow>\<^sup>*\<^bsub>G \<restriction> {w. a \<rightarrow>\<^sup>* w}\<^esub> p"
            proof(induction)
              case base
              then show ?case
                using  con induce_reachable_preserves_paths
                by (metis) 
            next
              case (step x y)
              then show ?case
              proof -
                have "Collect (reachable G y) \<subseteq> Collect (reachable G x)"
                  using adj_reachable_trans step.hyps(1) by force
                then show ?thesis
                  using reachable_induce_ss step.IH reachable_neq_reachable1
                  by metis 
              qed 
            qed   
            then show "r \<rightarrow>\<^sup>+\<^bsub>reduce_past_refl G a\<^esub> p" unfolding reduce_past_refl.simps
             past_nodes_refl.simps using reachable_in_verts une wf_digraph.reachable_neq_reachable1
              by (metis (mono_tags, lifting) Collect_cong wellformed_induce_subgraph)
          qed
          then show "\<exists>p. p \<in> verts (reduce_past_refl G a) \<and> (\<forall>r. r \<in> verts (reduce_past_refl G a) 
        \<longrightarrow> (r \<rightarrow>\<^sup>+\<^bsub>reduce_past_refl G a\<^esub> p \<or> r = p))" unfolding blockDAG_axioms_def 
            using pe reaches by auto
        qed
      qed 

subsubsection \<open>Genesis Graph\<close>

                                  
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
       u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc gen_graph e\<^esub> v \<Longrightarrow> False"
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
        (\<forall>r. r \<in> verts gen_graph \<longrightarrow> r \<rightarrow>\<^sup>+\<^bsub>gen_graph\<^esub> p \<or> r = p)"
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
 cases: "\<And>V. (blockDAG V \<Longrightarrow> card (verts V) = 1 \<Longrightarrow> P V)"
  "\<And>W c. (\<And>V. (blockDAG V \<Longrightarrow> card (verts V) = c \<Longrightarrow> P V)) 
  \<Longrightarrow> (blockDAG W \<Longrightarrow> card (verts W) = (Suc c) \<Longrightarrow> P W)"
shows "\<And>Z. blockDAG Z \<Longrightarrow> P Z"
proof - 
  fix Z:: "('a,'b) pre_digraph"
  assume bD: "blockDAG Z"
  then have bG: "card (verts Z) > 0" using blockDAG.no_empty_blockDAG by auto 
  show "P Z"
    using bG bD
  proof (induction "card (verts Z)"  arbitrary: Z rule: Nat.nat_induct_non_zero)
    case 1
    then show ?case using cases(1) by auto
next
  case su: (Suc n)
  show ?case 
    by (metis local.cases(2) su.hyps(2) su.hyps(3) su.prems)   
  qed   
qed 


lemma (in blockDAG) blockDAG_size_cases:
  obtains (one) "card (verts G) = 1" 
| (more) "card (verts G) > 1"
  using no_empty_blockDAG
  by linarith 

lemma (in blockDAG) blockDAG_cases_one:
  shows "card (verts G) = 1 \<longrightarrow> (G = gen_graph)"
proof (safe)
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
      using  DAG_def digraph_def blockDAG_axioms blockDAG_def
        loopfree_digraph_def by metis
  qed                                                                          
  then have "arcs G = arcs (blockDAG.gen_graph G)"
    by (simp add: blockDAG_axioms blockDAG.gen_graph_empty_arcs)
  then show "G = gen_graph"
    unfolding  blockDAG.gen_graph_def
    using verts_equal blockDAG_axioms  induce_subgraph_def
    blockDAG.gen_graph_def by fastforce
qed

lemma (in blockDAG) blockDAG_cases_more:
  shows "card (verts G) > 1 \<longleftrightarrow> (\<exists>b H. (blockDAG H \<and> b \<in> verts G \<and> del_vert b = H))"
proof safe
  assume "card (verts G) > 1"
  then have b1: "1 < card (verts G)" using no_empty_blockDAG by linarith
  obtain x where x_in: "x \<in> (verts G) \<and> is_genesis_node x" 
    using genesis genesisAlt genesis_node_def  by blast
  then have "0 < card ((verts G) - {x})" using card_Suc_Diff1 x_in finite_verts b1 by auto
  then have "((verts G) - {x}) \<noteq> {}" using card_gt_0_iff by blast
  then obtain y where y_def:"y \<in> (verts G) - {x}" by auto
  then have uneq: "y \<noteq> x" by auto
  have y_in: "y \<in> (verts G)" using y_def by simp
  then have "reachable1 G y x" using is_genesis_node.simps x_in
      reachable_neq_reachable1 uneq by simp
  then have "\<not> is_tip G x" by auto
  then obtain z where z_def: "z \<in> (verts G) - {x} \<and> is_tip G z" using tips_exist
  is_tip.simps by auto
  then have uneq: "z \<noteq> x" by auto
  have z_in: "z \<in> verts G" using z_def by simp
  have "\<not> is_genesis_node z"
  proof (rule ccontr, safe)
    assume "is_genesis_node z"
    then have "x = z" using unique_genesis x_in by auto
    then show False using uneq by simp
  qed
  then have "blockDAG (del_vert z)" using del_tips_bDAG z_def by simp
  then show "(\<exists>b H. blockDAG H \<and> b \<in> verts G \<and> del_vert b = H)" using z_def by auto
next 
  fix b and  H::"('a,'b) pre_digraph"
  assume bD: "blockDAG (del_vert b)"
  assume b_in: "b \<in> verts G"
  show  "card (verts G) > 1"
  proof (rule ccontr)
    assume "\<not> 1 < card (verts G)"
    then have "1 = card (verts G)" using no_empty_blockDAG by linarith
  then have "card ( verts ( del_vert b)) = 0" using b_in del_vert_def by auto
  then have "\<not> blockDAG (del_vert b)" using bD blockDAG.no_empty_blockDAG
    by (metis less_nat_zero_code) 
  then show "False" using bD by simp
  qed
qed

lemma (in blockDAG) blockDAG_cases:
  obtains (base) "(G = gen_graph)"
  | (more) "(\<exists>b H. (blockDAG H \<and> b \<in> verts G \<and> del_vert b = H))"
  using blockDAG_cases_one blockDAG_cases_more
    blockDAG_size_cases by auto

lemma (in blockDAG) blockDAG_induct[consumes 1, case_names base step]:
  assumes cases: "\<And>V. blockDAG V \<Longrightarrow> P (blockDAG.gen_graph V)"
       "\<And>H. 
   (\<And>b. blockDAG (pre_digraph.del_vert H b) \<Longrightarrow> b \<in> verts H \<Longrightarrow> P(pre_digraph.del_vert H b))
  \<Longrightarrow> (blockDAG H \<Longrightarrow> P H)"
     shows "P G"
proof(induct_tac G rule:blockDAG_nat_induct) 
  show "blockDAG G" using blockDAG_axioms by simp
next
  fix V::"('a,'b) pre_digraph"
  assume bD: "blockDAG V" 
  and "card (verts V) = 1"
  then have "V = blockDAG.gen_graph V"
    using blockDAG.blockDAG_cases_one equal_refl  by auto
  then show "P V" using bD cases(1)
    by metis  
next 
  fix c and W::"('a,'b) pre_digraph"
  show "(\<And>V. blockDAG V \<Longrightarrow> card (verts V) = c \<Longrightarrow> P V) \<Longrightarrow>
           blockDAG W \<Longrightarrow> card (verts W) = Suc c \<Longrightarrow> P W"
  proof -
    assume ind: "\<And>V. (blockDAG V \<Longrightarrow> card (verts V) = c \<Longrightarrow> P V)"
    and bD: "blockDAG W"
    and  size: "card (verts W) = Suc c"
    have  assm2: "\<And>b. blockDAG (pre_digraph.del_vert W b) 
            \<Longrightarrow> b \<in> verts W \<Longrightarrow> P(pre_digraph.del_vert W b)"
    proof -
      fix b
      assume bD2: "blockDAG (pre_digraph.del_vert W b)"
      assume in_verts: "b \<in> verts W"
      have "verts (pre_digraph.del_vert W b) = verts W - {b}"
        by (simp add: pre_digraph.verts_del_vert) 
      then have "card ( verts (pre_digraph.del_vert W b)) = c" 
        using in_verts fin_digraph.finite_verts bD fin_digraph_del_vert 
         size
        by (simp add: fin_digraph.finite_verts
            DAG.axioms blockDAG.axioms digraph.axioms) 
      then show "P (pre_digraph.del_vert W b)" using ind bD2 by auto
    qed
    show "?thesis" using cases(2)
      by (metis assm2 bD) 
  qed
qed

end
