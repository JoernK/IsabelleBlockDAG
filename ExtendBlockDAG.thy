theory ExtendBlockDAG
  imports blockDAG
begin

section \<open>Extend blockDAGs\<close>

subsection \<open>Definitions\<close>

locale Append_One = blockDAG +
  fixes G_A::"('a,'b) pre_digraph" (structure)
  and app::'a
assumes bD_A: "blockDAG G_A"
  and app_in: "app \<in> verts G_A"
  and app_notin: "app \<notin> verts G"
  and GG_A : "G = pre_digraph.del_vert G_A app"
  and new_node: "\<forall>b. \<not> b \<rightarrow>\<^bsub>G_A\<^esub> app"

locale Honest_Append_One = Append_One +
  assumes ref_tips: "\<forall>t \<in> tips G. app \<rightarrow>\<^bsub>G_A\<^esub> t"  

locale Append_One_Honest_Dishonest = Honest_Append_One + 
  fixes G_AB  (structure)
  and dis_n::'a
  assumes "Append_One G G_AB dis_n"


subsection \<open>Append-One Lemmas\<close>

lemma (in Append_One) append_subverts: 
  "verts G \<subset> verts G_A"
  unfolding GG_A  pre_digraph.verts_del_vert using app_in app_notin by auto

lemma (in Append_One) append_verts: 
  "verts G_A = verts G \<union> {app}"
  unfolding GG_A  pre_digraph.verts_del_vert using app_in app_notin by auto

lemma (in Append_One) append_subarcs_leq: 
  "arcs G \<subseteq> arcs G_A"
  unfolding GG_A  pre_digraph.arcs_del_vert using app_in app_notin 
  using wf_digraph_def subs Append_One_axioms by blast
  
lemma (in Append_One) append_subarcs: 
  "arcs G \<subset> arcs G_A"
proof
  show  "arcs G \<subseteq> arcs G_A" using append_subarcs_leq by simp
  obtain gen where gen_rec: " app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> gen" using bD_A blockDAG.genesis app_in
      app_notin append_subverts
      genesis_in_verts new_node psubsetD tranclE
    by (metis) 
  then obtain walk where walk_in: " pre_digraph.awalk G_A app walk gen \<and> walk \<noteq> []" 
    using wf_digraph.reachable1_awalk bD_A subs
    by metis 
  then obtain e where "\<exists>es. walk = e # es"
    by (metis list.exhaust) 
  then have e_in: "e \<in> arcs G_A \<and> tail G_A e = app"
    using wf_digraph.awalk_simps(2)
  bD_A subs walk_in
    by metis 
  then have "e \<notin> arcs G" using wf_digraph_def app_notin 
      blockDAG_axioms subs GG_A pre_digraph.tail_del_vert
    by metis 
  then show "arcs G \<noteq> arcs G_A" using e_in by auto
qed
  
lemma (in Append_One) append_head: 
  "head G_A = head G"
  using GG_A 
  by (simp add: pre_digraph.head_del_vert) 

lemma (in Append_One) append_tail: 
  "tail G_A = tail G"
  using GG_A 
  by (simp add: pre_digraph.tail_del_vert) 

lemma (in Append_One) append_subgraph: 
 "subgraph G G_A " 
  using  GG_A blockDAG_axioms subs bD_A
  by (simp add: subs wf_digraph.subgraph_del_vert) 

lemma (in Append_One) append_induced_subgraph: 
 "induced_subgraph G G_A "
  unfolding induced_subgraph_def
proof 
  show "subgraph G G_A" using append_subgraph by simp
  show "arcs G = {e \<in> arcs G_A. tail G_A e \<in> verts G \<and> head G_A e \<in> verts G}"
    unfolding GG_A pre_digraph.arcs_del_vert pre_digraph.verts_del_vert
  using append_verts bD_A subs wf_digraph_def
  by (metis (no_types, lifting) Diff_insert_absorb Un_empty_right
      Un_insert_right app_notin insertE)  
qed

lemma (in Append_One) append_is_tip:
"is_tip G_A app"
  unfolding is_tip.simps 
  using app_in new_node  tranclE
  by metis

lemma (in Append_One) append_in_tips:
"app  \<in> tips G_A"
  unfolding tips_def  
  using app_in new_node append_is_tip CollectI
  by metis



subsection \<open>Honest-Append-One Lemmas\<close>

lemma (in Honest_Append_One) reaches_all:
"\<forall>v \<in> verts G. app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> v"  
proof 
  fix v 
  assume v_in: "v \<in> verts G"
  consider "is_tip G v" | "\<not> is_tip G v" by auto
    then show "app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> v"
  proof(cases)
  case 1
  then show ?thesis using ref_tips v_in is_tip.simps r_into_trancl' reached_by
    by (metis) 
  next
    case 2
    then have "v \<notin> tips G" unfolding tips_def by simp
    then obtain t where t_in: "t \<in> tips G \<and> t \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v" 
      using reached_by_tip v_in by auto
    then have "t \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> v" using v_in append_subgraph arcs_ends_mono trancl_mono
        by (metis)
    moreover have "app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> t" 
    using ref_tips v_in r_into_trancl' t_in
    by (metis) 
    ultimately show ?thesis using trancl_trans by auto 
  qed
qed

lemma (in Honest_Append_One) append_is_only_tip:
  "tips G_A = {app}"
proof safe
  show "app \<in> tips G_A " using append_in_tips by simp
  fix x 
  assume as1: "x \<in> tips G_A"
  then have x_in: "x \<in> verts G_A" using digraph.tips_in_verts bD_A subs by auto 
  show "x = app"
  proof(rule ccontr)
    assume "x \<noteq> app"
    then have "x \<in> verts G" using append_verts x_in by auto
    then have "app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> x" using reaches_all by auto
    then have "\<not> is_tip G_A x"  unfolding is_tip.simps using app_in by auto
    then show "False" using as1 CollectD unfolding tips_def by auto
  qed
qed


end