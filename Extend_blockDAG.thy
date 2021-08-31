theory Extend_blockDAG
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
    and new_node: "\<forall>b \<in> verts G_A. \<not> b \<rightarrow>\<^bsub>G_A\<^esub> app"

locale Honest_Append_One = Append_One +
  assumes ref_tips: "\<forall>t \<in> tips G. app \<rightarrow>\<^bsub>G_A\<^esub> t"  


locale Append_One_Honest_Dishonest = Honest_Append_One + 
  fixes G_AB :: "('a, 'b) pre_digraph" (structure)
    and dis::'a
  assumes app_two:"Append_One G_A G_AB dis"
    and dis_n_app: "\<not> dis \<rightarrow>\<^bsub>G_AB\<^esub> app"

subsection \<open>Append-One Lemmas\<close>

lemma (in Append_One) new_node_alt:
  "(\<forall>b. \<not> b \<rightarrow>\<^bsub>G_A\<^esub> app)" 
proof(auto)
  fix b
  assume a2: "b \<rightarrow>\<^bsub>G_A\<^esub> app"
  then have "b \<in> verts G_A" using wf_digraph.adj_in_verts(1) bD_A subs by metis
  then show "False" using new_node a2 by auto
qed


lemma (in Append_One) append_subverts_leq:            
  "verts G \<subseteq> verts G_A"
  unfolding GG_A pre_digraph.verts_del_vert by auto

lemma (in Append_One) append_subverts:            
  "verts G \<subset> verts G_A"
  unfolding GG_A  pre_digraph.verts_del_vert using app_in app_notin by auto

lemma (in Append_One) append_verts: 
  "verts G_A = verts G \<union> {app}"
  unfolding GG_A  pre_digraph.verts_del_vert using app_in app_notin by auto

lemma (in Append_One) append_verts_in: 
  assumes "a \<in> verts G"
  shows "a \<in> verts G_A"
  unfolding append_verts
  by (simp add: assms) 

lemma (in Append_One) append_verts_diff: 
  shows "verts G = verts G_A - {app}"
  using append_verts app_in app_notin by auto

lemma (in Append_One) append_verts_cases: 
  assumes "a \<in> verts G_A"
  obtains (a_in_G) "a \<in> verts G" | (a_eq_app) "a = app"
  using append_verts assms by auto

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
      genesis_in_verts new_node psubsetD tranclE new_node_alt
    by (metis (mono_tags, lifting))
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


lemma (in Append_One) append_induce_subgraph: 
  "G_A \<restriction> (verts G) = G"  
proof -
  have aaa: "arcs G = {e \<in> arcs G_A. tail G_A e \<in> verts G \<and> head G_A e \<in> verts G}"
    unfolding GG_A pre_digraph.arcs_del_vert pre_digraph.verts_del_vert
    using append_verts bD_A subs wf_digraph_def
    by (metis (no_types, lifting) Diff_insert_absorb Un_empty_right
        Un_insert_right app_notin insertE)  
  show  "G_A \<restriction> verts G = G" 
    unfolding  induce_subgraph_def
    using aaa app_notin append_head append_tail 
      arcs_del_vert del_vert_def del_vert_not_in_graph verts_del_vert
    by (metis (no_types, lifting)) 
qed

lemma (in Append_One) append_induced_subgraph: 
  "induced_subgraph G G_A "
proof -
  interpret W: blockDAG "G_A" using bD_A by auto
  show ?thesis
    using W.induced_induce append_induce_subgraph append_subverts psubsetE
    by (metis) 
qed


lemma (in Append_One) append_not_reached:
  "\<forall>b \<in> verts G_A. \<not> b \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> app"
  using tranclE wf_digraph.reachable1_in_verts(2) bD_A subs new_node
  by metis  


lemma (in Append_One) append_not_reached_all:
  "\<forall>b. \<not> b \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> app"
  using tranclE bD_A new_node_alt
  by metis  


lemma (in Append_One) append_not_headed:
  "\<forall>b \<in> arcs G_A. \<not> head G_A b = app"
proof(rule ccontr, safe)
  fix b
  assume "b \<in> arcs G_A"
    and "app = head G_A b"
  then have "tail G_A b \<rightarrow>\<^bsub>G_A\<^esub> app"
    unfolding arcs_ends_def arc_to_ends_def
    by auto 
  then show False 
    by (simp add: new_node_alt) 
qed

lemma (in Append_One) dominates_preserve:
  assumes "b \<in> verts G"
  shows "b \<rightarrow>\<^bsub>G_A\<^esub> c \<longleftrightarrow> b \<rightarrow>\<^bsub>G\<^esub> c"
proof  
  assume " b \<rightarrow>\<^bsub>G\<^esub> c"
  then show "b \<rightarrow>\<^bsub>G_A\<^esub> c"
    using append_subgraph pre_digraph.adj_mono
    by metis
next 
  have b_napp : "b \<noteq> app" using assms(1) append_verts_diff by auto
  assume bc: "b \<rightarrow>\<^bsub>G_A\<^esub> c" 
  then have  c_napp: "c \<noteq> app" using new_node_alt by auto
  show "b \<rightarrow>\<^bsub>G\<^esub> c"  unfolding arcs_ends_def arc_to_ends_def
    using GG_A pre_digraph.arcs_del_vert bc b_napp c_napp
    using append_head append_tail by fastforce 
qed


lemma (in Append_One) reachable1_preserve:
  assumes "b \<in> verts G"
  shows "(b \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> c) \<longleftrightarrow> b \<rightarrow>\<^sup>+ c"
proof(standard)
  assume  "b \<rightarrow>\<^sup>+ c"
  then show "b \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> c"
    using trancl_mono append_subgraph arcs_ends_mono
    by (metis)  
next 
  interpret B2: blockDAG "G_A" using bD_A by simp
  assume c_re: "b \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> c"
  show "b \<rightarrow>\<^sup>+ c"   
    using c_re
  proof(cases  rule: trancl_induct)
    case (base y)
    then have "b \<rightarrow>\<^bsub>G\<^esub> y" using dominates_preserve assms(1) by auto
    then show "b \<rightarrow>\<^sup>+ y" by auto
  next
    fix y z    
    assume b_y: "b \<rightarrow>\<^sup>+ y" 
    then have y_in: "y \<in> verts G" using reachable1_in_verts(2)
      by (metis) 
    assume "y \<rightarrow>\<^bsub>G_A\<^esub> z"
    then have "y \<rightarrow>\<^bsub>G\<^esub> z" using dominates_preserve y_in by auto
    then show "b \<rightarrow>\<^sup>+ z" using b_y by auto
  qed
qed

lemma (in Append_One) append_past_nodes:
  assumes "a \<in> verts G"
  shows "past_nodes G a = past_nodes G_A a"
  unfolding past_nodes.simps append_verts using 
    assms reachable1_preserve append_not_reached_all by auto

lemma (in Append_One) append_is_tip:
  "is_tip G_A app"
  unfolding is_tip.simps 
  using app_in new_node append_not_reached
  by metis

lemma (in Append_One) append_in_tips:
  "app  \<in> tips G_A"
  unfolding tips_def  
  using app_in new_node append_is_tip CollectI
  by metis

lemma (in Append_One) append_future:
  assumes "a \<in> verts G"
  shows "future_nodes G a = future_nodes G_A a - {app}"
  unfolding future_nodes.simps append_verts
proof(auto simp: assms reachable1_preserve app_notin) qed

lemma (in Append_One) append_greater_1:
  "card (verts G_A) > 1"
  unfolding append_verts 
  using app_notin no_empty_blockDAG by auto  

lemma (in Append_One) append_reduce_some:
  assumes "a \<in> verts G"
  shows "reduce_past G_A a = reduce_past G a"
  unfolding reduce_past.simps past_nodes.simps append_head append_tail 
    induce_subgraph_def append_verts 
proof(standard,simp,standard)
  have "a \<noteq> app" using assms(1) append_verts_diff by auto
  then show vv: "{b. (b = app \<or> b \<in> verts G) \<and> a \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> b} = {b \<in> verts G. a \<rightarrow>\<^sup>+ b}" 
    using reachable1_preserve assms reachable1_in_verts(2) by blast  
  show "{e \<in> arcs G_A.
     (tail G e = app \<or> tail G e \<in> verts G) \<and>
     a \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> tail G e \<and> (head G e = app \<or> head G e \<in> verts G) \<and> a \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> head G e} =
    {e \<in> arcs G. tail G e \<in> verts G \<and> a \<rightarrow>\<^sup>+ tail G e \<and> head G e \<in> verts G \<and> a \<rightarrow>\<^sup>+ head G e} "
    unfolding vv GG_A pre_digraph.arcs_del_vert using append_not_reached_all
    using GG_A append_head append_tail assms reachable1_preserve by fastforce 
qed



lemma blockDAG_induct_append[consumes 1, case_names base step]:
  assumes fund: "blockDAG G"
  assumes cases: "\<And>V::('a,'b) pre_digraph. blockDAG V \<Longrightarrow> P (blockDAG.gen_graph V)"
    "\<And>G G_A::('a,'b) pre_digraph. \<And>app::'a. 
   Append_One G G_A app
  \<Longrightarrow> (P G)
  \<Longrightarrow> P G_A"
  shows "P G"
  using assms
proof(induct G rule: blockDAG_induct)
  case (base V)
  then show ?case by auto
next
  case (step H)
  show ?case proof(cases H rule: blockDAG.blockDAG_cases2, simp add: step)
    case 2
    then have "blockDAG (blockDAG.gen_graph H)" using step(2) blockDAG.gen_graph_sound by auto
    then show ?thesis using step(3) 2 by metis 
  next
    case 3
    then obtain Ha and b where bD_Ha: "blockDAG Ha" and b_in: "b \<in> verts H"
      and del_v: "Ha = pre_digraph.del_vert H b " and nre:"(\<forall>c\<in>verts H. (c, b) \<notin> (arcs_ends H)\<^sup>+)"
      by auto
    then have "b \<notin> verts Ha" unfolding del_v pre_digraph.verts_del_vert by auto
    then have "Append_One Ha H b" unfolding Append_One_def Append_One_axioms_def 
      using bD_Ha b_in del_v nre step.hyps(2) by auto 
    then show ?thesis using step
      using bD_Ha b_in del_v by auto 
  qed  
qed


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

lemma (in Honest_Append_One) append_past_all:
  "past_nodes G_A app = verts G"
  unfolding past_nodes.simps append_verts 
  using reaches_all DAG.cycle_free bD_A subs
  by fastforce 



lemma (in Honest_Append_One) append_in_future:
  assumes "a \<in> verts G"
  shows "app \<in> future_nodes G_A a"
  unfolding future_nodes.simps append_verts
  using assms
proof(auto simp: reaches_all reachable1_preserve) qed

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

lemma (in Honest_Append_One) reduce_append:
  "reduce_past G_A app = G"
  unfolding reduce_past.simps past_nodes.simps 
proof -
  have "{b \<in> verts G. app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> b} = verts G"
    using reaches_all by auto
  moreover have "{b \<in> verts G. app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> b} = {b \<in> verts G_A. app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> b}"
    unfolding append_verts using append_is_tip by fastforce
  ultimately have "{b \<in> verts G_A. app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> b} = verts G" by simp 
  then show "G_A \<restriction> {b \<in> verts G_A. app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> b} = G " 
    unfolding induce_subgraph_def 
    using append_induced_subgraph induced_subgraph_def 
      append_head append_tail
    by (metis (no_types, lifting) Collect_cong app_notin arcs_del_vert
        del_vert_def del_vert_not_in_graph verts_del_vert) 
qed

lemma (in Honest_Append_One) append_no_anticone:
  "anticone G_A app = {}"
  unfolding anticone.simps
proof safe
  fix x 
  assume  "x \<in> verts G_A"
    and  "app \<noteq> x"
    and as: "(app, x) \<notin> (arcs_ends G_A)\<^sup>+ "
  then have "x \<in> verts G" 
    using append_verts by auto
  then have "app \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> x"
    using reaches_all by auto
  then show "x \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> app" 
    using as by auto
qed

subsection \<open>Honest-Dishonest-Append-One Lemmas\<close>



lemma (in Append_One_Honest_Dishonest) app_dis_not_reached:
  shows "\<not> dis \<rightarrow>\<^sup>+\<^bsub>G_AB\<^esub> app" 
proof(rule ccontr, cases dis app "(arcs_ends G_AB)" rule: converse_trancl_induct, auto)
  fix y
  assume y_d: "y \<rightarrow>\<^bsub>G_AB\<^esub> app"
  interpret D1: Append_One G_A G_AB dis using app_two by simp
  interpret B3: blockDAG G_AB using D1.bD_A by auto
  have "y \<in> verts G_AB" using y_d B3.wellformed by auto
  then consider "y = dis" |  "y \<in> verts G_A" using D1.append_verts by auto
  then show False
  proof(cases)
    case 1
    then have "dis \<rightarrow>\<^bsub>G_AB\<^esub> app" using y_d by auto
    then show ?thesis using dis_n_app by auto
  next
    case 2
    then have "y \<rightarrow>\<^sup>+\<^bsub>G_A\<^esub> app" using D1.reachable1_preserve y_d by blast 
    then show ?thesis using append_not_reached_all by auto
  qed 
qed   


lemma (in Append_One_Honest_Dishonest) app_dis_only_tips:
  "tips G_AB = {app,dis}"
proof safe
  interpret A2: Append_One G_A G_AB dis using app_two by auto
  show "dis \<in> tips G_AB " using A2.append_in_tips by simp
  show "app \<in> tips G_AB " unfolding tips_def is_tip.simps A2.append_verts
    using app_dis_not_reached reachable1_preserve append_not_reached
      A2.reachable1_preserve app_in
    by simp 
  fix x 
  assume as1: "x \<in> tips G_AB"
    and app_x: "x \<noteq> app"
  have "x \<notin> verts G"
  proof 
    assume x_vG: "x \<in> verts G"
    then have "x \<in> verts G_A" using append_verts by auto 
    then have "app \<rightarrow>\<^sup>+\<^bsub>G_AB\<^esub> x" using A2.reachable1_preserve reaches_all x_vG app_in
      by simp 
    then have "x \<notin> tips G_AB"
      by (metis A2.append_verts_in app_in is_tip.elims(2) tips_tips)
    then show False using as1 by simp
  qed
  then show "x = dis" unfolding 
      append_verts_diff A2.append_verts_diff using app_x as1 tip_in_verts by force
qed

lemma (in Append_One_Honest_Dishonest) app_not_dis: 
"app \<noteq> dis"
  using app_in Append_One.app_notin app_two by metis


lemma (in Append_One_Honest_Dishonest) app_in2: 
"app \<in> verts G_AB" 
  using app_in Append_One.append_verts_in app_two by metis

context Append_One_Honest_Dishonest 

begin
interpretation A2: Append_One G_A G_AB dis  using local.app_two by auto


lemma  app2_head:
"head G_AB = head G" using append_head A2.append_head by simp

lemma  app2_tail:
"tail G_AB = tail G" using append_tail A2.append_tail by simp

lemma app_in_future2: 
  assumes "a \<in> verts G"  
  shows "app \<in> future_nodes G_AB a"
  unfolding future_nodes.simps A2.append_verts
  using app_in A2.reachable1_preserve app_in2 assms reaches_all
  by simp

lemma append_past_nodes2:
  "past_nodes G_AB app = verts G"
  using app_in A2.append_past_nodes append_past_all
  by auto 


lemma reachable1_preserve2:
  assumes "b \<in> verts G"
  shows "(b \<rightarrow>\<^sup>+\<^bsub>G_AB\<^esub> c) \<longleftrightarrow> b \<rightarrow>\<^sup>+ c"
  using A2.reachable1_preserve append_verts_in reachable1_preserve assms by auto

lemma reaches_all_in_G:
  assumes "b \<in> verts G"
  shows "app \<rightarrow>\<^sup>+\<^bsub>G_AB\<^esub> b"
  using assms(1) reaches_all A2.reachable1_preserve app_in
  by simp 

lemma  append_induce_subgraph2: 
  "G_AB \<restriction> (verts G) = G"
  using append_induce_subgraph A2.append_induce_subgraph
  unfolding append_verts
  by (metis A2.append_past_nodes Append_One.append_reduce_some 
      app_in app_two append_past_all reduce_past.elims) 

lemma  append_induced_subgraph2: 
  "induced_subgraph G G_AB"
  using wf_digraph.induced_induce A2.bD_A subs append_induce_subgraph2 append_subverts_leq
  A2.append_subverts_leq subset_trans
  by metis
  


lemma reduce_append2:
  "reduce_past G_AB app = G"
  unfolding reduce_past.simps past_nodes.simps 
proof -
  have "{b \<in> verts G. app \<rightarrow>\<^sup>+\<^bsub>G_AB\<^esub> b} = verts G"
    using reaches_all_in_G by auto
  moreover have "{b \<in> verts G. app \<rightarrow>\<^sup>+\<^bsub>G_AB\<^esub> b} = {b \<in> verts G_AB. app \<rightarrow>\<^sup>+\<^bsub>G_AB\<^esub> b}"
    unfolding A2.append_verts append_verts using append_is_tip app_dis_not_reached
    app_dis_only_tips
    A2.append_not_reached_all A2.reachable1_preserve by fastforce 
  ultimately have "{b \<in> verts G_AB. app \<rightarrow>\<^sup>+\<^bsub>G_AB\<^esub> b} = verts G" by simp 
  then show "G_AB \<restriction> {b \<in> verts G_AB. app \<rightarrow>\<^sup>+\<^bsub>G_AB\<^esub> b} = G" 
    using append_induced_subgraph2 
    unfolding induce_subgraph_def induced_subgraph_def app2_head app2_tail
    by (metis (no_types, lifting) Collect_cong app_notin del_vert_def del_vert_not_in_graph 
        pre_digraph.select_convs(2) verts_del_vert)
    
qed

end


end