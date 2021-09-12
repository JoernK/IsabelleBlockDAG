theory Verts_To_List
  imports Utils  "HOL-Library.Comparator" Extend_blockDAG
begin


text \<open>Function to sort a list $L$ under a graph G such if $a$ references $b$,
$b$ precedes $a$ in the list\<close>

fun unfold_referencing_verts:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a list" 
  where "unfold_referencing_verts G a = sorted_list_of_set ({b \<in> verts G. dominates G b a} \<union> {a})"  


fun unfold_referencing_verts_ex:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a list" 
  where "unfold_referencing_verts_ex G a = sorted_list_of_set ({b \<in> verts G. dominates G b a})"  

fun Verts_To_List_Rec:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where "Verts_To_List_Rec G L c = (if (c \<le> 0)
  then L else Verts_To_List_Rec G (foldr (@) (map (unfold_referencing_verts G) L) []) (c - 1))"
 
fun Verts_To_List:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a list"
  where "Verts_To_List G = remdups (Verts_To_List_Rec G [genesis_nodeAlt G] 
  (card (arcs G)))"

function Depth_first_search_rec:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "Depth_first_search_rec G a  = 
 (if(\<not> DAG G) then [] else (foldr (@) 
  (map (Depth_first_search_rec G) (unfold_referencing_verts_ex G a)) []) @ [a])"
  by auto
termination
proof
  let ?R = " measure ( \<lambda>(G, a). card {e \<in> verts G. e \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a})"  
  show "wf ?R"
    by simp 
next
  fix G::"('a::linorder,'b) pre_digraph"
  and a x::'a 
  assume "\<not> \<not> DAG G" 
  then interpret D: DAG G by auto
  assume x_in: "x \<in> set (unfold_referencing_verts_ex G a)"
  then have ff: "finite {b \<in> verts G. b \<rightarrow>\<^bsub>G\<^esub> a}" using D.finite_verts
    by simp 
  then have xa: "x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a" using x_in unfolding unfold_referencing_verts_ex.simps 
    using sorted_list_of_set(1)
    by auto 
  then have "\<And>b. b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> x \<Longrightarrow>  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a" using trancl_trans by auto
  then have "{b \<in> verts G.  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> x} \<subseteq> {b \<in> verts G.  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a}"
    by blast
  moreover have "\<not> x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> x" using D.cycle_free by simp
  ultimately have "{b \<in> verts G.  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> x} \<subset> {b \<in> verts G.  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a}" 
    using xa D.reachable1_in_verts(1) by blast 
  then have "card {b \<in> verts G.  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> x} < card {b \<in> verts G.  b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a}"
    by (simp add: psubset_card_mono)
  then show "((G, x), G, a) \<in> measure (\<lambda>(G, a). card {e \<in> verts G. e \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a})"
    by simp
qed


fun Depth_first_search_a:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "Depth_first_search_a G a =  rev (remdups (Depth_first_search_rec G a))"

fun Depth_first_search:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a list"
  where "Depth_first_search G =  Depth_first_search_a G (genesis_nodeAlt G)"

lemma Depth_first_search_sub:
  fixes G::"('a::linorder, 'b) pre_digraph"
shows "set (Depth_first_search G) \<subseteq> verts G"
  unfolding Depth_first_search.simps  Depth_first_search_a.simps
sorry


lemma Depth_first_search_top:
  assumes "blockDAG G" 
  and "b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a"
shows "(a,b) \<in> list_to_rel (Depth_first_search G)"
  using assms(1,2)
proof(induct G rule: blockDAG_induct_append)
  case (base V)
  then interpret bV: blockDAG V by auto
  have False using base(2) 
    unfolding arcs_ends_def bV.gen_graph_empty_arcs arc_to_ends_def by force
  then show ?case by auto
next
  case (step H)
  then show ?case sorry
qed
end