
theory Ghostdag  
  imports blockDAG Spectre
begin

fun top_le  :: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "top_le G a b = (if(tie_breakingDAG G) then 
(b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) \<or> (\<not>(b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) \<and> a \<le> b) else 
a \<le> b)"

fun top_less  :: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "top_less G a b = (if(tie_breakingDAG G) then 
(b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) \<or> (\<not>(b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) \<and> a < b) else 
a < b)"

fun le_blue_tuple ::
 "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> (('a set \<times> 'a list) \<times> 'a) \<Rightarrow> bool"
  where "le_blue_tuple ((B1 , C1),a1) ((B2 , C2),a2) = 
  (True \<longleftrightarrow> (card B1) < (card B2) \<or> (card B1 \<le> card B2 \<and> a1 \<ge> a2))"

fun less_blue_tuple ::
 "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> (('a set \<times> 'a list) \<times> 'a) \<Rightarrow> bool"
  where "less_blue_tuple ((B1 , C1),a1) ((B2 , C2),a2) = 
  (True \<longleftrightarrow> (card B1) < (card B2) \<or> (card B1 \<le> card B2 \<and> a1 > a2))"


fun add_set_list_tuple :: "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> ('a::linorder set \<times> 'a list)" 
  where "add_set_list_tuple ((S,L),a) = (S \<union> {a}, L @ [a])"

fun app_if_blue_else_add_end :: 
"('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a::linorder set \<times> 'a list)
 \<Rightarrow> 'a \<Rightarrow> ('a::linorder set \<times> 'a list)"  
where "app_if_blue_else_add_end G k (S,L) a = (if (kCluster G k (S \<union> {a})) 
then add_set_list_tuple ((S,L),a) else (S,L @ [a]))"

function OrderDAG :: "('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a set \<times> 'a list)" 
  where
  "OrderDAG G k =  
  (if (\<not> tie_breakingDAG G) then ({},[]) else 
  if (card (verts G) = 1)  then ({blockDAG.genesis_node G},[blockDAG.genesis_node G]) else
 let M = (linorder.Max le_blue_tuple
 (set ((map (\<lambda>i.(((OrderDAG (reduce_past G i) k)) , i)) (sorted_list_of_set (tips G))))))
 in let Current = (add_set_list_tuple M, snd M)
 in foldl (app_if_blue_else_add_end G k) (fst Current)
 (linorder.sorted_list_of_set (top_le G) (anticone G (snd M))) 
  )"
  by auto
termination proof 
  let ?R = "measure ( \<lambda>(G, k). (card (verts G)))"
  show "wf ?R" by auto
next
  fix G::"('a::linorder,'b) pre_digraph"
  fix k::nat 
  fix x
  assume tD:  "\<not> \<not> tie_breakingDAG G"
  then have bD: "blockDAG G" using tie_breakingDAG_def by auto
  assume "card (verts G) \<noteq> 1"
  then have "card (verts G) > 1" using bD blockDAG.blockDAG_size_cases by auto 
  then have nT: "\<forall>x \<in> tips G. \<not> blockDAG.is_genesis_node G x"
    using blockDAG.tips_unequal_gen bD tips_def mem_Collect_eq
    by metis
  assume " x \<in> set (sorted_list_of_set (tips G))"
  then have in_t: "x \<in> tips G" using bD
    by (metis card_gt_0_iff length_pos_if_in_set length_sorted_list_of_set set_sorted_list_of_set) 
  then show "((reduce_past G x, k), G, k) \<in> measure (\<lambda>(G, k). card (verts G))"
    using blockDAG.reduce_less bD tips_def is_tip.simps
    by fastforce  
qed

lemma "class.linorder (top_le G)  (top_less G)" 
proof -
  fix G::"('a::linorder,'b) pre_digraph"
  consider (tD) "tie_breakingDAG G"| (ntD) "\<not> tie_breakingDAG G" by auto
  then show "class.linorder (top_le G) (top_less G)" 
  proof(cases)
    case tD  
    then have bD: "blockDAG G" by using tie_breakingDAG_def by auto
    show ?thesis 
    proof
      show "\<And>x y. top_less G x y = (top_le G x y \<and> \<not> top_le G y x)" using bD subs DAG.unidirectional
      wf_digraph.reachable1_reachable
        by (metis dual_order.order_iff_strict not_less_iff_gr_or_eq top_le.elims(1) top_less.elims(1)) 
    show "\<And>x. top_le G x x" by auto
    show "\<And>x y z. top_le G x y \<Longrightarrow> top_le G y z \<Longrightarrow> top_le G x z" 
    proof -
      fix x y z 
      assume "top_le G x y" 
      assume "top_le G y z"
      then consider "(z \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y)" | "(\<not>(z \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y) \<and> \<not>(y \<rightarrow>\<^sup>+\<^bsub>G\<^esub> z) \<and> y \<le> z)"
        by (metis tD top_le.simps)
      then show "top_le G x z"  
        oops
  next
    case ntD
    have les: "\<And>a b. top_le G a b \<equiv> a \<le> b" using top_le.simps top_less.simps ntD by auto
    have lesss: "\<And>a b. top_less G a b \<equiv> a < b"  using top_le.simps top_less.simps ntD by auto
    show "class.linorder (top_le G) (top_less G)" 
    proof
      show "\<And>x y. top_less G x y = (top_le G x y \<and> \<not> top_le G y x)" using les lesss by auto
      show "\<And>x. top_le G x x" by auto
      show "\<And>x y z. top_le G x y \<Longrightarrow> top_le G y z \<Longrightarrow> top_le G x z" using les lesss by auto
      show "\<And>x y. top_le G x y \<Longrightarrow> top_le G y x \<Longrightarrow> x = y" using les lesss by auto
      show "\<And>x y. top_le G x y \<or> top_le G y x" using les lesss by auto
  qed
  oops



end