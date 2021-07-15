
theory Ghostdag  
  imports blockDAG "HOL-Library.Product_Lexorder"
begin


fun max_blue_set ::
 "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> (('a set \<times> 'a list) \<times> 'a) \<Rightarrow> bool"
  where "max_blue_set ((B1 , C1),a1) ((B2 , C2),a2) = 
  (True \<longleftrightarrow> (card B1) > (card B2) \<or> (card B1 \<ge> card B2 \<and> a1 \<le> a2))"

function OrderDAG :: "('a::linorder,'b) pre_digraph \<Rightarrow> int \<Rightarrow> ('a set \<times> 'a list)" 
  where
  "OrderDAG G k =  
  (if (\<not> blockDAG G) then ({},[]) else 
  if (card (verts G) = 1)  then ({blockDAG.genesis_node G},[blockDAG.genesis_node G]) else
  fst (linorder.Max max_blue_set
 (set ((map (\<lambda>i.(((OrderDAG (reduce_past G i) k)) , i)) (sorted_list_of_set (tips G)))))))"
  by auto
termination proof 
  let ?R = "measure ( \<lambda>(G, k). (card (verts G)))"
  show "wf ?R" by auto
next
  fix G::"('a::linorder,'b) pre_digraph"
  fix k::int 
  fix x
  assume bD: "\<not> \<not> blockDAG G"
  assume "card (verts G) \<noteq> 1"
  then have "card (verts G) > 1" using bD  blockDAG.blockDAG_size_cases by auto 
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

end