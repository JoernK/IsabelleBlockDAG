
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

fun larger_blue_tuple ::
 "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> (('a set \<times> 'a list) \<times> 'a) \<Rightarrow> (('a set \<times> 'a list) \<times> 'a)"
  where "larger_blue_tuple A B = 
  (if (card (fst (fst A))) > (card (fst (fst B))) \<or> 
  (card (fst (fst A)) \<ge> card (fst (fst B)) \<and> snd A \<le> snd B) then A else B)"


fun add_set_list_tuple :: "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> ('a::linorder set \<times> 'a list)" 
  where "add_set_list_tuple ((S,L),a) = (S \<union> {a}, L @ [a])"

fun app_if_blue_else_add_end :: 
"('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a::linorder set \<times> 'a list)
 \<Rightarrow> 'a \<Rightarrow> ('a::linorder set \<times> 'a list)"  
where "app_if_blue_else_add_end G k (S,L) a = (if (kCluster G k (S \<union> {a})) 
then add_set_list_tuple ((S,L),a) else (S,L @ [a]))"

fun choose_max_blue_set :: "(('a::linorder set \<times> 'a list) \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> (('a set \<times> 'a list) \<times> 'a)"
  where "choose_max_blue_set L def = foldr (larger_blue_tuple) L (({},[]),def)" 


function OrderDAG :: "('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a set \<times> 'a list)" 
  where
  "OrderDAG G k =  
  (if (\<not> tie_breakingDAG G) then ({},[]) else 
  if (card (verts G) = 1)  then ({genesis_nodeAlt G},[genesis_nodeAlt G]) else
 let M =  choose_max_blue_set 
  ((map (\<lambda>i.(((OrderDAG (reduce_past G i) k)) , i)) (sorted_list_of_set (tips G))))
   (genesis_nodeAlt G)
 in let Current = (add_set_list_tuple M, snd M)
 in foldl (app_if_blue_else_add_end G k) (fst Current)
 (sorted_list_of_set (anticone G (snd M))))"
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

   
      
end