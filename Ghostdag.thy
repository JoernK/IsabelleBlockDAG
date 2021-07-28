
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


fun top_insert:: "('a::linorder,'b) pre_digraph \<Rightarrow>'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "top_insert G [] a = [a]"
  | "top_insert G (b # L) a = (if (a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) then (b # top_insert G L a) else (a # ( b # L)))"

fun top_sort:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "top_sort G []= [] "
  | "top_sort G (a # L) = top_insert G (top_sort G L) a"


lemma in_insert: "set (top_insert G L a) = set L \<union> {a}" 
proof(induct L, simp_all, auto) qed 

lemma top_sort_con: "set (top_sort G L) = set L"
proof(induct L)
case Nil
then show ?case by auto
next
  case (Cons a L)
  then show ?case using top_sort.simps(2) in_insert insert_is_Un list.simps(15) sup_commute
    by (metis) 
qed


fun larger_blue_tuple ::
 "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> (('a set \<times> 'a list) \<times> 'a) \<Rightarrow> (('a set \<times> 'a list) \<times> 'a)"
  where "larger_blue_tuple A B = 
  (if (card (fst (fst A))) > (card (fst (fst B))) \<or> 
  (card (fst (fst A)) \<ge> card (fst (fst B)) \<and> snd A \<le> snd B) then A else B)"


fun add_set_list_tuple :: "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> ('a::linorder set \<times> 'a list)" 
  where "add_set_list_tuple ((S,L),a) = (S \<union> {a}, L @ [a])"

fun app_if_blue_else_add_end :: 
"('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a::linorder set \<times> 'a list)
 \<Rightarrow> ('a::linorder set \<times> 'a list)"  
where "app_if_blue_else_add_end G k a (S,L) = (if (kCluster G k (S \<union> {a})) 
then add_set_list_tuple ((S,L),a) else (S,L @ [a]))"

fun choose_max_blue_set :: "(('a::linorder set \<times> 'a list) \<times> 'a) list \<Rightarrow> (('a set \<times> 'a list) \<times> 'a)"
  where "choose_max_blue_set L = fold (larger_blue_tuple) L (hd L)" 


function OrderDAG :: "('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a set \<times> 'a list)" 
  where
  "OrderDAG G k =  
  (if (\<not> tie_breakingDAG G) then ({},[]) else 
  if (card (verts G) = 1)  then ({genesis_nodeAlt G},[genesis_nodeAlt G]) else
 let M =  choose_max_blue_set 
  ((map (\<lambda>i.(((OrderDAG (reduce_past G i) k)) , i)) (sorted_list_of_set (tips G))))
 in let Current = (add_set_list_tuple M, snd M)
 in fold (app_if_blue_else_add_end G k) (top_sort G (sorted_list_of_set (anticone G (snd M))))
 (fst Current))
 "
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


lemma app_if_blue_mono:
  assumes "finite S"
  shows  "(fst (S,L)) \<subseteq> (fst (app_if_blue_else_add_end G k a (S,L)))"
  unfolding app_if_blue_else_add_end.simps add_set_list_tuple.simps
  by (simp add: assms card_mono subset_insertI)

lemma app_if_blue_mono2:
  shows  "set (snd (S,L)) \<subseteq> set (snd (app_if_blue_else_add_end G k a (S,L) ))"
  unfolding app_if_blue_else_add_end.simps add_set_list_tuple.simps
  by (simp add: subsetI)



lemma app_if_blue_append:
  shows  "a \<in> set (snd (app_if_blue_else_add_end G k a (S,L) ))"
  unfolding app_if_blue_else_add_end.simps add_set_list_tuple.simps
  by simp

lemma app_if_blue_card_mono:
  assumes "finite S"
  shows  "card (fst (S,L)) \<le> card (fst (app_if_blue_else_add_end G k a (S,L)))"
  unfolding app_if_blue_else_add_end.simps add_set_list_tuple.simps
  by (simp add: assms card_mono subset_insertI)  
  

lemma larger_blue_tuple_mono:
  assumes "finite (fst V)"
  shows "larger_blue_tuple ((app_if_blue_else_add_end G k a V),b) (V,b)
       = ((app_if_blue_else_add_end G k a V),b)" 
  using assms app_if_blue_card_mono larger_blue_tuple.simps eq_refl
  by (metis fst_conv prod.collapse snd_conv) 


lemma larger_blue_tuple_subs:
  shows "larger_blue_tuple A B \<in> {A,B}" by auto

lemma choose_max_blue_avoid_empty:
  assumes "L \<noteq> []"
  shows "choose_max_blue_set L \<in> set L"
  unfolding choose_max_blue_set.simps 
proof (rule fold_invariant)
    show " \<And>x. x \<in> set L \<Longrightarrow> x \<in> set L" using assms by auto
  next 
    show "hd L \<in> set L" using assms by auto
  next 
    fix x s 
    assume "x \<in> set L"
    and "s \<in> set L"
    then show "larger_blue_tuple x s \<in> set L" using larger_blue_tuple.simps by auto
  qed

lemma fold_app_mono:
  assumes "x \<in> set (snd (S,L1))"
  shows " x \<in> set (snd (fold (app_if_blue_else_add_end G k) L2 (S,L1)))"
proof(rule fold_invariant)
  show "\<And>x. x \<in> set L2 \<Longrightarrow>  x \<in> set L2" by simp
  show "x \<in> set (snd (S, L1))" using assms(1) by simp
  show "\<And>xa s. xa \<in> set L2 \<Longrightarrow> x \<in> set (snd s) \<Longrightarrow> 
  x \<in> set (snd (app_if_blue_else_add_end G k xa s)) " by auto 
qed  

lemma fold_app_mono3: 
  assumes "set L1 \<subseteq> set L2"
  shows "set (snd (fold (app_if_blue_else_add_end G k) L (S1, L1)))
   \<subseteq> set (snd (fold (app_if_blue_else_add_end G k) L (S2, L2)))"
  using assms
proof(induction  L arbitrary: S1 S2 L1 L2)
  case Nil
  then show ?case using assms by auto
next
  case (Cons a L4)
  let ?L1.0 = "snd (app_if_blue_else_add_end G k a (S1, L1))"
  let ?L2.0 = "snd (app_if_blue_else_add_end G k a (S2, L2))"
  have "set ?L1.0 \<subseteq> set ?L2.0" using Cons(2) Ghostdag.app_if_blue_else_add_end.simps
      add_set_list_tuple.simps
    using empty_set insert_is_Un list.simps(15) set_append by auto 
  then have kk: "set (snd (fold (app_if_blue_else_add_end G k) L4 
  (fst (app_if_blue_else_add_end G k a (S1, L1)), ?L1.0)))
    \<subseteq> set (snd (fold (app_if_blue_else_add_end G k) L4 
  (fst (app_if_blue_else_add_end G k a (S2, L2)), ?L2.0)))" using Cons by blast
  have ee: "\<And>Q S. (app_if_blue_else_add_end G k a (S, Q)) =
   (fst (app_if_blue_else_add_end G k a (S, Q)), snd (app_if_blue_else_add_end G k a (S, Q)))"
    using app_if_blue_else_add_end.simps fst_def snd_def by auto 
  then show ?case unfolding fold_Cons comp_apply  using kk by auto     
qed
  

lemma fold_app_mono2:
  assumes "x \<in> set L2"
  shows "x \<in> set (snd (fold (app_if_blue_else_add_end G k) L2 (S,L1)))" 
  using assms
proof (induct L2)
  case Nil
  then show ?case by simp
next
  case (Cons a L2)
  then consider "x = a" | "x \<in> set L2" by auto
  then show ?case 
  proof(cases)
    case 1
    then show ?thesis unfolding fold_Cons comp_apply using  app_if_blue_append
      by (simp add: fold_app_mono) 
  next
    case 2
    then have " x \<in> set (snd (fold (app_if_blue_else_add_end G k) L2 (S, L1)))" using Cons by auto
    then show 
      "x \<in> set (snd (fold (app_if_blue_else_add_end G k) (a # L2) (S, L1)))"
    unfolding fold_Cons comp_apply using  fold_app_mono3 app_if_blue_mono2
    by (metis (no_types, hide_lams) old.prod.exhaust sndI subset_code(1)) 
  qed
qed

lemma (in tie_breakingDAG) OrderDAG_total: 
  shows "x \<in> verts G \<longrightarrow> x \<in> set (snd (OrderDAG G k))" 
proof(safe)
  have bD: "blockDAG G" using tie_breakingDAG_axioms tie_breakingDAG_def by auto
  assume x_in: "x \<in> verts G"
  then consider (cD1) "card (verts G) = 1"| (cDm) "card (verts G) \<noteq> 1" by auto 
  then show "x \<in> set (snd (OrderDAG G k))"
  proof(cases)
    case (cD1)
    then have "set (snd (OrderDAG G k)) = {genesis_nodeAlt G}" 
      using tie_breakingDAG_axioms OrderDAG.simps by auto
    then show ?thesis using x_in bD cD1
         genesis_nodeAlt_sound blockDAG.is_genesis_node.simps
      using gen_gen gen_graph_all_one by fastforce 
  next
    case (cDm)
    then show ?thesis
    proof -
      obtain pp where pp_in: "pp =  (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G)))" using tips_exist by auto
      have mm: "choose_max_blue_set pp \<in> set pp" using pp_in choose_max_blue_avoid_empty tips_finite
         list.map_disc_iff sorted_list_of_set_eq_Nil_iff tips_not_empty
        by (metis (mono_tags, lifting))  
      then have kk: "snd (choose_max_blue_set pp) \<in> set (map  snd pp)"
        by auto 
      have mm2: "\<And>L. (map snd (map (\<lambda>i. ((OrderDAG (reduce_past G i) k) , i)) L)) =  L" 
      proof -
        fix L
        show "map snd (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i)) L) = L"
        proof(induct L)
          case Nil
          then show ?case by auto
        next
          case (Cons a L)
          then show ?case by auto
        qed
      qed
      have "set (map snd pp) = set (sorted_list_of_set (tips G))" 
        using mm2 pp_in  by auto
      then have tt2: "snd (choose_max_blue_set pp) \<in> tips G"
        using tips_finite sorted_list_of_set(1) kk  by auto  
      show ?thesis 
         proof(rule blockDAG.tips_cases)
         show "blockDAG G" using bD by auto
         show "snd (choose_max_blue_set pp) \<in> tips G" using tt2 by auto
         show "x \<in> verts G" using x_in by auto
       next  
        assume as1: "x = snd (choose_max_blue_set pp)"
        obtain Cur where cur_in: "Cur = fst (add_set_list_tuple (choose_max_blue_set pp), x)"
            by auto
        have "x \<in> set (snd(Cur))" 
          unfolding as1 using  add_set_list_tuple.simps cur_in
          add_set_list_tuple.cases snd_conv insertI1 snd_conv
          by (metis (mono_tags, hide_lams) Un_insert_right fst_conv list.simps(15) set_append) 
        then have "x \<in> set (snd (fold (app_if_blue_else_add_end G k)
                   (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp))))) (Cur)))"
          using  finite_verts fold_app_mono surj_pair
        by (metis)
      then show ?thesis unfolding pp_in cur_in using tie_breakingDAG_axioms OrderDAG.simps cDm
         fst_conv 
        by (metis (mono_tags, lifting)) 
      next
        assume anti: "x \<in> anticone G (snd (choose_max_blue_set pp))" 
        obtain ttt where ttt_in: "ttt = fst (add_set_list_tuple (choose_max_blue_set pp)
        , snd (choose_max_blue_set pp))" by auto
        have "x \<in> set (snd (fold (app_if_blue_else_add_end G k)
                 (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp)))))
                   ttt))" 
          using pp_in sorted_list_of_set(1) anti
         anticon_finite fold_app_mono2 surj_pair top_sort_con  by metis 
        then show "x \<in> set (snd (OrderDAG G k))" using OrderDAG.simps pp_in bD cDm ttt_in 
          by (metis (no_types, lifting) map_eq_conv tie_breakingDAG_axioms) 
      next 
        assume  as2: "x \<in> past_nodes G (snd (choose_max_blue_set pp))"
        show "x \<in> set (snd (OrderDAG G k))" using tie_breakingDAG_axioms pp_in
          
        


(*
proof (safe, induction G rule: blockDAG_induct)
  case fund
  then show ?case using tie_breakingDAG_def tie_breakingDAG_axioms by auto
next 
  case (base V)
  then have cD: "card (verts (blockDAG.gen_graph V)) = 1" using blockDAG.gen_graph_one by simp 
  have tB: "tie_breakingDAG ((blockDAG.gen_graph V)) \<and> blockDAG ((blockDAG.gen_graph V)) "
    using tie_breakingDAG_def base.hyps blockDAG.gen_graph_sound by auto
  then have res: " set (snd (OrderDAG (blockDAG.gen_graph V) k)) 
  = {genesis_nodeAlt (blockDAG.gen_graph V)}"
  using OrderDAG.simps cD by auto
  assume x_in: "x \<in> verts (blockDAG.gen_graph V)"
  then have "blockDAG.is_genesis_node (blockDAG.gen_graph V) x"
    by (metis blockDAG.no_empty_blockDAG blockDAG.reduce_less blockDAG.reduce_past_dagbased
        cD gr_implies_not0 less_one tB)
  then have "genesis_nodeAlt (blockDAG.gen_graph V) = x"
    by (metis blockDAG.genesis_unique_exists cD genesis_nodeAlt_one_sound tB) 
  then show "x \<in> set (snd (OrderDAG (blockDAG.gen_graph V) k))"
    using res genesis_nodeAlt_sound tB blockDAG.unique_genesis
    by auto 
next
  case (step H)
  then show ?case 
qed
*)

end