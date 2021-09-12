theory Ghostdag_Properties
  imports Ghostdag Extend_blockDAG Properties 
begin


section \<open>GHOSTDAG properties\<close>

subsection \<open>GHOSTDAG Order Preserving\<close>

lemma GhostDAG_preserving:
  assumes "blockDAG G"
    and "x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y"
  shows "(y,x) \<in> GHOSTDAG k G"
  unfolding GHOSTDAG.simps using assms 
proof(induct G k arbitrary: x y rule: OrderDAG.induct )
  case (1 G k)
  then show ?case proof (cases G rule: OrderDAG_casesAlt)
    case ntB
    then show ?thesis using 1 by auto
  next
    case one
    then have "\<not> x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y"
      using subs wf_digraph.reachable1_in_verts 1
      by (metis DAG.cycle_free OrderDAG_casesAlt blockDAG.reduce_less
          blockDAG.reduce_past_dagbased blockDAG.unique_genesis less_one not_one_less_zero) 
    then show ?thesis using 1 by simp
  next  
    case more
    obtain pp where pp_in: "pp =  (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G)))" using blockDAG.tips_exist by auto
    have backw: "list_to_rel (snd (OrderDAG G k)) = 
                     list_to_rel (snd (fold (app_if_blue_else_add_end G k)
                    (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp)))))
                   (add_set_list_tuple (choose_max_blue_set pp))))"
      using OrderDAG.simps less_irrefl_nat more pp_in
      by (metis (mono_tags, lifting))
    obtain S where s_in: 
      "(top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp))))) = S" by simp
    obtain t where t_in : "(add_set_list_tuple (choose_max_blue_set pp)) = t" by simp
    obtain ma where ma_def: "ma = (snd (choose_max_blue_set pp))" by simp
    have ma_vert: "ma \<in> verts G" unfolding ma_def using chosen_map_simps(2) digraph.tips_in_verts
        more(1) subs subsetD pp_in by blast 
    have ma_tip: "is_tip G ma" unfolding ma_def
      using chosen_map_simps(2) more pp_in  tips_tips
      by (metis (no_types))          
    then have no_gen: "\<not> blockDAG.is_genesis_node G ma" unfolding ma_def  using pp_in 
        blockDAG.tips_unequal_gen more
      by metis
    then have red_bd: "blockDAG (reduce_past G ma)"  
      using blockDAG.reduce_past_dagbased more ma_vert unfolding ma_def
      by auto
    consider (ind) "x \<in> past_nodes G ma \<and> y \<in> past_nodes G ma"
      |(x_in) "x \<notin>  past_nodes G ma \<and> y \<in> past_nodes G ma"
      |(y_in) "x \<in>  past_nodes G ma \<and> y \<notin> past_nodes G ma"
      |(both_nin) "x \<notin>  past_nodes G ma \<and> y \<notin> past_nodes G ma" by auto
    then show ?thesis proof(cases)
      case ind
      then have "x \<rightarrow>\<^sup>+\<^bsub>reduce_past G ma\<^esub> y" using DAG.reduce_past_path2 more  
          1 subs
        by (metis) 
      moreover have ma_tips: " ma \<in> set (sorted_list_of_set (tips G))" 
        using chosen_map_simps(1) pp_in more(1) 
        unfolding ma_def by auto
      ultimately have "(y,x) \<in> list_to_rel (snd (OrderDAG (reduce_past G ma) k))"
        unfolding ma_def
        using more 1 ind less_numeral_extra(4) ma_def red_bd
        by (metis)
      then have "(y,x) \<in> list_to_rel (snd (fst (choose_max_blue_set pp)))"
        using chosen_map_simps(6) pp_in 1 unfolding ma_def by fastforce
      then have rel_base: "(y,x) \<in> list_to_rel (snd (add_set_list_tuple(choose_max_blue_set pp)))"
        using add_set_list_tuple.simps list_to_rel_mono prod.collapse snd_conv
        by metis 

      show ?thesis 
        unfolding  ma_def backw s_in
        using rel_base  unfolding t_in 
        using fold_app_mono_rel prod.collapse
        by metis       
    next
      case x_in
      then have "y \<in> set (snd (OrderDAG (reduce_past G ma) k))"
        unfolding reduce_past.simps using induce_subgraph_verts Verts_in_OrderDAG 
          more red_bd reduce_past.elims
        by (metis)
      then have y_in_base: "y \<in> set (snd (fst (choose_max_blue_set pp)))"
        unfolding ma_def using chosen_map_simps(6) more pp_in
        by fastforce 
      consider (x_t) "x = ma" | (x_ant) "x \<in> anticone G ma" using DAG.verts_comp2 
          subs 1  ma_tip ma_vert 
          mem_Collect_eq tips_def wf_digraph.reachable1_in_verts(1) x_in
        by (metis (no_types, lifting)) 
      then show ?thesis proof(cases)
        case x_t
        then have "(y,x) \<in>  list_to_rel (snd (add_set_list_tuple (choose_max_blue_set pp)))"
          unfolding x_t ma_def 
          using y_in_base add_set_list_tuple.simps list_to_rel_append prod.collapse sndI
          by metis
        then show ?thesis unfolding  ma_def backw s_in
          unfolding t_in 
          using fold_app_mono_rel prod.collapse
          by metis     
      next
        case x_ant
        then have "x \<in> set (sorted_list_of_set (anticone G ma))" 
          using sorted_list_of_set(1) more subs
          by (metis DAG.anticon_finite) 
        moreover have "y \<in> set (snd (add_set_list_tuple (choose_max_blue_set pp)))"
          using  add_set_list_tuple_mono in_mono prod.collapse y_in_base
          by (metis (mono_tags, lifting)) 
        ultimately show ?thesis unfolding backw
          by (metis fold_app_app_rel ma_def prod.collapse top_sort_con) 
      qed
    next
      case y_in
      then have "y \<in> past_nodes G ma" unfolding past_nodes.simps using 1(2,3)
          wf_digraph.reachable1_in_verts(2) subs mem_Collect_eq trancl_trans
        by (metis (mono_tags, lifting)) 
      then show ?thesis using y_in by simp 
    next
      case both_nin
      consider (x_t) "x = ma" | (x_ant) "x \<in> anticone G ma" using DAG.verts_comp2 
          subs 1  ma_tip ma_vert 
          mem_Collect_eq tips_def wf_digraph.reachable1_in_verts(1) both_nin
        by (metis (no_types, lifting)) 
      then show ?thesis proof(cases)
        case x_t 
        have "y \<in> past_nodes G ma" using 1(3) more 
            past_nodes.simps unfolding x_t
          by (simp add: subs wf_digraph.reachable1_in_verts(2)) 
        then show ?thesis using both_nin by simp 
      next
        have y_ina: "y \<in> anticone G ma" 
        proof(rule ccontr) 
          assume "\<not> y \<in> anticone G ma "
          then have "y = ma"
            unfolding anticone.simps using subs wf_digraph.reachable1_in_verts(2) 1(2,3) 
              ma_tip both_nin
            by fastforce  
          then have "x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> ma" using 1(3) by auto
          then show False using subs  1(2)
            by (metis wf_digraph.tips_not_referenced ma_tip)  
        qed
        case x_ant
        then have "(y,x) \<in> list_to_rel (top_sort G (sorted_list_of_set (anticone G ma)))"
          using y_ina DAG.anticon_finite subs 1(2,3) sorted_list_of_set(1) top_sort_rel
          by metis
        then show ?thesis unfolding backw ma_def  using
            fold_app_mono list_to_rel_mono2
          by (metis old.prod.exhaust)
      qed
    qed
  qed
qed


lemma "\<forall>k. Order_Preserving (GHOSTDAG k)"
  unfolding Order_Preserving_def 
  using GhostDAG_preserving
  by blast 



subsection \<open>GHOSTDAG Linear Order\<close>



lemma GhostDAG_linear: 
  assumes "blockDAG G" 
  shows "linear_order_on (verts G) (GHOSTDAG k G)"
  unfolding GHOSTDAG.simps 
  using list_order_linear OrderDAG_distinct OrderDAG_total assms by metis

lemma "\<forall>k. Linear_Order (GHOSTDAG k)"
  unfolding Linear_Order_def 
  using GhostDAG_linear by blast


subsection \<open>GHOSTDAG One Appending Monotone\<close>

lemma OrderDAG_append_one:
  assumes "Honest_Append_One G G_A a"
  shows "snd (OrderDAG G_A k) = snd (OrderDAG G k) @ [a]"
proof -
  have bD_A: "blockDAG G_A" using assms Append_One.bD_A Honest_Append_One_def
    by metis
  have g1: "card (verts G_A) \<noteq> 1" 
    using assms Append_One.append_greater_1 Honest_Append_One_def less_not_refl
    by metis
  have "(tips G_A) = {a}" using Honest_Append_One.append_is_only_tip assms by metis
  then have tips_app: "(sorted_list_of_set (tips G_A)) = [a]" by auto 
  obtain the_map where the_map_in:
   "the_map = ((map (\<lambda>i.(((OrderDAG (reduce_past G_A i) k)) , i)) (sorted_list_of_set (tips G_A))))"
    by auto
  then have m_l: " the_map = [((OrderDAG (reduce_past G_A a) k), a)]"
    unfolding the_map_in using tips_app by auto
  then have c_l: "choose_max_blue_set the_map
  = ((OrderDAG (reduce_past G_A a) k), a)"
    by (metis (no_types, lifting) choose_max_blue_avoid_empty list.discI list.set_cases set_ConsD)
  then have bb: "choose_max_blue_set the_map
  = ((OrderDAG G k), a)" using  Honest_Append_One.reduce_append assms
    by metis 
  let ?M = "choose_max_blue_set the_map"
  have "anticone G_A (snd ?M)= {}" 
    unfolding c_l 
    using assms Honest_Append_One.append_no_anticone sndI
    by metis
  then have eml: "(top_sort G_A (sorted_list_of_set (anticone G_A (snd ?M)))) = []"
    by (metis sorted_list_of_set_empty top_sort.simps(1)) 
  then have "(fold (app_if_blue_else_add_end G k) 
  (top_sort G_A (sorted_list_of_set (anticone G_A (snd ?M))))
 (add_set_list_tuple ?M)) = (add_set_list_tuple ?M)"  
    using bb by simp 
  moreover have " snd (add_set_list_tuple ?M) = snd (OrderDAG G k) @ [a]"
    unfolding bb 
    using add_set_list_tuple.simps Pair_inject add_set_list_tuple.elims snd_conv
    by (metis (mono_tags, lifting)) 
  ultimately show ?thesis 
    unfolding the_map_in 
    using OrderDAG.simps bD_A g1 eml fold_simps(1) list.simps(8) list.simps(9) the_map_in tips_app
    by (metis (no_types, lifting)) 
qed 
  
lemma "\<forall>k. Honest_One_Appending_Monotone (GHOSTDAG k)"
  unfolding Honest_One_Appending_Monotone_def GHOSTDAG.simps 
  using list_to_rel_mono OrderDAG_append_one
  by metis

end