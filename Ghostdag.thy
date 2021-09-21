
theory Ghostdag  
  imports blockDAG Utils TopSort
begin

section \<open>GHOSTDAG\<close>
text \<open>Based on the GHOSTDAG blockDAG consensus algorithmus by Sompolinsky and Zohar 2018\<close>


subsection \<open>Funcitions and Definitions\<close>    

text \<open>Function to compare the size of set and break ties. Used for the GHOSTDAG maximum blue 
      cluster selection\<close>
fun larger_blue_tuple ::
  "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> (('a set \<times> 'a list) \<times> 'a) \<Rightarrow> (('a set \<times> 'a list) \<times> 'a)"
  where "larger_blue_tuple A B = 
  (if (card (fst (fst A))) > (card (fst (fst B))) \<or> 
  (card (fst (fst A)) \<ge> card (fst (fst B)) \<and> snd A \<le> snd B) then A else B)"

text \<open>Function to add node $a$ to a tuple of a set S and List L\<close>
fun add_set_list_tuple :: "(('a::linorder set \<times> 'a list)  \<times> 'a) \<Rightarrow> ('a::linorder set \<times> 'a list)" 
  where "add_set_list_tuple ((S,L),a) = (S \<union> {a}, L @ [a])"

text \<open>Function that adds a node $a$ to a kCluster $S$, if $S + {a}$ remains a kCluster.
    Also adds $a$ to the end of list $L$\<close>
fun app_if_blue_else_add_end :: 
  "('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a::linorder set \<times> 'a list)
 \<Rightarrow> ('a::linorder set \<times> 'a list)"  
  where "app_if_blue_else_add_end G k a (S,L) = (if (kCluster G k (S \<union> {a})) 
then add_set_list_tuple ((S,L),a) else (S,L @ [a]))"

text \<open>Function to select the largest $((S,L),a)$ according to $larger-blue-tuple$\<close>
fun choose_max_blue_set :: "(('a::linorder set \<times> 'a list) \<times> 'a) list \<Rightarrow> (('a set \<times> 'a list) \<times> 'a)"
  where "choose_max_blue_set L = fold (larger_blue_tuple) L (hd L)" 

text \<open>GHOSTDAG ordering algorithm\<close>
function OrderDAG :: "('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a set \<times> 'a list)" 
  where
    "OrderDAG G k =  
  (if (\<not> blockDAG G) then ({},[]) else 
  if (card (verts G) = 1)  then ({genesis_nodeAlt G},[genesis_nodeAlt G]) else
 let M =  choose_max_blue_set 
  ((map (\<lambda>i.(((OrderDAG (reduce_past G i) k)) , i)) (sorted_list_of_set (tips G))))
 in fold (app_if_blue_else_add_end G k) (top_sort G (sorted_list_of_set (anticone G (snd M))))
 (add_set_list_tuple M))
 "
  by auto
termination proof 
  let ?R = "measure ( \<lambda>(G, k). (card (verts G)))"
  show "wf ?R" by auto
next
  fix G::"('a::linorder,'b) pre_digraph"
  fix k::nat 
  fix x
  assume bD:  "\<not> \<not> blockDAG G"
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




text \<open>Creating a relation on verts $G$ based on the GHOSTDAG OrderDAG algorithm\<close>
fun GHOSTDAG :: " nat \<Rightarrow> ('a::linorder,'b) pre_digraph \<Rightarrow> 'a rel"
  where "GHOSTDAG k G = list_to_rel (snd (OrderDAG G k))"

subsection\<open>Soundness\<close>

lemma OrderDAG_casesAlt:
  obtains (ntB) "\<not> blockDAG G" 
  | (one) "blockDAG G \<and> card (verts G) = 1"
  | (more) "blockDAG G \<and> card (verts G) > 1"
  using  blockDAG.blockDAG_size_cases by auto



subsubsection \<open>Soundness of the $add-set-list$ function\<close>

lemma add_set_list_tuple_mono:
  shows "set L \<subseteq> set (snd (add_set_list_tuple ((S,L),a)))"
  using add_set_list_tuple.simps by auto

lemma add_set_list_tuple_mono2:
  shows "set (snd (add_set_list_tuple ((S,L),a))) \<subseteq> set L \<union> {a} "
  using add_set_list_tuple.simps by auto

lemma add_set_list_tuple_length:
  shows "length (snd (add_set_list_tuple ((S,L),a))) = Suc (length L)"
proof(induct L, auto) qed


subsubsection \<open>Soundness of the $add-if-blue$ function\<close>

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

lemma app_if_blue_mono3:
  shows  "set (snd (app_if_blue_else_add_end G k a (S,L))) \<subseteq> set L \<union> {a}"
  unfolding app_if_blue_else_add_end.simps add_set_list_tuple.simps
  by (simp add: subsetI)

lemma app_if_blue_mono4:
  assumes "set L1 \<subseteq> set L2"
  shows  "set (snd (app_if_blue_else_add_end G k a (S,L1)))
   \<subseteq> set (snd (app_if_blue_else_add_end G k a (S2,L2)))"
  unfolding app_if_blue_else_add_end.simps add_set_list_tuple.simps
  using assms by auto


lemma app_if_blue_card_mono:
  assumes "finite S"
  shows  "card (fst (S,L)) \<le> card (fst (app_if_blue_else_add_end G k a (S,L)))"
  unfolding app_if_blue_else_add_end.simps add_set_list_tuple.simps
  by (simp add: assms card_mono subset_insertI)  



lemma app_if_blue_else_add_end_length:
  shows "length (snd (app_if_blue_else_add_end G k a (S,L))) = Suc (length  L)"
proof(induction L, auto) qed




subsubsection \<open>Soundness of the $larger-blue-tuple$ comparison\<close>

lemma larger_blue_tuple_mono:
  assumes "finite (fst V)"
  shows "larger_blue_tuple ((app_if_blue_else_add_end G k a V),b) (V,b)
       = ((app_if_blue_else_add_end G k a V),b)" 
  using assms app_if_blue_card_mono larger_blue_tuple.simps eq_refl
  by (metis fst_conv prod.collapse snd_conv) 


lemma larger_blue_tuple_subs:
  shows "larger_blue_tuple A B \<in> {A,B}" by auto


subsubsection \<open>Soundness of the $choose_max_blue_set$ function\<close>
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


subsubsection \<open>Auxiliary lemmas for OrderDAG\<close>

lemma fold_app_length:
  shows "length (snd  (fold (app_if_blue_else_add_end G k) 
  L1 PL2)) = length L1 + length (snd PL2)"
proof(induct L1 arbitrary: PL2)
  case Nil
  then show ?case by auto
next
  case (Cons a L1)
  then show ?case unfolding fold_Cons comp_apply using app_if_blue_else_add_end_length
    by (metis add_Suc add_Suc_right length_Cons old.prod.exhaust snd_conv) 
qed

lemma fold_app_mono:
  shows "snd (fold (app_if_blue_else_add_end G k) L2 (S,L1)) = L1 @ L2 "
proof(induct L2 arbitrary: S L1, simp)
  case (Cons a L2)
  then show ?case unfolding fold_simps(2) using app_if_blue_else_add_end.simps
    by simp
qed


lemma fold_app_mono1:
  assumes "x \<in> set (snd (S,L1))"
  shows " x \<in> set (snd (fold (app_if_blue_else_add_end G k) L2 (S2,L1)))"
  using fold_app_mono
  by (metis Cons_eq_appendI append.assoc assms in_set_conv_decomp sndI) 

lemma fold_app_mono2:
  assumes "x \<in> set L2"
  shows "x \<in> set (snd (fold (app_if_blue_else_add_end G k) L2 (S,L1)))" 
  using assms unfolding fold_app_mono by auto

lemma fold_app_mono3: 
  assumes "set L1 \<subseteq> set L2"
  shows "set (snd (fold (app_if_blue_else_add_end G k) L (S1, L1)))
   \<subseteq> set (snd (fold (app_if_blue_else_add_end G k) L (S2, L2)))"
  using assms unfolding fold_app_mono
  by auto 


lemma fold_app_mono_ex: 
  shows "set (snd (fold (app_if_blue_else_add_end G k) L2 (S,L1))) = (set L2 \<union> set L1)" 
  unfolding fold_app_mono by auto


lemma fold_app_mono_rel: 
  assumes "(x,y) \<in> list_to_rel L1"
  shows "(x,y) \<in> list_to_rel (snd (fold (app_if_blue_else_add_end G k) L2 (S,L1)))" 
  using assms 
proof(induct L2 arbitrary: S L1, simp)
  case (Cons a L2)
  then show ?case 
    unfolding fold.simps(2) comp_apply 
    using list_to_rel_mono app_if_blue_else_add_end.simps
    by (metis add_set_list_tuple.simps prod.collapse snd_conv)
qed

lemma fold_app_mono_rel2: 
  assumes "(x,y) \<in> list_to_rel L2"
  shows "(x,y) \<in> list_to_rel (snd (fold (app_if_blue_else_add_end G k) L2 (S,L1)))" 
  using assms
  by (simp add: fold_app_mono list_to_rel_mono2) 

lemma fold_app_app_rel: 
  assumes "x \<in> set L1"
    and "y \<in> set L2"
  shows "(x,y) \<in> list_to_rel (snd (fold (app_if_blue_else_add_end G k) L2 (S,L1)))" 
  using assms 
proof(induct L2 arbitrary: S L1, simp)
  case (Cons a L2)
  then show ?case 
    unfolding fold.simps(2) comp_apply 
    using list_to_rel_append app_if_blue_else_add_end.simps
    by (metis Un_iff add_set_list_tuple.simps fold_app_mono_rel set_ConsD set_append)  
qed

lemma chosen_max_tip:
  assumes "blockDAG G"
  assumes "x = snd ( choose_max_blue_set (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G))))" 
  shows  "x \<in> set (sorted_list_of_set (tips G))" and " x \<in> tips G"
proof - 
  interpret bD: blockDAG using assms by auto
  obtain pp where pp_in: "pp =  (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
   (sorted_list_of_set (tips G)))" using blockDAG.tips_exist by auto
  have mm: "choose_max_blue_set pp \<in> set pp" using pp_in choose_max_blue_avoid_empty
      bD.tips_finite 
      list.map_disc_iff sorted_list_of_set_eq_Nil_iff bD.tips_not_empty 
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
  then show "x \<in> set (sorted_list_of_set (tips G))" using pp_in assms(2) kk by blast 
  then show "x \<in> tips G"
    using bD.tips_finite sorted_list_of_set(1) kk assms pp_in by auto
qed


lemma chosen_map_simps1:
  assumes " x \<in> set  (map (\<lambda>i. (P i, i)) L)"
  shows  "fst x = P (snd x)"
  using assms
proof(induct L, auto) qed

lemma chosen_map_simps:
  assumes "blockDAG G"
  assumes "x = map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G))" 
  shows  "snd  (choose_max_blue_set x) \<in> set (sorted_list_of_set (tips G))" 
    and  "snd (choose_max_blue_set x) \<in> tips G"
    and "set (map snd x) = set (sorted_list_of_set (tips G))"
    and "choose_max_blue_set x \<in> set x"
    and "\<not> blockDAG.is_genesis_node G (snd (choose_max_blue_set x)) \<Longrightarrow>
  blockDAG (reduce_past G (snd (choose_max_blue_set x)))"
    and "OrderDAG (reduce_past G (snd (choose_max_blue_set x))) k = fst (choose_max_blue_set x)"
proof - 
  interpret bD: blockDAG using assms(1) by auto
  obtain pp where pp_in: "pp =  (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
   (sorted_list_of_set (tips G)))" using blockDAG.tips_exist by auto
  have mm: "choose_max_blue_set pp \<in> set pp" using pp_in choose_max_blue_avoid_empty
      bD.tips_finite
      list.map_disc_iff sorted_list_of_set_eq_Nil_iff bD.tips_not_empty 
    by (metis (mono_tags, lifting))  
  then have kk: "snd (choose_max_blue_set pp) \<in> set (map  snd pp)"
    by auto 
  have seteq: "set (map snd pp) = set (sorted_list_of_set (tips G))" 
    using map_snd_map pp_in  by auto
  then show "snd (choose_max_blue_set x) \<in> set (sorted_list_of_set (tips G))" 
    using pp_in assms(2) kk by blast 
  then show tip: "snd (choose_max_blue_set x) \<in> tips G"
    using bD.tips_finite sorted_list_of_set(1) kk pp_in by auto
  show "set (map snd x) = set (sorted_list_of_set (tips G))"
    using map_snd_map assms(2) 
    by simp
  then show "choose_max_blue_set x \<in> set x" using seteq pp_in assms(2)
      mm by blast 
  show "OrderDAG (reduce_past G (snd (choose_max_blue_set x))) k = fst (choose_max_blue_set x)"
    by (metis (no_types) assms(2) chosen_map_simps1 mm pp_in) 
  assume "\<not> blockDAG.is_genesis_node G (snd (choose_max_blue_set x))"
  then show " blockDAG (reduce_past G (snd (choose_max_blue_set x)))"
    using tip bD.reduce_past_dagbased bD.tips_in_verts subsetD
    by metis    
qed

subsubsection \<open>OrderDAG soundness\<close>

lemma Verts_in_OrderDAG: 
  assumes "blockDAG G"
    and "x \<in> verts G"
  shows "x \<in> set (snd (OrderDAG G k))"
  using assms
proof(induct G k  arbitrary: x rule: OrderDAG.induct)
  case (1 G k x)
  then have bD: "blockDAG G" by auto
  assume x_in: "x \<in> verts G"
  then consider (cD1) "card (verts G) = 1"| (cDm) "card (verts G) \<noteq> 1" by auto 
  then show "x \<in> set (snd (OrderDAG G k))"
  proof(cases)
    case (cD1)
    then have "set (snd (OrderDAG G k)) = {genesis_nodeAlt G}" 
      using 1 OrderDAG.simps by auto
    then show ?thesis using x_in bD cD1
        genesis_nodeAlt_sound blockDAG.is_genesis_node.simps
      using 1
      by (metis card_1_singletonE singletonD) 
  next
    case (cDm)
    then show ?thesis
    proof -
      obtain pp where pp_in: "pp =  (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G)))" using blockDAG.tips_exist by auto
      then have tt2: "snd (choose_max_blue_set pp) \<in> tips G"
        using chosen_map_simps bD
        by blast   
      show ?thesis 
      proof(rule blockDAG.tips_cases)
        show "blockDAG G" using bD by auto
        show "snd (choose_max_blue_set pp) \<in> tips G" using tt2 by auto
        show "x \<in> verts G" using x_in by auto
      next  
        assume as1: "x = snd (choose_max_blue_set pp)"
        obtain fCur where fcur_in: "fCur = add_set_list_tuple (choose_max_blue_set pp)"
          by auto
        have "x \<in> set (snd(fCur))" 
          unfolding as1 using  add_set_list_tuple.simps fcur_in
            add_set_list_tuple.cases snd_conv insertI1 snd_conv
          by (metis (mono_tags, hide_lams) Un_insert_right fst_conv list.simps(15) set_append) 
        then have "x \<in> set (snd (fold (app_if_blue_else_add_end G k)
                   (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp))))) (fCur)))"
          using  fold_app_mono1 surj_pair
          by (metis)
        then show ?thesis unfolding pp_in fcur_in using 1 OrderDAG.simps cDm
          by (metis (mono_tags, lifting)) 
      next
        assume anti: "x \<in> anticone G (snd (choose_max_blue_set pp))" 
        obtain ttt where ttt_in: "ttt = add_set_list_tuple (choose_max_blue_set pp)" by auto
        have "x \<in> set (snd (fold (app_if_blue_else_add_end G k)
                 (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp)))))
                   ttt))" 
          using pp_in sorted_list_of_set(1) anti bD subs(1)
            DAG.anticon_finite fold_app_mono2 surj_pair top_sort_con  by metis 
        then show "x \<in> set (snd (OrderDAG G k))" using OrderDAG.simps pp_in bD cDm ttt_in 1
          by (metis (no_types, lifting) map_eq_conv) 
      next 
        assume  as2: "x \<in> past_nodes G (snd (choose_max_blue_set pp))"
        then have pas: "x \<in> verts (reduce_past G (snd (choose_max_blue_set pp)))" 
          using reduce_past.simps induce_subgraph_verts by auto
        have cd1: "card (verts G) > 1" using cDm bD
          using blockDAG.blockDAG_size_cases by blast 
        have "(snd (choose_max_blue_set pp)) \<in> set (sorted_list_of_set (tips G))" using tt2
            digraph.tips_finite bD subs sorted_list_of_set(1)
          by blast 
        moreover 
        have "blockDAG (reduce_past G (snd (choose_max_blue_set pp)))" using 
            blockDAG.reduce_past_dagbased bD tt2  blockDAG.tips_unequal_gen 
            cd1 tips_def CollectD by metis
        ultimately have bass: 
          "x \<in> set ((snd (OrderDAG (reduce_past G (snd (choose_max_blue_set pp))) k)))" 
          using  pp_in 1 cDm tt2 pas by metis
        then have in_F: "x \<in> set (snd ( fst ((choose_max_blue_set pp))))" 
          using x_in chosen_map_simps(6) pp_in
          using bD by fastforce  
        then have "x \<in> set (snd (fold (app_if_blue_else_add_end G k)
         (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp)))))
         (fst((choose_max_blue_set pp)))))"
          by (metis fold_app_mono1 in_F prod.collapse) 
        moreover have "OrderDAG G k = (fold (app_if_blue_else_add_end G k)
         (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp)))))
         (add_set_list_tuple (choose_max_blue_set pp)))" using cDm 1 OrderDAG.simps pp_in
          by (metis (no_types, lifting) map_eq_conv) 
        then show "x \<in> set (snd (OrderDAG G k))"
          by (metis (no_types, lifting) add_set_list_tuple_mono fold_app_mono1
              in_F prod.collapse subset_code(1))  
      qed
    qed
  qed
qed


lemma OrderDAG_in_verts: 
  assumes "x \<in> set (snd (OrderDAG G k))"
  shows "x \<in> verts G"
  using assms
proof(induction G k arbitrary: x rule: OrderDAG.induct)
  case (1 G k x)
  consider (inval) "\<not> blockDAG G"| (one) "blockDAG G \<and>
  card (verts G) = 1" | (val) "blockDAG G \<and>
  card (verts G) \<noteq> 1" by auto
  then show ?case 
  proof(cases)
    case inval
    then show ?thesis using 1 by auto
  next
    case one
    then show ?thesis using OrderDAG.simps 1 genesis_nodeAlt_one_sound blockDAG.is_genesis_node.simps
      using empty_set list.simps(15) singleton_iff sndI by fastforce  
  next
    case val
    then show ?thesis
    proof 
      have bD: "blockDAG G" using val  by auto
      obtain M where M_in:"M = choose_max_blue_set (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G)))" by auto
      obtain pp where pp_in: "pp =  (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G)))" using blockDAG.tips_exist by auto
      have "set (snd (OrderDAG G k)) =
       set (snd (fold (app_if_blue_else_add_end G k) (top_sort G (sorted_list_of_set (anticone G (snd M))))
      (add_set_list_tuple M)))" unfolding M_in val using OrderDAG.simps val
        by (metis (mono_tags, lifting)) 
      then have "set (snd (OrderDAG G k)) 
    = set (top_sort G (sorted_list_of_set (anticone G (snd M)))) \<union> set (snd (add_set_list_tuple M))"
        using fold_app_mono_ex
        by (metis eq_snd_iff)
      then consider (ac) "x \<in> set (top_sort G (sorted_list_of_set (anticone G (snd M))))" 
        | (co) "x \<in> set (snd (add_set_list_tuple M))" 
        using 1 by auto
      then show "x \<in> verts G" proof(cases)
        case ac
        then show ?thesis using top_sort_con DAG.anticone_in_verts val 
            sorted_list_of_set(1) subs(1)
          by (metis DAG.anticon_finite subsetD) 
      next
        case co
        then consider (ma) "x = snd M" | (nma) "x \<in> set (snd( fst(M)))" 
          using add_set_list_tuple.simps
          by (metis (no_types, lifting) Un_insert_right append_Nil2 insertE
              list.simps(15) prod.collapse set_append sndI) 
        then show ?thesis proof(cases)
          case ma
          then show ?thesis unfolding M_in  using bD 
              chosen_map_simps(2) digraph.tips_in_verts subs
            by blast 
        next
          have mm: "choose_max_blue_set pp \<in> set pp" unfolding pp_in using bD chosen_map_simps(4)
            by (metis (mono_tags, lifting) Nil_is_map_conv choose_max_blue_avoid_empty)   
          case nma
          then have "x \<in> set (snd (OrderDAG (reduce_past G (snd M)) k))" 
            unfolding M_in choose_max_blue_avoid_empty blockDAG.tips_not_empty bD
            by (metis (no_types, lifting) ex_map_conv fst_conv mm pp_in snd_conv) 
          then have "x \<in> verts (reduce_past G (snd M))" using 1 val chosen_map_simps M_in pp_in 
              sorted_list_of_set(1) digraph.tips_finite subs bD
            by blast 
          then show "x \<in> verts G" using reduce_past.simps induce_subgraph_verts past_nodes.simps
            by auto
        qed
      qed 
    qed
  qed
qed


lemma OrderDAG_length:
  shows "blockDAG G \<Longrightarrow> length (snd (OrderDAG G k)) = card (verts G)"
proof(induct G k rule: OrderDAG.induct)
  case (1 G k)
  then show ?case proof (cases G rule: OrderDAG_casesAlt)
    case ntB
    then show ?thesis using 1 by auto
  next
    case one
    then show ?thesis using OrderDAG.simps by auto
  next
    case more
    show ?thesis using 1
    proof -
      have bD: "blockDAG G" using 1 by auto
      obtain ma where pp_in: "ma = (choose_max_blue_set (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G))))"
        by (metis)
      then have backw: "OrderDAG G k = fold (app_if_blue_else_add_end G k) 
              (top_sort G (sorted_list_of_set (anticone G (snd ma))))
              (add_set_list_tuple ma)" using OrderDAG.simps pp_in more
        by (metis (mono_tags, lifting) less_numeral_extra(4)) 
      have tt: "snd ma \<in> set (sorted_list_of_set (tips G))" using pp_in chosen_max_tip 
          more by auto
      have ttt: "snd ma \<in> tips G" using chosen_max_tip(2) pp_in
          more by auto
      then have bD2: "blockDAG (reduce_past G (snd ma))" using blockDAG.tips_unequal_gen bD more 
          blockDAG.reduce_past_dagbased bD tips_def 
        by fastforce
      then have "length (snd (OrderDAG (reduce_past G (snd ma)) k)) 
                  = card (verts (reduce_past G (snd ma)))"
        using 1 tt bD2 more by auto
      then have "length (snd (fst ma)) 
                  = card (verts (reduce_past G (snd ma)))"
        using bD chosen_map_simps(6) pp_in
        by fastforce  
      then have "length (snd (add_set_list_tuple ma)) = 1 + card (verts (reduce_past G (snd ma)))"
        by (metis add_set_list_tuple_length plus_1_eq_Suc prod.collapse)
      then show ?thesis unfolding backw
        using subs(1) DAG.verts_size_comp ttt
          add.assoc add.commute bD fold_app_length length_sorted_list_of_set top_sort_len
        by (metis (full_types))   
    qed
  qed
qed

lemma OrderDAG_total:
  assumes "blockDAG G" 
  shows "set (snd (OrderDAG G k)) = verts G"
  using Verts_in_OrderDAG OrderDAG_in_verts assms(1)
  by blast 

lemma  OrderDAG_distinct:
  assumes "blockDAG G"
  shows "distinct (snd (OrderDAG G k))"
  using OrderDAG_length OrderDAG_total
    card_distinct assms
  by metis 






end