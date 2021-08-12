
theory Ghostdag  
  imports blockDAG
begin

section \<open>GHOSTDAG\<close>
text \<open>Based on the GHOSTDAG blockDAG consensus algorithmus by Sompolinsky and Zohar 2018\<close>
subsection \<open>Utils\<close>

text \<open>The following functions transform a list L to a relation containing a  tuple (a,b)
  iff a = b or a precedes b in the list L \<close>
fun list_to_rel:: "'a list \<Rightarrow> ('a \<times> 'a) set"
  where "list_to_rel [] = {}"
  | "list_to_rel (x#xs) = {x} \<times> (set (x#xs)) \<union> list_to_rel xs"


lemma list_to_rel_in : " (a,b)  \<in> (list_to_rel L) \<longrightarrow> a \<in> set L \<and> b \<in> set L" 
proof(induct L, auto) qed

text \<open>Show soundness of list_to_rel\<close>
lemma list_to_rel_equal: 
"(a,b) \<in> list_to_rel L \<longleftrightarrow> (\<exists>k::nat. hd (drop k L) = a \<and> b \<in> set (drop k L))"
proof(safe)
  assume "(a, b) \<in> list_to_rel L"
  then show "\<exists>k. hd (drop k L) = a \<and> b \<in> set  (drop k L)"
  proof(induct L)
    case Nil
    then show ?case by auto
  next
    case (Cons a2 L)
    then consider "(a, b) \<in> {a2} \<times> set (a2 # L) " | "(a,b) \<in>  list_to_rel L" by auto
    then show ?case unfolding list_to_rel.simps(2)  
    proof(cases)
      case 1
      then have "a = hd (a2 # L)" by auto
      moreover have "b \<in> set (a2 # L)" using 1 by auto
      ultimately show ?thesis using drop0
        by metis 
    next
      case 2
      then obtain k where k_in : "hd (drop k (L)) = a \<and> b \<in> set (drop k (L))" 
        using Cons(1) by auto
      show ?thesis proof
        let ?k = "Suc k"
        show "hd (drop ?k (a2 # L)) = a \<and> b \<in> set (drop ?k (a2 # L))"
          unfolding drop_Suc using k_in by auto 
      qed
  qed
    qed
  next
  fix k 
  assume "b \<in> set (drop k L)"
  and "a = hd (drop k L)"
  then show "(hd (drop k L), b) \<in> list_to_rel L"
  proof(induct L arbitrary: k)
    case Nil
    then show ?case by auto
  next
    case (Cons a L)
    consider (zero) "k = 0" | (more) "k > 0" by auto    
    then show ?case 
    proof(cases)
      case zero
    then show ?thesis using Cons drop_0 by auto
  next
    case more
    then obtain k2 where k2_in:  "k = Suc k2"
      using gr0_implies_Suc by auto 
     show ?thesis using Cons unfolding k2_in drop_Suc list_to_rel.simps(2) by auto
    qed
  qed
qed

lemma list_to_rel_append:
  assumes "a \<in> set L"
  shows "(a,b) \<in> list_to_rel (L @ [b])" 
  using assms
proof(induct L, simp, auto) qed 

text \<open>For every distinct L, list_to_rel L return a linear order on set L\<close>
lemma list_order_linear:
  assumes "distinct L"
  shows "linear_order_on (set L)  (list_to_rel L)" 
  unfolding linear_order_on_def total_on_def partial_order_on_def preorder_on_def refl_on_def
  trans_def antisym_def 
proof(safe)
  fix a b
  assume "(a, b) \<in> list_to_rel L"
  then show "a \<in> set L" 
  proof(induct L, auto) qed
next 
  fix a b
  assume "(a, b) \<in> list_to_rel L"
  then show "b \<in> set L" 
  proof(induct L, auto) qed
next 
  fix x 
  assume "x \<in> set L"
  then show "(x, x) \<in> list_to_rel L"
  proof(induct L, auto) qed
next
  fix x y z 
  assume as1: "(x,y) \<in> list_to_rel L"
  and  as2: "(y, z) \<in> list_to_rel L"
  then show "(x, z) \<in> list_to_rel L"
    using assms
  proof(induct L)
    case Nil
    then show ?case by auto
  next
    case (Cons a L)
    then consider (nor) "(x, y) \<in> {a} \<times> set (a # L) \<and> (y, z) \<in> {a} \<times> set (a # L)" 
      | (xy) "(x,y) \<in> list_to_rel L \<and> (y, z) \<in> {a} \<times> set (a # L)" 
      | (yz) "(y,z) \<in> list_to_rel L \<and> (x, y) \<in> {a} \<times> set (a # L)"
      | (both) "(y,z) \<in> list_to_rel L \<and> (x,y) \<in> list_to_rel L" by auto
    then show ?case proof(cases)
    case nor
      then show ?thesis by auto
    next
      case xy 
      then have "y \<in> set L" using list_to_rel_in by metis
      also have "y = a" using xy by auto
      ultimately have "\<not> distinct (a # L)"
        by simp 
    then show ?thesis using Cons by auto
    next
    case yz
    then show ?thesis using list_to_rel.simps(2)
      by (metis Cons.prems(2) SigmaD1 SigmaI UnI1 list_to_rel_in)  
    next
      case both
      then show ?thesis unfolding list_to_rel.simps(2) using Cons by auto
    qed
  qed 
next
  fix x y 
  assume "(x, y) \<in> list_to_rel L"
  and "(y, x) \<in> list_to_rel L"
  then show "x = y"
    using assms
  proof(induct L, simp)
    case (Cons a L)
      then consider (nor) "(x, y) \<in> {a} \<times> set (a # L) \<and> (y, x) \<in> {a} \<times> set (a # L)" 
      | (xy) "(x,y) \<in> list_to_rel L \<and> (y, x) \<in> {a} \<times> set (a # L)" 
      | (yz) "(y,x) \<in> list_to_rel L \<and> (x, y) \<in> {a} \<times> set (a # L)"
      | (both) "(y,x) \<in> list_to_rel L \<and> (x,y) \<in> list_to_rel L" by auto
      then show ?case unfolding list_to_rel.simps 
      proof(cases)
      case nor
      then show ?thesis by auto
      next
      case xy
      then show ?thesis
        by (metis Cons.prems(3) SigmaD1 distinct.simps(2) list_to_rel_in singletonD) 
      next
        case yz
        then show ?thesis  
          by (metis Cons.prems(3) SigmaD1 distinct.simps(2) list_to_rel_in singletonD) 
      next
        case both
      then show ?thesis using Cons by auto 
      qed
    qed
  next
    fix x y 
    assume "x \<in> set L"
    and "y \<in> set L"
    and "x \<noteq> y"
    and "(y, x) \<notin> list_to_rel L"
    then show "(x, y) \<in> list_to_rel L"
    proof(induct L, auto) qed    
  qed

subsection \<open>Funcitions and Definitions\<close>    

text \<open>Function to sort a list $L$ under a graph G such if $a$ references $b$,
$b$ precedes $a$ in the list\<close>

fun top_insert:: "('a::linorder,'b) pre_digraph \<Rightarrow>'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "top_insert G [] a = [a]"
  | "top_insert G (b # L) a = (if (a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) then (b # top_insert G L a) else (a # ( b # L)))"

fun top_sort:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "top_sort G []= [] "
  | "top_sort G (a # L) = top_insert G (top_sort G L) a"

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

text \<open>Function that adds a node $a$ to a kCluster $S$, if $S \<union> {a}$ remains a kCluster.
    Also adds $a$ to the end of list $L$\<close>
fun app_if_blue_else_add_end :: 
"('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a::linorder set \<times> 'a list)
 \<Rightarrow> ('a::linorder set \<times> 'a list)"  
where "app_if_blue_else_add_end G k a (S,L) = (if (kCluster G k (S \<union> {a})) 
then add_set_list_tuple ((S,L),a) else (S,L @ [a]))"

text \<open>Function to select the largest $((S,L),a)$ according to $larger_blue_tuple$\<close>
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
fun GhostDAG_Relation :: "('a::linorder,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a) set"
  where "GhostDAG_Relation G k = list_to_rel (snd (OrderDAG G k))"

subsection\<open>Soundness\<close>

lemma OrderDAG_casesAlt:
  obtains (ntB) "\<not> blockDAG G" 
  | (one) "blockDAG G \<and> card (verts G) = 1"
  | (more) "blockDAG G \<and> card (verts G) > 1"
  using  blockDAG.blockDAG_size_cases by auto
   

subsubsection \<open>Soundness of the topological sort algorithm\<close>
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


lemma top_insert_len: "length (top_insert G L a) = Suc (length L)"
proof(induct L)
case Nil
then show ?case by auto
next
  case (Cons a L)
  then show ?case using top_insert.simps(2) by auto
qed


lemma top_sort_len: "length (top_sort G L) = length L"
proof(induct L)
case Nil
then show ?case by auto
next
  case (Cons a L)
  then have "length (a#L) = Suc (length L)" by auto
  then show ?case using
      top_insert_len top_sort.simps(2) Cons
    by (simp add: top_insert_len)   
qed


subsubsection \<open>Soundness of the $add_set_list$ function\<close>

lemma add_set_list_tuple_mono:
  shows "set L \<subseteq> set (snd (add_set_list_tuple ((S,L),a)))"
  using add_set_list_tuple.simps by auto

lemma add_set_list_tuple_mono2:
  shows "set (snd (add_set_list_tuple ((S,L),a))) \<subseteq> set L \<union> {a} "
  using add_set_list_tuple.simps by auto

lemma add_set_list_tuple_length:
  shows "length (snd (add_set_list_tuple ((S,L),a))) = Suc (length L)"
proof(induct L, auto) qed


subsubsection \<open>Soundness of the $add_if_blue$ function\<close>

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
  

  
  
subsubsection \<open>Soundness of the $larger_blue_tuple$ comparison\<close>

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
  assumes "x \<in> set (snd (S,L1))"
  shows " x \<in> set (snd (fold (app_if_blue_else_add_end G k) L2 (S2,L1)))"
proof(rule fold_invariant)
  show "\<And>x. x \<in> set L2 \<Longrightarrow>  x \<in> set L2" by simp
  show "x \<in> set (snd (S2, L1))" using assms(1) by simp
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

lemma fold_app_mono_ex: 
 shows "(set L2 \<union> set L1) = set (snd (fold (app_if_blue_else_add_end G k) L2 (S,L1)))" 
proof
  show "set L2 \<union> set L1 \<subseteq> set (snd (fold (app_if_blue_else_add_end G k) L2 (S, L1)))"
    using fold_app_mono fold_app_mono2 by auto
next
  show "set (snd (fold (app_if_blue_else_add_end G k) L2 (S, L1))) \<subseteq> set L2 \<union> set L1" 
  proof(rule fold_invariant)
      show "\<And>x. x \<in> set L2 \<Longrightarrow>  x \<in> set L2" by auto
    next 
      show "set (snd (S, L1)) \<subseteq> set L2 \<union> set L1" by auto
    next 
      fix x 
      fix s::"'a set \<times> 'a list" 
      assume x_in: "x \<in> set L2"
      and s_sub: "set (snd s) \<subseteq> set L2 \<union> set L1"
      then have "set (snd (app_if_blue_else_add_end G k x s)) \<subseteq> 
      set (snd (app_if_blue_else_add_end G k x (fst s, L2 @ L1)))"
        using app_if_blue_mono4
        by (metis prod.collapse set_append)
      then show "set (snd (app_if_blue_else_add_end G k x s)) \<subseteq> set L2 \<union> set L1" 
        using x_in app_if_blue_mono3
        by fastforce
    qed
  qed



lemma map_snd_map: "\<And>L. (map snd (map (\<lambda>i. (P i , i)) L)) =  L" 
      proof -
        fix L
        show "map snd (map (\<lambda>i. (P i, i)) L) = L"
        proof(induct L)
          case Nil
          then show ?case by auto
        next
          case (Cons a L)
          then show ?case by auto
        qed
      qed

lemma chosen_max_tip:
  assumes "blockDAG G"
  assumes "x = snd ( choose_max_blue_set (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G))))" 
  shows  "x \<in> set (sorted_list_of_set (tips G))" and " x \<in> tips G"
proof - 
  obtain pp where pp_in: "pp =  (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
   (sorted_list_of_set (tips G)))" using blockDAG.tips_exist by auto
    have mm: "choose_max_blue_set pp \<in> set pp" using pp_in choose_max_blue_avoid_empty
        digraph.tips_finite subs assms(1)
       list.map_disc_iff sorted_list_of_set_eq_Nil_iff blockDAG.tips_not_empty 
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
      using digraph.tips_finite sorted_list_of_set(1) kk subs assms pp_in by auto
qed

lemma chosen_map_simps:
  assumes "blockDAG G"
  assumes "x = map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G))" 
  shows  "snd  (choose_max_blue_set x) \<in> set (sorted_list_of_set (tips G))" 
    and  "snd (choose_max_blue_set x) \<in> tips G"
    and "set (map snd x) = set (sorted_list_of_set (tips G))"
    and "choose_max_blue_set x \<in> set x"
proof - 
  obtain pp where pp_in: "pp =  (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
   (sorted_list_of_set (tips G)))" using blockDAG.tips_exist by auto
    have mm: "choose_max_blue_set pp \<in> set pp" using pp_in choose_max_blue_avoid_empty
        digraph.tips_finite subs assms(1)
       list.map_disc_iff sorted_list_of_set_eq_Nil_iff blockDAG.tips_not_empty 
      by (metis (mono_tags, lifting))  
    then have kk: "snd (choose_max_blue_set pp) \<in> set (map  snd pp)"
      by auto 
    have seteq: "set (map snd pp) = set (sorted_list_of_set (tips G))" 
      using map_snd_map pp_in  by auto
    then show "snd (choose_max_blue_set x) \<in> set (sorted_list_of_set (tips G))" 
      using pp_in assms(2) kk by blast 
    then show "snd (choose_max_blue_set x) \<in> tips G"
      using digraph.tips_finite sorted_list_of_set(1) kk subs assms pp_in by auto
    show "set (map snd x) = set (sorted_list_of_set (tips G))"
      using map_snd_map assms(2) 
      by simp
    then show "choose_max_blue_set x \<in> set x" using seteq pp_in assms(2)
      mm by blast 
qed






subsubsection \<open>OrderDAG soundness\<close>

lemma Verts_in_OrderDAG: 
  assumes "blockDAG G"
  shows "x \<in> verts G \<longrightarrow> x \<in> set (snd (OrderDAG G k))"
  using assms(1)
proof(safe, induct G k  arbitrary: x rule: OrderDAG.induct)
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
          using  fold_app_mono surj_pair
        by (metis)
      then show ?thesis unfolding pp_in fcur_in using 1 OrderDAG.simps cDm
        by (metis (mono_tags, lifting)) 
      next
        assume anti: "x \<in> anticone G (snd (choose_max_blue_set pp))" 
        obtain ttt where ttt_in: "ttt = add_set_list_tuple (choose_max_blue_set pp)" by auto
        have "x \<in> set (snd (fold (app_if_blue_else_add_end G k)
                 (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp)))))
                   ttt))" 
          using pp_in sorted_list_of_set(1) anti bD subs
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
        digraph.tips_finite bD subs sorted_list_of_set(1) by auto
        moreover 
        have "blockDAG (reduce_past G (snd (choose_max_blue_set pp)))" using 
        blockDAG.reduce_past_dagbased bD tt2  blockDAG.tips_unequal_gen 
        cd1 tips_def CollectD by metis
        ultimately have bass: 
          "x \<in> set ((snd (OrderDAG (reduce_past G (snd (choose_max_blue_set pp))) k)))" 
          using  pp_in 1 cDm tt2 pas by metis
        then have in_F: "x \<in> set (snd ( fst ((choose_max_blue_set pp))))" unfolding pp_in
          using surj_pair
          imageE list.set_map chosen_map_simps old.prod.inject pp_in prod.collapse
          bD map_eq_conv 
          by (smt (verit, best) map_eq_conv) 
        then have "x \<in> set (snd (fold (app_if_blue_else_add_end G k)
         (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp)))))
         (fst((choose_max_blue_set pp)))))"
          by (metis fold_app_mono in_F prod.collapse) 
        moreover have "OrderDAG G k = (fold (app_if_blue_else_add_end G k)
         (top_sort G (sorted_list_of_set (anticone G (snd (choose_max_blue_set pp)))))
         (add_set_list_tuple (choose_max_blue_set pp)))" using cDm 1(4) OrderDAG.simps pp_in
          by (metis (no_types, lifting) map_eq_conv) 
        then show "x \<in> set (snd (OrderDAG G k))"
          by (metis (no_types, lifting) add_set_list_tuple_mono fold_app_mono
               in_F prod.collapse subset_code(1))  
      qed
    qed
  qed
qed


lemma OrderDAG_in_verts: "x \<in> set (snd (OrderDAG G k)) \<longrightarrow> x \<in> verts G"
proof(induction G k arbitrary: x rule: OrderDAG.induct)
  case (1 G k x)
  consider (inval) "\<not> blockDAG G"| (one) "blockDAG G \<and>
  card (verts G) = 1" | (val) "blockDAG G \<and>
  card (verts G) \<noteq> 1" by auto
  then show ?case 
  proof(cases)
    case inval
    then show ?thesis using OrderDAG.simps by auto
  next
    case one
    then show ?thesis using OrderDAG.simps genesis_nodeAlt_one_sound blockDAG.is_genesis_node.simps
      using empty_set list.simps(15) singleton_iff sndI by fastforce  
  next
    case val
    then show ?thesis
    proof safe
    have bD: "blockDAG G" using val  by auto
    assume pre: "x \<in> set (snd (OrderDAG G k))"
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
      using pre by auto
    then show "x \<in> verts G" proof(cases)
        case ac
        then show ?thesis using top_sort_con DAG.anticone_in_verts val 
        sorted_list_of_set(1) subs
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
    then show ?thesis using  1 by auto
    next
      case one
      then show ?thesis using OrderDAG.simps by auto
    next
    case more
    show ?thesis using 1
    proof -
      have bD: "blockDAG G" using 1 by auto
      assume ind: "(\<And>x. \<not> \<not> blockDAG G \<Longrightarrow>
          card (verts G) \<noteq> 1 \<Longrightarrow>
          x \<in> set (sorted_list_of_set (tips G)) \<Longrightarrow> blockDAG (reduce_past G x)
           \<Longrightarrow> length (snd (OrderDAG (reduce_past G x) k)) = card (verts (reduce_past G x)))"
      obtain x where x_in: "x = (choose_max_blue_set (map (\<lambda>i. (OrderDAG (reduce_past G i) k, i))
       (sorted_list_of_set (tips G))))"
        by (metis)
      then have tt: "snd x \<in> set (sorted_list_of_set (tips G))" using chosen_max_tip 
      more by auto
      have ttt: "snd x \<in> tips G" using chosen_max_tip(2) x_in
      more by auto
      then have bD2: "blockDAG (reduce_past G (snd x))" using blockDAG.tips_unequal_gen bD more 
      blockDAG.reduce_past_dagbased bD tips_def 
        by fastforce
      then have "length (snd (OrderDAG (reduce_past G (snd x)) k)) 
                  = card (verts (reduce_past G (snd x)))"
        using ind tt bD2 more by auto
      moreover have "(OrderDAG (reduce_past G (snd x)) k) = fst x" unfolding x_in using 
          choose_max_blue_avoid_empty prod.collapse 
          Pair_inject ex_map_conv list.map_disc_iff map_eq_conv tt 
        by (smt (verit, del_insts)) 
      ultimately show ?thesis using x_in OrderDAG.simps more fold_app_length 
          add_set_list_tuple_length  DAG.verts_size_comp subs bD
           add_Suc_shift length_sorted_list_of_set less_irrefl_nat map_eq_conv
           plus_1_eq_Suc prod.collapse top_sort_len ttt
        by (smt (z3)) 
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


lemma GhostDAG_linear: 
  assumes "blockDAG G" 
  shows "linear_order_on (verts G) (GhostDAG_Relation G k)"
  unfolding GhostDAG_Relation.simps 
  using list_order_linear OrderDAG_distinct OrderDAG_total assms by metis

lemma GhostDAG_preserving:
  assumes "blockDAG G"
  and "x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y"
shows "(y,x) \<in> GhostDAG_Relation G k"
  unfolding GhostDAG_Relation.simps using assms 
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
       oops
      

end