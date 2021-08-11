(* 
    Title: DAGbasedConsensus\Spectre.thy
    Author:     Joern Kussmaul
*)

theory Spectre
  imports Main Graph_Theory.Graph_Theory blockDAG 
begin

text \<open>Based on the SPECTRE paper by Sompolinsky, Lewenberg and Zohar 2016\<close>
section  \<open>Spectre\<close>

subsection  \<open>Definitions\<close>


text \<open>Function to check and break occuring ties\<close>
fun tie_break_int:: "'a::linorder \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int"
  where "tie_break_int a b i =
 (if i=0 then (if (b < a) then -1 else 1) else 
              (if i > 0 then 1 else -1))"

text \<open>Function given a list of votes, sums them up if non empty, otherwise "no_vote"\<close>
fun sumlist_break :: "'a::linorder \<Rightarrow>'a \<Rightarrow> int list \<Rightarrow> int"
  where "sumlist_break a b [] = 0" (* votes like virtual block, occurs if node a neither sees b nor c*)
  | "sumlist_break a b (x # xs) = tie_break_int a b (sum_list (x # xs))"

text \<open>Spectre core algorithm, vote_Spectre V a b c returns 
      1 if a votes in favour of b (or b = c),
     -1 if a votes in favour of c, 0 otherwise\<close>
function vote_Spectre :: "('a::linorder,'b) pre_digraph \<Rightarrow>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> int" 
  where
  "vote_Spectre V a b c = (
  if (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V) then 0 else 
  if (b=c)  then 1 else 
  if (((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<or> a = b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 1  else
  if (((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c) \<or> a = c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b)) then -1 else
  if ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 
   (sumlist_break b c (map (\<lambda>i.
 (vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set (past_nodes V a))))
 else 
   sumlist_break b c (map (\<lambda>i.
   (vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a))))"
  by auto
termination
proof
let ?R = " measures [( \<lambda>(V, a, b, c). (card (verts V))),  ( \<lambda>(V, a, b, c). card {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a})] "  
  show "wf ?R"
    by simp 
next 
  fix V::"('a::linorder, 'b) pre_digraph" 
  fix x a b c
  assume bD: " \<not> (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V)"
  then have "a \<in> verts V"  by simp
  then have "card (verts (reduce_past V a)) < card (verts V)"   
    using bD blockDAG.reduce_less
    by metis
  then show "((reduce_past V a, x, b, c), V, a, b, c)
       \<in> measures
           [\<lambda>(V, a, b, c). card (verts V),  
            \<lambda>(V, a, b, c). card {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a}]" (* In the recursive step, either the number of
             nodes decreases or the number of nodes that reach the voter a*)
    by simp
next 
  fix V::"('a::linorder, 'b) pre_digraph" 
  fix x a b c
  assume bD: " \<not> (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V)"
  then have a_in: "a \<in> verts V" using bD by simp
  assume "x \<in> set (sorted_list_of_set (future_nodes V a))"
  then have "x \<in> future_nodes V a" using DAG.finite_future
    set_sorted_list_of_set bD subs
    by metis
  then have rr: "x \<rightarrow>\<^sup>+\<^bsub>V\<^esub> a" using future_nodes.simps bD mem_Collect_eq
    by simp  
  then have a_not: "\<not> a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> x" using bD DAG.unidirectional subs by metis
  have bD2: "blockDAG V" using bD by simp
  have "\<forall>x. {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> x} \<subseteq> verts V" using subs bD2  subsetI
      wf_digraph.reachable_in_verts(1) mem_Collect_eq
    by metis 
  then have fin: "\<forall>x. finite {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> x}" using subs bD2 fin_digraph.finite_verts 
      finite_subset
    by metis
  have "x \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a" using rr wf_digraph.reachable1_reachable subs bD2 by metis
  then have "{e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> x} \<subseteq> {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a}" using rr
      wf_digraph.reachable_trans Collect_mono subs bD2 by metis
  then have "{e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> x} \<subset> {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a}" using a_not
  subs bD2 a_in mem_Collect_eq psubsetI wf_digraph.reachable_refl
    by metis 
  then have "card {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> x} < card {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a}" using fin
    by (simp add: psubset_card_mono)
  then show "((V, x, b, c), V, a, b, c)
       \<in> measures
           [\<lambda>(V, a, b, c). card (verts V), \<lambda>(V, a, b, c). card {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a}]"
    by simp
qed

text \<open>Given vote_Spectre calculate if a < b for arbitrary nodes\<close>
fun Spectre_Order :: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "Spectre_Order G a b = ( sumlist_break a b (map (\<lambda>i.
   (vote_Spectre G i a b)) (sorted_list_of_set (verts G))) = 1)" 

text \<open>Given  Spectre_Order calculate the corresponding Relation over the nodes of G\<close>
definition Spectre_Order_Relation :: "('a::linorder,'b) pre_digraph \<Rightarrow> ('a \<times> 'a) set"
  where "Spectre_Order_Relation G \<equiv> {(a,b) \<in> (verts G \<times> verts G). Spectre_Order G a b}"

subsection \<open>Lemmas\<close>

lemma domain_tie_break:
  shows "tie_break_int a b c \<in> {-1 ,1}"
  using  tie_break_int.simps by simp

lemma domain_sumlist:
  shows "sumlist_break a b c  \<in> {-1 ,0 ,1}"
  using sumlist_break.simps(1) insertCI sumlist_break.elims domain_tie_break
  by (metis insert_commute)
  

lemma domain_sumlist_not_empty:
  assumes "l \<noteq> []"
  shows "sumlist_break a b l  \<in> {-1, 1}"
  using  sumlist_break.elims domain_tie_break assms
  by metis 
  
  

lemma Spectre_casesAlt:
  fixes V:: "('a::linorder,'b) pre_digraph"
  and a :: "'a::linorder" and  b :: "'a::linorder" and c :: "'a::linorder"
  obtains (no_bD) "(\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V)"
  | (equal) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and> b = c" 
  | (one) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and>
         b \<noteq> c  \<and> (((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<or> a = b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))" 
  | (two) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and> b \<noteq> c 
  \<and> \<not>(((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<or> a = b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) \<and> 
  ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c) \<or> a = c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b)"
  | (three) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and> b \<noteq> c 
   \<and> \<not>(((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<or> a = b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) \<and>  
   \<not>(((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c) \<or> a = c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b))\<and> 
  ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))"
  | (four) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and> b \<noteq> c  \<and>
  \<not>(((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<or> a = b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) \<and>  
   \<not>(((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c) \<or> a = c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b))\<and>  
  \<not>((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))"
  by auto
  

lemma Spectre_theo:
  assumes "P 0"
  and "P 1"
  and "P (-1)" 
  and "P (sumlist_break b c (map (\<lambda>i.
 (vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set ((past_nodes V a)))))"
  and "P (sumlist_break b c (map (\<lambda>i.
   (vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a))))"
shows "P (vote_Spectre V a b c)"
  using assms vote_Spectre.simps
  by (metis (mono_tags, lifting)) 
  

lemma domain_Spectre:
  shows "vote_Spectre V a b c \<in> {-1, 0, 1}"
proof(rule Spectre_theo, simp, simp, simp, metis domain_sumlist, metis domain_sumlist) qed
 

lemma antisymmetric_tie_break:
  shows "b\<noteq>c  \<Longrightarrow> tie_break_int b c i = - tie_break_int c b (-i)"
  unfolding  tie_break_int.simps using less_not_sym by auto

   
lemma antisymmetric_sumlist:
  shows "b \<noteq> c \<Longrightarrow> sumlist_break b c l = - sumlist_break c b (map (\<lambda>x. -x) l) "
proof(induct l, simp)
  case (Cons a l)
  have "sum_list (map uminus (a # l)) = - sum_list  (a # l)"
    by (metis map_ident map_map uminus_sum_list_map) 
  then show ?case using sumlist_break.simps(2) antisymmetric_tie_break Cons by auto
qed
  


lemma vote_Spectre_antisymmetric: 
  shows "b \<noteq> c \<Longrightarrow> vote_Spectre V a b c = - (vote_Spectre V a c b)"
proof(induction V a b c rule: vote_Spectre.induct)
  fix V ::"('a::linorder, 'b) pre_digraph"
  and a:: "'a::linorder" and  b:: "'a::linorder" and  c :: "'a::linorder"
  assume past: "(\<And>x. \<not> (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V) \<Longrightarrow>
             b \<noteq> c \<Longrightarrow>
             \<not> ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b \<or> a = b) \<and> (a, c) \<notin> (arcs_ends V)\<^sup>+) \<Longrightarrow>
             \<not> ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c \<or> a = c) \<and> (a, b) \<notin> (arcs_ends V)\<^sup>+) \<Longrightarrow>
             a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b \<and> a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c \<Longrightarrow>
             x \<in> set (sorted_list_of_set (past_nodes V a)) \<Longrightarrow>
              b \<noteq> c \<Longrightarrow> vote_Spectre (reduce_past V a) x b c
               = - vote_Spectre (reduce_past V a) x c b)"
  and fut: "(\<And>x. \<not> (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V) \<Longrightarrow>
             b \<noteq> c \<Longrightarrow>
             \<not> ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b \<or> a = b) \<and> (a, c) \<notin> (arcs_ends V)\<^sup>+) \<Longrightarrow>
             \<not> ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c \<or> a = c) \<and> (a, b) \<notin> (arcs_ends V)\<^sup>+) \<Longrightarrow>
             \<not> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b \<and> a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c) \<Longrightarrow>
             x \<in> set (sorted_list_of_set (future_nodes V a)) \<Longrightarrow>
             b \<noteq> c \<Longrightarrow> vote_Spectre V x b c = - vote_Spectre V x c b)"
  and not_eq: "b \<noteq> c"
  show "vote_Spectre V a b c = - vote_Spectre V a c b"
  proof(cases a b c V rule:Spectre_casesAlt)
  case no_bD
    then show ?thesis by auto
  next
  case equal
  then show ?thesis using not_eq  by simp
  next
    case one
    then show ?thesis by auto   
  next
    case two
    then show ?thesis by auto
  next
    case three
    then have ff: "vote_Spectre V a b c = (sumlist_break b c (map (\<lambda>i.
 (vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set (past_nodes V a))))" by auto
    have ff2: "vote_Spectre V a c b = (sumlist_break c b (map (\<lambda>i.
    (- vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set (past_nodes V a))))" 
       using three past vote_Spectre.simps map_eq_conv
       by (smt (verit))
     have "(map (\<lambda>i. - vote_Spectre (reduce_past V a) i b c) (sorted_list_of_set (past_nodes V a)))
     = (map uminus (map (\<lambda>i. vote_Spectre (reduce_past V a) i b c)
       (sorted_list_of_set (past_nodes V a))))" 
       using map_map by auto       
     then have "vote_Spectre V a c b = - (sumlist_break b c (map (\<lambda>i.
    (vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set (past_nodes V a))))" 
    using  antisymmetric_sumlist not_eq ff2
    by (metis verit_minus_simplify(4)) 
    then show ?thesis using  ff by auto
  next
    case four
    then have ff: "vote_Spectre V a b c = sumlist_break b c (map (\<lambda>i.
   (vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a)))" by auto 
    have ff2: "vote_Spectre V a c b = (sumlist_break c b (map (\<lambda>i.
    (- vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a))))" 
       using four fut vote_Spectre.simps map_eq_conv
       by (smt (z3))
     have "(map (\<lambda>i. - vote_Spectre V i b c) (sorted_list_of_set (future_nodes V a)))
     = (map uminus (map (\<lambda>i. vote_Spectre V i b c) (sorted_list_of_set (future_nodes V a))))" 
       using map_map by auto       
     then have "vote_Spectre V a c b = - (sumlist_break b c (map (\<lambda>i.
    (vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a))))" 
    using  antisymmetric_sumlist not_eq ff2
    by (metis verit_minus_simplify(4)) 
    then show ?thesis using ff by auto
  qed  
qed


lemma vote_Spectre_reflexive:
assumes "blockDAG V"
  and "a \<in> verts V"
shows "\<forall>b \<in> verts V. vote_Spectre V b a a = 1 " using vote_Spectre.simps assms by auto 

lemma Spectre_Order_reflexive:
assumes "blockDAG V"
  and "a \<in> verts V" 
shows "Spectre_Order V a a" 
  unfolding Spectre_Order.simps 
proof -   
  obtain l where l_def: "l = (map (\<lambda>i. vote_Spectre V i a a) (sorted_list_of_set (verts V)))"
    by auto
  have only_one: "l = (map (\<lambda>i.1) (sorted_list_of_set (verts V)))"
    using l_def vote_Spectre_reflexive assms sorted_list_of_set(1)
    by (simp add: fin_digraph.finite_verts subs)
  have ne: "l \<noteq> []"
    using  blockDAG.no_empty_blockDAG length_map
    by (metis assms(1) length_sorted_list_of_set less_numeral_extra(3) list.size(3) l_def)
  have "sum_list l = card (verts V)" using ne only_one sum_list_map_eq_sum_count
    by (simp add: sum_list_triv)
  then have "sum_list l > 0" using blockDAG.no_empty_blockDAG assms(1) by simp
  then show "sumlist_break a a (map (\<lambda>i. vote_Spectre V i a a) (sorted_list_of_set (verts V))) = 1"
    using l_def ne sumlist_break.simps(2) tie_break_int.simps
    by (metis list.exhaust verit_comp_simplify1(1)) 
qed

lemma Spectre_Order_antisym: 
  assumes "blockDAG V"
  and "a \<in> verts V \<and> b \<in> verts V" 
  and "a \<noteq> b"
  shows "Spectre_Order V a b = (\<not> (Spectre_Order V b a))"
proof -
  obtain l where l_def: "l = (map (\<lambda>i. vote_Spectre V i a b) (sorted_list_of_set (verts V)))"
    by auto
  then have ne: "l \<noteq> []"
    using  blockDAG.no_empty_blockDAG length_map assms(1)
      length_sorted_list_of_set less_numeral_extra(3) list.size(3) l_def
    by metis
  then have dm: "sumlist_break a b l \<in> {-1,1}" using domain_sumlist_not_empty by auto  
  obtain l2 where l2_def: "l2 = (map (\<lambda>i. vote_Spectre V i b a) (sorted_list_of_set (verts V)))"
      by auto
    have minus: "l2 = map uminus l"
      unfolding l_def l2_def map_map
      using  vote_Spectre_antisymmetric assms(3)
      by (metis comp_apply) 
    have anti: "sumlist_break a b l = - sumlist_break b a l2" unfolding minus 
      using antisymmetric_sumlist assms(3) by auto
    have ne2: "l2 \<noteq> []"
      using ne minus by auto
    then have dm2: "sumlist_break b a l2 \<in> {-1,1}" using domain_sumlist_not_empty by auto
    then show "?thesis" unfolding Spectre_Order.simps using anti l_def dm l2_def 
    add.inverse_inverse empty_iff equal_neg_zero insert_iff zero_neq_one
    by (metis)
qed  
  
lemma Spectre_Order_total:
  assumes "blockDAG V"
  and "a \<in> verts V \<and> b \<in> verts V" 
shows "Spectre_Order V a b \<or> Spectre_Order V b a"
proof safe
  assume notB: " \<not> Spectre_Order V b a"
  consider (eq) "a = b"| (neq) "a \<noteq> b" by auto
  then show "Spectre_Order V a b"
  proof (cases)
  case eq
  then show ?thesis using Spectre_Order_reflexive assms by metis
  next
    case neq
     then show "?thesis" using Spectre_Order_antisym notB assms
       by blast 
   qed
 qed




lemma Spectre_Order_Relation_total:
  assumes "blockDAG G"
  shows "total_on (verts G) (Spectre_Order_Relation G)"
  unfolding total_on_def Spectre_Order_Relation_def 
  using Spectre_Order_total assms
  by fastforce 

lemma Spectre_Order_Relation_reflexive:
  assumes "blockDAG G"
  shows "refl_on (verts G) (Spectre_Order_Relation G)" 
  unfolding refl_on_def Spectre_Order_Relation_def 
  using Spectre_Order_reflexive assms by fastforce

lemma Spectre_Order_Relation_antisym:
  assumes "blockDAG G"
  shows "antisym (Spectre_Order_Relation G)" 
  unfolding antisym_def Spectre_Order_Relation_def 
  using Spectre_Order_antisym assms by fastforce
     
  
end
