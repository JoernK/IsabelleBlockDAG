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
 (if i=0 then (if (b < a) then -1 else 1) else i)"

text \<open>Sign function with 0\<close>
fun signum :: "int \<Rightarrow> int"
  where "signum a =  (if a > 0 then 1 else if a < 0 then -1 else 0)"

text \<open>Spectre core algorithm, $vote-Spectre V a b c$ returns 
     $1$ if a votes in favour of $b$ (or $b = c$),
     $-1$ if a votes in favour of $c$, $0$ otherwise\<close>
function vote_Spectre :: "('a::linorder,'b) pre_digraph \<Rightarrow>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> int" 
  where
    "vote_Spectre V a b c = (
  if (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V) then 0 else 
  if (b=c)  then 1 else 
  if (((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<or> a = b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 1  else
  if (((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c) \<or> a = c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b)) then -1 else
  if ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 
   (tie_break_int b c (signum (sum_list (map (\<lambda>i.
 (vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set (past_nodes V a))))))
 else 
   signum (sum_list (map (\<lambda>i.
   (vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a)))))"
  by auto
termination
proof
  let ?R = " measures [( \<lambda>(V, a, b, c). (card (verts V))),  ( \<lambda>(V, a, b, c). card {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a})]"  
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

text \<open>Given vote-Spectre calculate if $a < b$ for arbitrary nodes\<close>
definition Spectre_Order :: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "Spectre_Order G a b = ( tie_break_int a b (signum ( sum_list (map (\<lambda>i.
   (vote_Spectre G i a b)) (sorted_list_of_set (verts G))))) = 1)" 

text \<open>Given Spectre-Order calculate the corresponding relation over the nodes of G\<close>
definition Spectre_Order_Relation :: "('a::linorder,'b) pre_digraph \<Rightarrow> ('a \<times> 'a) set"
  where "Spectre_Order_Relation G \<equiv> {(a,b) \<in> (verts G \<times> verts G). Spectre_Order G a b}"

subsection \<open>Lemmas\<close>

lemma sumlist_one_mono:
  assumes "\<forall> x \<in> set L. x \<ge> 0 "
    and "\<exists> x \<in> set L. x > 0"
  shows "signum (sum_list L) = 1"
  using assms 
proof(induct L, simp)
  case (Cons a2 L)
  consider (bg) "a2 > 0" | "a2 = 0" using Cons
    by (metis le_less list.set_intros(1))
  then show ?case 
  proof(cases)
    case bg
    then have "sum_list L \<ge> 0 " using Cons 
      by (simp add: sum_list_nonneg)
    then have "sum_list (a2 # L) > 0" using bg sum_list_def
      by auto 
    then show ?thesis using tie_break_int.simps
      by auto 
  next
    case 2
    then have  be: "\<exists>a\<in>set L. 0 < a" using Cons
      by (metis less_int_code(1) set_ConsD) 
    then have "L \<noteq> []" by auto
    then show ?thesis using sum_list_def 2
      using Cons.hyps Cons.prems(1) be by auto
  qed
qed

lemma domain_signum: "signum i \<in> {-1,0,1}" by simp

lemma domain_tie_break:
  shows "tie_break_int a b (signum i) \<in> {-1 ,1}"
  using  tie_break_int.simps
  by auto 



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
    and "P (tie_break_int b c (signum (sum_list (map (\<lambda>i.
 (vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set ((past_nodes V a)))))))"
    and "P  (signum (sum_list (map (\<lambda>i.
   (vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a)))))"
  shows "P (vote_Spectre V a b c)"
  using assms vote_Spectre.simps
  by (metis (mono_tags, lifting)) 


lemma domain_Spectre:
  shows "vote_Spectre V a b c \<in> {-1, 0, 1}"
proof(rule Spectre_theo, auto) qed



lemma antisymmetric_tie_break:
  shows "b\<noteq>c  \<Longrightarrow> tie_break_int b c i = - tie_break_int c b (-i)"
  unfolding  tie_break_int.simps using less_not_sym by auto


lemma antisymmetric_sumlist:
  shows "sum_list (l::int list) = - sum_list (map (\<lambda>x. -x) l) "
proof(induct l, auto) qed


lemma antisymmetric_signum:
  shows "signum i = - (signum (-i))"
  by auto

lemma vote_Spectre_antisymmetric: 
  shows "b \<noteq> c \<Longrightarrow> vote_Spectre V a b c = - (vote_Spectre V a c b)"
proof(induction V a b c rule: vote_Spectre.induct)
  case (1 V a b c)
  show "vote_Spectre V a b c = - vote_Spectre V a c b"
  proof(cases a b c V rule:Spectre_casesAlt)
    case no_bD
    then show ?thesis by fastforce
  next
    case equal
    then show ?thesis using 1  by simp
  next
    case one
    then show ?thesis by auto   
  next
    case two
    then show ?thesis by fastforce
  next
    case three
    then have ff: "vote_Spectre V a b c = tie_break_int b c (signum (sum_list (map (\<lambda>i.
 (vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set (past_nodes V a)))))"
      using vote_Spectre.simps 
      by (metis (mono_tags, lifting)) 
    have ff1: "vote_Spectre V a c b = tie_break_int c b (signum (sum_list (map (\<lambda>i.
      (vote_Spectre (reduce_past V a) i c b)) (sorted_list_of_set (past_nodes V a)))))"
      using vote_Spectre.simps three by fastforce 
    then have ff2: "vote_Spectre V a c b = tie_break_int c b (signum (sum_list (map (\<lambda>i.
    (- vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set (past_nodes V a)))))" 
      using three 1 map_eq_conv ff
      by (smt (verit, best))   
    have "(map (\<lambda>i. - vote_Spectre (reduce_past V a) i b c) (sorted_list_of_set (past_nodes V a)))
     = (map uminus (map (\<lambda>i. vote_Spectre (reduce_past V a) i b c)
       (sorted_list_of_set (past_nodes V a))))" 
      using map_map by auto       
    then have "vote_Spectre V a c b = - (tie_break_int b c (signum (sum_list (map (\<lambda>i.
    (vote_Spectre (reduce_past V a) i b c)) (sorted_list_of_set (past_nodes V a))))))" 
      using  antisymmetric_sumlist 1 ff2 antisymmetric_signum antisymmetric_tie_break
      by (metis verit_minus_simplify(4)) 
    then show ?thesis using  ff
      by presburger 
  next
    case four
    then have ff: "vote_Spectre V a b c = signum (sum_list (map (\<lambda>i.
   (vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a))))"
      using vote_Spectre.simps
      by (metis (mono_tags, lifting)) 
    then have ff2: "vote_Spectre V a c b =  signum (sum_list (map (\<lambda>i.
    (- vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a))))" 
      using four 1 vote_Spectre.simps map_eq_conv
      by (smt (z3)) 
    have "(map (\<lambda>i. - vote_Spectre V i b c) (sorted_list_of_set (future_nodes V a)))
     = (map uminus (map (\<lambda>i. vote_Spectre V i b c) (sorted_list_of_set (future_nodes V a))))" 
      using map_map by auto       
    then have "vote_Spectre V a c b = - ( signum (sum_list (map (\<lambda>i.
    (vote_Spectre V i b c)) (sorted_list_of_set (future_nodes V a)))))" 
      using  antisymmetric_sumlist 1 ff2 antisymmetric_signum 
      by (metis verit_minus_simplify(4)) 
    then show ?thesis using ff
      by linarith 
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
  unfolding Spectre_Order_def 
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
  then show "tie_break_int a a
    (signum (sum_list (map (\<lambda>i. vote_Spectre V i a a) (sorted_list_of_set (verts V))))) = 1"
    using l_def ne  tie_break_int.simps
      list.exhaust verit_comp_simplify1(1) by auto
qed


lemma vote_Spectre_one_exists:
  assumes "blockDAG V"
    and "a \<in> verts V" 
    and "b \<in> verts V" 
  shows "\<exists> i \<in> verts V. vote_Spectre V i a b \<noteq> 0"
proof
  show "a \<in> verts V" using assms(2) by simp
  show "vote_Spectre V a a b \<noteq> 0"
    using assms
  proof(cases a b a V rule: Spectre_casesAlt, simp, simp, simp, simp)
    case three
    then show ?thesis
      by (meson DAG.cycle_free blockDAG.axioms(1)) 
  next
    case four
    then show ?thesis
      by blast 
  qed
qed

lemma Spectre_Order_antisym: 
  assumes "blockDAG V"
    and "a \<in> verts V" 
    and "b \<in> verts V" 
    and "a \<noteq> b"
  shows "Spectre_Order V a b = (\<not> (Spectre_Order V b a))"
proof -
  obtain wit where wit_in: "vote_Spectre V wit a b \<noteq> 0 \<and> wit \<in> verts V" 
    using  vote_Spectre_one_exists assms
    by blast 
  obtain l where l_def: "l = (map (\<lambda>i. vote_Spectre V i a b) (sorted_list_of_set (verts V)))"
    by auto
  have "wit \<in>  set (sorted_list_of_set (verts V))" 
    using  wit_in sorted_list_of_set(1) 
      fin_digraph.finite_verts subs
    by (simp add: fin_digraph.finite_verts subs assms(1)) 
  then have "vote_Spectre V wit a b \<in> set l" unfolding l_def
    by (metis (mono_tags, lifting) image_eqI list.set_map)
  then have dm: "tie_break_int a b (signum (sum_list l)) \<in> {-1,1}"
    by auto  
  obtain l2 where l2_def: "l2 = (map (\<lambda>i. vote_Spectre V i b a) (sorted_list_of_set (verts V)))"
    by auto
  have minus: "l2 = map uminus l"
    unfolding l_def l2_def map_map
    using  vote_Spectre_antisymmetric assms(4)
    by (metis comp_apply)  
  have anti: "tie_break_int a b (signum (sum_list l)) = 
                   - tie_break_int b a (signum (sum_list l2))" unfolding minus 
    using antisymmetric_sumlist antisymmetric_tie_break antisymmetric_signum assms(4) by metis
  then show "?thesis" unfolding Spectre_Order_def using anti l_def dm l2_def 
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


lemma vote_Spectre_Preserving:
  assumes "c \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b"
  shows "vote_Spectre G a b c \<in> {0,1}"
  using assms
proof(induction G a b c rule: vote_Spectre.induct)
  case (1 V a b c)
  then show ?case 
  proof(cases a b c V rule:Spectre_casesAlt)
    case no_bD
    then show ?thesis by auto
  next
    case equal
    then show ?thesis  by simp
  next
    case one
    then show ?thesis by auto   
  next
    case two
    then show ?thesis
      by (metis "local.1.prems" trancl_trans) 
  next
    case three
    then have a_not_gen: "\<not> blockDAG.is_genesis_node V a"
      using blockDAG.genesis_reaches_nothing
      by metis
    then have bD: "blockDAG (reduce_past V a)" using blockDAG.reduce_past_dagbased 
        three by auto
    have b_in2: "b \<in> past_nodes V a" using three by auto
    also have c_in2: "c \<in> past_nodes V a" using three by auto
    ultimately have "c \<rightarrow>\<^sup>+\<^bsub>reduce_past V a\<^esub> b" using DAG.reduce_past_path2 three 1
      by (metis blockDAG.axioms(1)) 
    then have allsorted01:"\<forall>x. x \<in> set (sorted_list_of_set (past_nodes V a)) \<longrightarrow>
          vote_Spectre (reduce_past V a) x b c \<in> {0, 1}" using 1 three by auto
    then have all01: "\<forall>x. x \<in> (past_nodes V a) \<longrightarrow>
          vote_Spectre (reduce_past V a) x b c \<in> {0, 1}"
      using  subs three sorted_list_of_set(1) DAG.finite_past
      by metis 
    obtain wit where wit_in: "wit \<in> past_nodes V a" 
      and wit_vote: "vote_Spectre (reduce_past V a) wit b c \<noteq> 0"
      using vote_Spectre_one_exists b_in2 c_in2 bD induce_subgraph_verts reduce_past.simps
      by metis 
    then have wit_vote1: "vote_Spectre (reduce_past V a) wit b c = 1" using all01
      by blast 
    obtain the_map where the_map_in: 
      "the_map = (map (\<lambda>i. vote_Spectre (reduce_past V a) i b c) 
               (sorted_list_of_set (past_nodes V a)))"
      by auto  
    have all01_1: "\<forall>x \<in> set the_map. x \<in> {0,1}"
      unfolding the_map_in set_map 
      using allsorted01 by blast 
    have "\<exists>x \<in> set the_map. x = 1"
      unfolding the_map_in set_map 
      using wit_in wit_vote1
        sorted_list_of_set(1) DAG.finite_past bD subs
      by (metis (no_types, lifting) image_iff three) 
    then have "\<exists>x \<in> set the_map. x > 0"
      using zero_less_one by blast 
    moreover have "\<forall>x \<in> set the_map. x \<ge> 0" using all01_1
      by (metis empty_iff insert_iff less_int_code(1) not_le_imp_less zero_le_one) 
    ultimately have "signum (sum_list the_map) = 1" using sumlist_one_mono by simp
    then have "tie_break_int b c (signum (sum_list the_map)) = 1" using tie_break_int.simps
      by simp
    then have "vote_Spectre V a b c = 1 " unfolding the_map_in using three vote_Spectre.simps
      by simp
    then show ?thesis by simp
  next
    case four 
    then have all01: "\<forall>a2. a2 \<in> set (sorted_list_of_set (future_nodes V a)) \<longrightarrow>
                              vote_Spectre V a2 b c \<in> {0,1}"
      using 1
      by metis
    have "\<forall>a2. a2 \<in> set (sorted_list_of_set (future_nodes V a)) 
                \<longrightarrow> vote_Spectre V a2 b c \<ge> 0" 
    proof safe
      fix a2
      assume " a2 \<in> set (sorted_list_of_set (future_nodes V a))"
      then have "vote_Spectre V a2 b c \<in> {0, 1}" using all01 by auto
      then show "vote_Spectre V a2 b c  \<ge> 0"
        by fastforce
    qed 
    then have "(sum_list (map (\<lambda>i. vote_Spectre V i b c) 
      (sorted_list_of_set (future_nodes V a)))) \<ge> 0" using sum_list_mono sum_list_0
      by metis 
    then have "signum (sum_list (map (\<lambda>i. vote_Spectre V i b c) 
      (sorted_list_of_set (future_nodes V a)))) \<in> {0,1}" unfolding signum.simps
      by simp 
    then show ?thesis using four by simp 
  qed 
qed



lemma Spectre_Order_Preserving:
  assumes "blockDAG G"
    and "b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a"
  shows "Spectre_Order G a b" 
proof - 
  have set_ordered: "set (sorted_list_of_set (verts G)) = verts G"
    using assms(1) subs fin_digraph.finite_verts
      sorted_list_of_set by auto
  have a_in: "a \<in> verts G" using wf_digraph.reachable1_in_verts(2) assms subs
    by metis 
  have b_in: "b \<in> verts G" using wf_digraph.reachable1_in_verts(1) assms subs
    by metis 
  obtain the_map where the_map_in: 
    "the_map = (map (\<lambda>i. vote_Spectre G i a b) (sorted_list_of_set (verts G)))" by auto
  obtain wit where wit_in: "wit \<in> verts G" and wit_vote: "vote_Spectre G wit a b \<noteq> 0"
    using vote_Spectre_one_exists a_in b_in assms(1)
    by blast 
  have "(vote_Spectre G wit a b) \<in> set the_map" 
    unfolding the_map_in set_map 
    using assms(1) fin_digraph.finite_verts 
      subs sorted_list_of_set(1) wit_in image_iff
    by metis 
  then have exune: "\<exists>x \<in> set the_map. x \<noteq> 0"
    using wit_vote by blast 
  have all01: "\<forall>x \<in> set the_map. x \<in> {0,1}" 
    unfolding set_ordered the_map_in set_map using vote_Spectre_Preserving assms(2) image_iff 
    by (metis (no_types, lifting))
  then have "\<exists>x \<in> set the_map. x = 1" using exune
    by blast 
  then have "\<exists>x \<in> set the_map. x > 0"
    using zero_less_one by blast 
  moreover have "\<forall>x \<in> set the_map. x \<ge> 0" using all01
    by (metis empty_iff insert_iff less_int_code(1) not_le_imp_less zero_le_one) 
  ultimately have "signum (sum_list the_map) = 1" using sumlist_one_mono by simp
  then have "tie_break_int a b (signum (sum_list the_map)) = 1" using tie_break_int.simps
    by simp
  then show ?thesis unfolding the_map_in Spectre_Order_def by simp  
qed


lemma Spectre_Order_Relation_Preserving:
  assumes "blockDAG G"
    and "b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a"
  shows "(a,b) \<in> (Spectre_Order_Relation G)"   
  unfolding Spectre_Order_Relation_def
  using assms  wf_digraph.reachable1_in_verts subs
    Spectre_Order_Preserving
    SigmaI case_prodI mem_Collect_eq by fastforce 

definition (in blockDAG) test:: "int"
  where "test = 1" 


lemma [code]:  "blockDAG.test = 1" sorry


end

