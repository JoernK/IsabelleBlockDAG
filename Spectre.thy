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
definition SPECTRE :: "('a::linorder,'b) pre_digraph \<Rightarrow> ('a \<times> 'a) set"
  where "SPECTRE G \<equiv> {(a,b) \<in> (verts G \<times> verts G). Spectre_Order G a b}"

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

lemma signum_mono:
  assumes "i \<le> j"
  shows "signum i \<le> signum j" using assms by simp

lemma tie_break_mono:
  assumes "i \<le> j"
  shows "tie_break_int b c  i \<le> tie_break_int b c j" using assms by simp

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


lemma domain_Spectre:
  shows "vote_Spectre V a b c \<in> {-1, 0, 1}"
proof(rule vote_Spectre.cases, auto) qed



lemma antisymmetric_tie_break:
  shows "b\<noteq>c  \<Longrightarrow> tie_break_int b c i = - tie_break_int c b (-i)"
  unfolding  tie_break_int.simps using less_not_sym by auto


lemma antisymmetric_sumlist:
  shows "sum_list (l::int list) = - sum_list (map (\<lambda>x. -x) l) "
proof(induct l, auto) qed


lemma antisymmetric_signum:
  shows "signum i = - (signum (-i))"
  by auto



lemma append_diff_sorted_set:
  assumes "a \<in> A"
  and "finite A"
shows "sum_list ((map (P::('a::linorder \<Rightarrow> int)))
   (sorted_list_of_set (A - {a}))) 
  = sum_list ((map P)(sorted_list_of_set (A))) - (P a)"
proof -
  let ?L1 =  "(sorted_list_of_set (A))"
  have d_1: "distinct ?L1" using sum_list_distinct_conv_sum_set sorted_list_of_set(2) by auto
   then have s_1: "sum_list ((map P) ?L1) 
  = sum P (set ?L1)" using sum_list_distinct_conv_sum_set by metis
  let ?L2 = " (sorted_list_of_set (A - {a}))"
  have d_2: "distinct ?L2" using sum_list_distinct_conv_sum_set sorted_list_of_set(2) by auto
  then have s_2: "sum_list ((map P) ?L2) 
  = sum P (set ?L2)" using sum_list_distinct_conv_sum_set by metis
  have s_3: "sum P (set ?L2) = sum P (set ?L1) - (P a)"
    using assms sorted_list_of_set(1)
    by (simp add: sum_diff1) 
  show ?thesis
    unfolding s_1 s_2 s_3 by simp
qed  


lemma append_diff_sorted_set2:
  assumes "a \<in> A"
  and "b \<in> A"
  and "a \<noteq> b"
  and "finite A"
shows "sum_list ((map (P::('a::linorder \<Rightarrow> int)))
   (sorted_list_of_set (A - {a} - {b}))) 
  = sum_list ((map P)(sorted_list_of_set (A))) - (P a) - (P b)"
  using assms append_diff_sorted_set
  by (metis finite_Diff insert_Diff insert_iff) 


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

end

