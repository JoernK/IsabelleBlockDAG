(* 
    Author:     Joern Kussmaul
*)

theory Spectre
  imports Main Graph_Theory.Graph_Theory blockDAG 
begin

section  \<open>Spectre\<close>
 
locale tie_breakingDAG = 
  fixes G::"('a::linorder,'b) pre_digraph"
  assumes is_blockDAG: "blockDAG G"

subsection  \<open>Functions and Definitions\<close>

fun tie_break_int:: "'a::linorder \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int"
  where "tie_break_int a b i =
 (if i=0 then (if (a \<le> b) then 1 else -1) else 
              (if i > 0 then 1 else -1))"

fun sumlist_break_acc :: "'a::linorder \<Rightarrow>'a \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int"
  where "sumlist_break_acc a b s [] = tie_break_int a b s"
  | "sumlist_break_acc a b s (x#xs) = sumlist_break_acc a b (s + x) xs"

fun sumlist_break :: "'a::linorder \<Rightarrow>'a \<Rightarrow> int list \<Rightarrow> int"
  where "sumlist_break a b [] = 0"
  | "sumlist_break a b (x # xs) = sumlist_break_acc a b 0 (x # xs)"

function vote_Spectre :: "('a::linorder,'b) pre_digraph \<Rightarrow>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> int" 
  where
  "vote_Spectre V a b c = (
  if (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V) then 0 else 
  if (b=c)  then 1 else 
  if ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 1  else
  if ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b)) then -1 else
  if ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 
   (sumlist_break b c (map (\<lambda>i.
 (vote_Spectre (DAG.reduce_past V a) i b c)) (sorted_list_of_set ((DAG.past_nodes V a)))))
 else 
   sumlist_break b c (map (\<lambda>i.
   (vote_Spectre V i b c)) (sorted_list_of_set (DAG.future_nodes V a))))"
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
  then have "card (verts (DAG.reduce_past V a)) < card (verts V)"   
    using bD blockDAG.reduce_less
    by metis
  then show "((DAG.reduce_past V a, x, b, c), V, a, b, c)
       \<in> measures
           [\<lambda>(V, a, b, c). card (verts V),
            \<lambda>(V, a, b, c). card {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a}]"
    by simp
next 
  fix V::"('a::linorder, 'b) pre_digraph" 
  fix x a b c
  assume bD: " \<not> (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V)"
  then have a_in: "a \<in> verts V" using bD by simp
  assume "x \<in> set (sorted_list_of_set (DAG.future_nodes V a))"
  then have "x \<in> DAG.future_nodes V a" using DAG.finite_future
    set_sorted_list_of_set bD subs
    by metis
  then have rr: "x \<rightarrow>\<^sup>+\<^bsub>V\<^esub> a" using DAG.future_nodes.simps bD subs mem_Collect_eq
    by metis
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

definition (in tie_breakingDAG) SpectreOrder:
  "SpectreOrder \<equiv> {(a,b). sumlist_break a b (map (\<lambda>i.
   (vote_Spectre G i a b)) (sorted_list_of_set (verts G))) = 1}"

subsubsection \<open>Lemmas\<close>

lemma domain_tie_break:
  shows "tie_break_int a b c \<in> {-1 ,0 ,1}"
  using  tie_break_int.simps by simp

lemma domain_sumlist_acc:
  shows "sumlist_break_acc a b c d \<in> {-1 ,0 ,1}"
proof(induction d arbitrary: a b c)
  case Nil
  then show ?case by auto
next
  case (Cons d2 d)
  then show ?case using Spectre.sumlist_break_acc.simps(2) by metis
qed

lemma domain_sumlist:
  shows "sumlist_break a b c  \<in> {-1 ,0 ,1}"
  using domain_sumlist_acc sumlist_break.simps(1)
  by (metis insertCI sumlist_break.elims) 

lemma Spectre_casesAlt:
  obtains (no_bD) "(\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V)"
  | (equal) "(blockDAG V \<and> a \<in> verts V \<or> b \<in> verts V \<or> c \<in> verts V) \<and> b = c" 
  | (one) "(blockDAG V \<and> a \<in> verts V \<or> b \<in> verts V \<or> c \<in> verts V) \<and>
         b \<noteq> c  \<and> ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))" 
  | (two) "(blockDAG V \<and> a \<in> verts V \<or> b \<in> verts V \<or> c \<in> verts V) \<and> b \<noteq> c  \<and> 
  \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))\<and> ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b))"
  | (three) "(blockDAG V \<and> a \<in> verts V \<or> b \<in> verts V \<or> c \<in> verts V) \<and> b \<noteq> c  \<and> 
  \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))\<and> \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b)) \<and> ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))"
  | (four) "(blockDAG V \<and> a \<in> verts V \<or> b \<in> verts V \<or> c \<in> verts V) \<and> b \<noteq> c  \<and> 
  \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))\<and> \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b)) \<and> \<not>((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))"
  by auto

lemma Spectre_theo:
  assumes "P 0"
  and "P 1"
  and "P (-1)" 
  and "P (sumlist_break b c (map (\<lambda>i.
 (vote_Spectre (DAG.reduce_past V a) i b c)) (sorted_list_of_set ((DAG.past_nodes V a)))))"
  and "P (sumlist_break b c (map (\<lambda>i.
   (vote_Spectre V i b c)) (sorted_list_of_set (DAG.future_nodes V a))))"
shows "P (vote_Spectre V a b c)"
  using assms vote_Spectre.simps
  by auto 

lemma domain_Spectre:
  shows "vote_Spectre V a b c \<in> {-1, 0, 1}"
proof(rule Spectre_theo)
  show "0 \<in> {- 1, 0, 1}" by simp
  show "1 \<in> {- 1, 0, 1}" by simp
  show " - 1 \<in> {- 1, 0, 1}" by simp
  show "sumlist_break b c
     (map (\<lambda>i. vote_Spectre (DAG.reduce_past V a) i b c) (sorted_list_of_set (DAG.past_nodes V a)))
    \<in> {- 1, 0, 1}" using domain_sumlist by simp 
  show "sumlist_break b c (map (\<lambda>i. vote_Spectre V i b c)
  (sorted_list_of_set (DAG.future_nodes V a))) \<in> {- 1, 0, 1}" using domain_sumlist by simp 
qed

lemma Spectre_antisymmetric: "b\<noteq>c \<Longrightarrow> (vote_Spectre V a b c) = - (vote_Spectre V a c b)"
proof(rule Spectre_casesAlt)
  let ?V = V
  let ?a = a 
  let ?b = b
  let ?c = c
  assume "\<not> blockDAG ?V \<or> ?a \<notin> verts ?V \<or> ?b \<notin> verts ?V \<or> ?c \<notin> verts ?V"
  then show "(vote_Spectre V a b c) = - (vote_Spectre V a c b)" using vote_Spectre.simps by auto
next
  show "b \<noteq> c \<Longrightarrow> (blockDAG V \<and> a \<in> verts V \<or> b \<in> verts V \<or> c \<in> verts V) \<and> b = c \<Longrightarrow>
    vote_Spectre V a b c = - vote_Spectre V a c b" by auto
  oops
  
lemma (in tie_breakingDAG) "total_on (verts G) SpectreOrder"
  unfolding total_on_def SpectreOrder 
 
proof safe
  fix x y
  assume x_in: "x \<in> verts G"
  assume y_in: "y \<in> verts G"
  assume "x \<noteq> y"
  assume "sumlist_break y x (map (\<lambda>i. vote_Spectre G i y x) (sorted_list_of_set (verts G))) \<noteq> 1"
  then show "sumlist_break x y (map (\<lambda>i. vote_Spectre G i x y) (sorted_list_of_set (verts G))) = 1"
  proof
    oops


end
