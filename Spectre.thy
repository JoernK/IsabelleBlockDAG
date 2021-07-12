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
 (if i=0 then (if (b < a) then -1 else 1) else 
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
  fixes V:: "('a::linorder,'b) pre_digraph"
  and a :: "'a::linorder" and  b::  "'a::linorder" and c ::  "'a::linorder"
  obtains (no_bD) "(\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V)"
  | (equal) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and> b = c" 
  | (one) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and>
         b \<noteq> c  \<and> ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c))" 
  | (two) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and> b \<noteq> c  \<and> 
  \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c))\<and> ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b))"
  | (three) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and> b \<noteq> c  \<and> 
  \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c))\<and> \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b)) \<and> ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))"
  | (four) "(blockDAG V \<and> a \<in> verts V \<and> b \<in> verts V \<and> c \<in> verts V) \<and> b \<noteq> c  \<and> 
  \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c))\<and> \<not>((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b)) \<and> \<not>((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c))"
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


lemma antisymmetric_tie_break:
  shows "b\<noteq>c \<and> i = 0 \<Longrightarrow> tie_break_int b c i = - tie_break_int c b i"
  unfolding  tie_break_int.simps using less_not_sym by auto


lemma antisymmetric_sumlist_acc:
  shows "b \<noteq> c  \<Longrightarrow> sumlist_break_acc b c s l1 = - sumlist_break_acc c b (-s) ( map (\<lambda>x. -x) l1)"
proof(induction l1 arbitrary:  b c s)
  case Nil
  then show ?case using sumlist_break_acc.simps(1) antisymmetric_tie_break by auto
next
  case (Cons a l)
  then show ?case unfolding list.simps(9) sumlist_break_acc.simps(2) by auto  
qed
  

lemma antisymmetric_sumlist:
  shows "b \<noteq> c \<Longrightarrow> sumlist_break b c l = - sumlist_break c b (map (\<lambda>x. -x) l) "
  using antisymmetric_sumlist_acc sumlist_break.simps(2) by (cases l) auto


lemma Spectre_antisymmetric: 
  shows "b \<noteq> c \<longrightarrow> vote_Spectre V a b c = - vote_Spectre V a c b"
proof -  
  consider (nbD) "\<not> blockDAG V" | (bD) "blockDAG V " by auto
  then show ?thesis
  proof( cases)
    case nbD
    then show ?thesis by auto
  next
    case bD
    then show ?thesis 
    proof(induct V a b c  rule:vote_Spectre.induct)
      fix V a b c
      assume "(\<And>x. \<not> (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V) \<Longrightarrow>
             b \<noteq> c \<Longrightarrow>
             \<not> (a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b \<and> (a, c) \<notin> (arcs_ends V)\<^sup>+) \<Longrightarrow>
             \<not> (a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c \<and> (a, b) \<notin> (arcs_ends V)\<^sup>+) \<Longrightarrow>
             a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b \<and> a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c \<Longrightarrow>
             x \<in> set (sorted_list_of_set (DAG.past_nodes V a)) \<Longrightarrow>
             blockDAG (DAG.reduce_past V a) \<Longrightarrow>
             b \<noteq> c \<longrightarrow>
             vote_Spectre (DAG.reduce_past V a) x b c = - vote_Spectre (DAG.reduce_past V a) x c b)
        "
        and
       "(\<And>x. \<not> (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V) \<Longrightarrow>
             b \<noteq> c \<Longrightarrow>
             \<not> (a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b \<and> (a, c) \<notin> (arcs_ends V)\<^sup>+) \<Longrightarrow>
             \<not> (a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c \<and> (a, b) \<notin> (arcs_ends V)\<^sup>+) \<Longrightarrow>
             \<not> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b \<and> a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c) \<Longrightarrow>
             x \<in> set (sorted_list_of_set (DAG.future_nodes V a)) \<Longrightarrow>
             blockDAG V \<Longrightarrow> b \<noteq> c \<longrightarrow> vote_Spectre V x b c = - vote_Spectre V x c b)"
      show "blockDAG V \<Longrightarrow> b \<noteq> c \<longrightarrow> vote_Spectre V a b c = - vote_Spectre V a c b "
        nitpick
                                 
lemma (in tie_breakingDAG) "total_on (verts G) SpectreOrder"
  unfolding total_on_def SpectreOrder 
  oops

end
