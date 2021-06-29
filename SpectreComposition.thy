theory SpectreComposition
  imports Main Graph_Theory.Graph_Theory blockDAG Composition Spectre
begin

context tie_break_compositionGraph
begin


fun tie_break_comp_int:: "'a set \<Rightarrow> 'a set \<Rightarrow> int \<Rightarrow> int"
  where "tie_break_comp_int a b i =
 (if i=0 then (if (le a b) then 1 else -1) else 
              (if i > 0 then 1 else -1))"

fun sumlist_break_comp_acc :: "'a set \<Rightarrow>'a set \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int"
  where "sumlist_break_comp_acc a b s [] = tie_break_comp_int a b s"
  | "sumlist_break_comp_acc a b s (x#xs) = sumlist_break_comp_acc a b (s + x) xs"

fun sumlist_break_comp :: "'a set \<Rightarrow>'a set \<Rightarrow> int list \<Rightarrow> int"
  where "sumlist_break_comp a b [] = 0"
  | "sumlist_break_comp a b (x # xs) = sumlist_break_comp_acc a b 0 (x # xs)"

function vote_SpectreComp :: "('a set,'b) pre_digraph \<Rightarrow>'a set\<Rightarrow> 'a set\<Rightarrow> 'a set\<Rightarrow> int" 
  where
  "vote_SpectreComp V a b c = (
  if (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V) then 0 else 
  if (b=c)  then 1 else 
  if ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then card a else
  if ((a \<rightarrow>\<^sup>*\<^bsub>V\<^esub> c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b)) then card a else
  if ((a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>V\<^esub> c)) then 
   (sumlist_break_comp b c (map (\<lambda>i.
 (vote_SpectreComp (DAG.reduce_past V a) i b c)) (linorder.sorted_list_of_set le ((DAG.past_nodes V a)))))
 else 
   sumlist_break_comp b c (map (\<lambda>i.
   (vote_SpectreComp V i b c)) (linorder.sorted_list_of_set le (DAG.future_nodes V a))))"
  by auto
termination
proof
let ?R = " measures [( \<lambda>(V, a, b, c). (card (verts V))),  ( \<lambda>(V, a, b, c). card {e. e \<rightarrow>\<^sup>*\<^bsub>V\<^esub> a})] "  
  show "wf ?R"
    by simp 
next 
  fix V::"('a set, 'b) pre_digraph" 
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
  fix V::"('a set, 'b) pre_digraph" 
  fix x a b c
  assume bD: " \<not> (\<not> blockDAG V \<or> a \<notin> verts V \<or> b \<notin> verts V \<or> c \<notin> verts V)"
  then have a_in: "a \<in> verts V" using bD by simp
  assume "x \<in> set (linorder.sorted_list_of_set le (DAG.future_nodes V a))"
  then have "x \<in> DAG.future_nodes V a" using DAG.finite_future
    linorder.set_sorted_list_of_set bD subs tie_break_compositionGraph_axioms 
    tie_break_compositionGraph_def tie_break_compositionGraph_axioms_def
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


lemma compeq: 
  shows "vote_Spectre G a b c = vote_SpectreComp G' {a} {b} {c}" 
  sorry
