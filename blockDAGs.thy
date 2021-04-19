(*  Title:      HOL/blockDAGs.thy
    Author:     Joern Kussmaul
*)

section \<open>blockDAGs\<close>

theory blockDAGs
  imports Main HOL.HOL
begin

datatype 'Block blockDAG = Gen 'Block |Cons 'Block "'Block blockDAG" "'Block set" 

fun in_dag:: "'Block blockDAG \<Rightarrow> 'Block \<Rightarrow> bool" 
  where 
  "in_dag (Gen x) a = (x = a)"
| "in_dag (Cons b dag l) a  = (if (b=a) then True else (in_dag dag a))"

fun in_dag_edges:: "'Block blockDAG \<Rightarrow> 'Block \<Rightarrow> 'Block set  \<Rightarrow> bool" 
  where 
  "in_dag_edges (Gen x) a l = (if (x=a & l={}) then True else False)"
| "in_dag_edges (Cons b dag l) a l2 = (if (b=a & l=l2) then True else (in_dag_edges dag a l2))"


fun to_list:: "'Block blockDAG \<Rightarrow> 'Block list"
  where 
  "to_list (Gen x) = [x]"
| "to_list (Cons b dag l) = b # (to_list dag)"

fun to_set:: "'Block blockDAG \<Rightarrow> 'Block set"
  where 
  "to_set(Gen x) = {x}"
| "to_set(Cons b dag l) = {b} \<union> (to_set dag)"

fun past_rec:: "'Block blockDAG \<Rightarrow> 'Block set \<Rightarrow> 'Block set"
  where
  "past_rec (Gen x) a = ( if (x \<in> a) then {x} else {})"
| "past_rec (Cons b dag l) a = 
  ( if (b \<in> a) 
      then ((past_rec dag ((a)\<union>l) ) \<union> {b}) 
      else (past_rec dag a))" 

fun past:: "'Block blockDAG \<Rightarrow> 'Block \<Rightarrow> 'Block set"
  where
  "past blockDAG b = (past_rec blockDAG {b})" 


fun tips_rec::  "'Block blockDAG  \<Rightarrow> 'Block set \<Rightarrow> 'Block set"
  where
  "tips_rec (Gen x) l2 =  (if (x \<in> l2) then {} else {x})"
| "tips_rec (Cons b dag l1) l2 =  (if (b \<in> (l1 \<union> l2)) then tips_rec dag (l1 \<union> l2)
 else ({b} \<union> tips_rec dag (l1 \<union> l2)))"

fun tips::  "'Block blockDAG  \<Rightarrow> 'Block set"
  where
  "tips bdag = (tips_rec bdag {})"

fun no_duplicates_rec:: "'Block blockDAG \<Rightarrow> 'Block set \<Rightarrow> bool"
  where
  "no_duplicates_rec (Gen x) l = (if (x \<in> l) then False else True)"
| "no_duplicates_rec (Cons b dag l1) l2 = (if (b \<in> l2) then False else 
      (no_duplicates_rec dag (l2 \<union> {b})))"    

fun no_duplicates:: "'Block blockDAG \<Rightarrow> bool"
  where 
  "no_duplicates blockDAG = no_duplicates_rec blockDAG {}"


fun well_formed:: "'Block blockDAG \<Rightarrow> bool"
  where 
  "well_formed (Gen x) = True" 
| "well_formed (Cons b dag l) =
     (\<not>(b \<in> l) & \<not>(l = {}) & \<not>(in_dag dag b) & (well_formed dag)
      & (\<forall>x. ((x \<in> (past_rec dag l)) \<longleftrightarrow>  ((x \<in> l)))))"


fun del_from_dag:: "'Block blockDAG \<Rightarrow> 'Block \<Rightarrow> 'Block blockDAG"
  where
  "del_from_dag (Gen x) a = (Gen x)"
| "del_from_dag (Cons x dag l1) a = (if (\<not>(a \<in> (tips (Cons x dag l1)))) then (Cons x dag l1) 
    else (if (a = x) then dag else (Cons x (del_from_dag dag a) l1)))"


fun equals_gen:: "'Block blockDAG \<Rightarrow> 'Block \<Rightarrow> bool"
  where 
  "equals_gen (Gen a) b = (a = b)"
|  "equals_gen (Cons a dag l) b = equals_gen dag b"
lemma del_length [simp]: "size( del_from_dag dag a) \<le> (size dag)"
  apply(induct_tac dag)
   apply(simp)
  apply(auto)
  done
   
(*lemma del_length_less [simp]: 
  shows "((a \<in> (tips dag)) & \<not>(equals_gen dag a))
   \<longrightarrow>  size(del_from_dag dag a) < (size dag)"
  apply(induct_tac dag)
  apply(simp)
*)
  

  

fun equal:: "'Block blockDAG \<Rightarrow> 'Block blockDAG \<Rightarrow> bool" 
  where
  "equal (Gen a) (Gen b) = (a = b)"
| "equal (Cons a dag l) (Cons b dag2 l2) = (if ((a = b) & (l=l2)) then (equal dag dag2)
   else ( (a \<in> (tips dag2)) & (b \<in> (tips dag)) &
   (in_dag_edges dag b l2) & (in_dag_edges dag2 a l)
    &  (equal (del_from_dag dag b)( del_from_dag dag2 a))))"
| "equal (Gen a) (Cons b dag l) = False"
| "equal (Cons b dag l) (Gen a)= False"

lemma eas0 [simp]: "well_formed (Cons a dag l) \<longrightarrow> a \<in> (tips (Cons a dag l))"
  by auto

lemma eaaas [simp]: "a \<in> l \<longrightarrow> (a \<in> (l \<union> l2))"
  by auto

lemma eaaas2 [simp]: "a \<notin> (l \<union> l2) \<longleftrightarrow> (a \<notin> l & a \<notin> l2)"
  by auto

lemma wfr [simp]: "well_formed (Cons a dag l) \<longrightarrow> well_formed dag"
  by auto

lemma eas [simp]: "to_list (Gen a) = [a]"
  by auto

lemma eas2 [simp]: "to_list (Cons b (Gen  a) c)  = [b,a]"
  by auto

lemma eas3 [simp]: "(set (to_list (Cons b (Gen a) c)) = {a,b})"
  by auto

lemma eas4 [simp]: "tips (Gen a) = {a}"
  by simp

lemma eas5 [simp]: "tips (Cons b (Gen a) {}) = {a,b}"
  by auto

lemma eas6 [simp]: "(no_duplicates (Cons b (Gen a) {a})) \<Longrightarrow> (tips (Cons b (Gen a) {a}) = {b})"
  by auto

lemma eas7 [simp]: "well_formed (Gen a)"
  by simp

lemma eas8 [simp]: "(no_duplicates (Cons b (Gen a) {a})) \<Longrightarrow> well_formed (Cons b (Gen a) {a})"
  by auto

lemma eas9 [simp]: "\<not>(well_formed (Cons b (Gen a) {}))"
  by simp

lemma eas10 [simp]: "(let dag = (Cons c (Cons b (Gen a) {a}) {a,b}) in 
  ((no_duplicates dag) \<longrightarrow> (well_formed dag)))"
  by auto

lemma eas11 [simp]:"(let dag = (Cons c (Cons b (Gen a) {a}) {a}) in 
  ((no_duplicates dag) \<longrightarrow> (well_formed dag)))"
  by auto

lemma eas12 [simp]:"(let dag = (Cons c (Cons b (Gen a) {c}) {a}) in 
  ((no_duplicates dag) \<longrightarrow> \<not>(well_formed dag)))"
  by auto

lemma eas13 [simp]: "\<not>(no_duplicates (Cons a (Gen a) {}))"
  by auto

lemma eas14 [simp] : " ((equal (Gen a ) (Cons b dag2 l2)) \<longleftrightarrow> (equal (Cons b dag2 l2) (Gen a)))"
  by auto

lemma eas15 [simp]: " ((equal (Gen a ) (Gen b)) \<longleftrightarrow> (equal (Gen b) (Gen a)))"
  by auto

lemma easaf [simp]: "no_duplicates (Cons a dag l) \<longrightarrow> \<not> (in_dag dag a)"
  apply(induct_tac dag)
   apply(simp)
  oops
  
 

lemma eaas [simp]:
  "a \<in> (tips (Cons b dag l)) \<longrightarrow> a \<notin> l"
  oops

lemma eas152 [simp]: "(x \<notin> (tips dag)) \<longrightarrow> ((del_from_dag dag x ) = dag)"
  apply(induct_tac dag)
  apply(auto)
  done


lemma eas17 [simp]: "equal dag1 dag1"
  apply(induct_tac dag1)
   apply(simp)
  apply(auto)
  done
lemma eas19 [simp]: "equal dag1 dag2 \<longrightarrow> equal (Cons a dag1 l) (Cons a dag2 l)"
  apply(auto)
  done
lemma eas20 [simp]:
  assumes "well_formed dag1"
  assumes "well_formed dag2"
  shows "equal (Cons a dag1 l1) (Cons b dag2 l2) \<longrightarrow>
  equal (del_from_dag dag1 b) (del_from_dag dag2 a)"
  apply(induction)
  oops

lemma eas16 [simp]:
  assumes "well_formed dag1"
  assumes "well_formed dag2"
  shows "equal dag1 dag2 \<longleftrightarrow> equal dag2 dag1"
  
(*
    apply(induction)
    apply (smt (verit, ccfv_SIG) del_from_dag.elims eas15 equal.simps(3) equal.simps(4))
    apply(induction)
     apply simp_all
 *) 

end
