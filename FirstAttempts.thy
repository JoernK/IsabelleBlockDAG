(*  Title:      HOL/blockDAG.thy
    Author:     Joern Kussmaul
*)

section \<open>BlockDAGs\<close>

theory FirstAttempts
  imports Main
begin

datatype 'Block blockDAG = Gen 'Block |Cons 'Block "'Block blockDAG" "'Block set" 
fun in_dag:: "'Block blockDAG \<Rightarrow> 'Block \<Rightarrow> bool" 
  where 
  "in_dag (Gen x) a = (if x=a then True else False)"
| "in_dag (Cons b dag l) a  = (if b=a then True else (in_dag dag a))"

fun to_list:: "'Block blockDAG \<Rightarrow> 'Block list"
  where 
  "to_list (Gen x) = [x]"
| "to_list (Cons b dag l) = b # (to_list dag)"

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



fun tips_rec::  "'Block blockDAG  \<Rightarrow> 'Block list \<Rightarrow> 'Block list"
  where
  "tips_rec (Gen x) l2 =  l2"
| "tips_rec (Cons b dag l1) l2 = tips_rec dag (filter (\<lambda>a. \<not>(a \<in> l1)) l2)"

fun tips::  "'Block blockDAG  \<Rightarrow> 'Block set"
  where
  "tips bdag = set (tips_rec bdag (to_list bdag))"

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
      & (\<forall>x. ((x \<in> (past_rec dag l)) \<longrightarrow>  ((x \<in> l)))))"


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

lemma eas12 [simp]: "\<not>(no_duplicates (Cons a (Gen a) {}))"
  by auto
end
