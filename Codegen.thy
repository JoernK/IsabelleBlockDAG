(* 
    Author:     Joern Kussmaul
*)


theory Codegen
  imports blockDAG Spectre Ghostdag Extend_blockDAG Verts_To_List
begin

section \<open>Code Generation\<close>

fun arcAlt::  "('a,'b) pre_digraph \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool"
  where "arcAlt G e uv = (e \<in> arcs G \<and> tail G e = fst uv \<and> head G e = snd uv)"

fun iterate:: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where  "iterate S P = Finite_Set.fold (\<lambda> r A. S r \<and> A) False P "

lemma (in DAG) arcAlt_eq:                     
  shows "arcAlt G e uv = wf_digraph.arc G e uv"
  unfolding arc_def arcAlt.simps by simp
  
lemma [code]: "blockDAG G = (DAG G \<and> ((\<exists> p \<in> verts G. ((\<forall>r \<in> verts G. (r \<rightarrow>\<^sup>+\<^bsub>G\<^esub> p \<or> r = p)))) \<and>
 (\<forall>e \<in> (arcs G). \<forall> u \<in> verts G. \<forall> v \<in> verts G. 
(u \<rightarrow>\<^sup>+\<^bsub>(pre_digraph.del_arc G  e)\<^esub> v) \<longrightarrow> \<not> arcAlt G e (u,v))))" 
  using  DAG.arcAlt_eq  wf_digraph_def DAG.axioms(1)
    digraph.axioms(1) fin_digraph.axioms(1) wf_digraph.arcE blockDAG_axioms_def blockDAG_def 
  by metis
     
lemma [code]: "DAG G = (digraph G \<and> (\<forall>v \<in> verts G. \<not>(v \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v)))"
  unfolding DAG_axioms_def DAG_def
  by (metis digraph.axioms(1) fin_digraph.axioms(1) wf_digraph.reachable1_in_verts(1)) 

lemma [code]: "digraph G = (fin_digraph G \<and> loopfree_digraph G \<and> nomulti_digraph G)"
  unfolding digraph_def by auto

lemma [code]: "wf_digraph G = (
 (\<forall>e \<in> arcs G. tail G e \<in> verts G) \<and>
 (\<forall>e \<in> arcs G. head G e \<in> verts G))"
  using wf_digraph_def by auto

lemma [code]: "nomulti_digraph G = (wf_digraph G \<and> 
  (\<forall>e1 \<in> arcs G. \<forall> e2 \<in> arcs G .
     arc_to_ends G e1 = arc_to_ends G e2 \<longrightarrow> e1 = e2))"
  unfolding nomulti_digraph_def nomulti_digraph_axioms_def by auto

lemma [code]: "loopfree_digraph G = (wf_digraph G \<and> (\<forall>e \<in> arcs G.  tail G e \<noteq> head G e))"
  unfolding loopfree_digraph_def loopfree_digraph_axioms_def by auto

lemma [code]: "pre_digraph.del_arc G a =
 \<lparr> verts = verts G, arcs = arcs G - {a}, tail = tail G, head = head G \<rparr>"
  by (simp add: pre_digraph.del_arc_def)


lemma [code]: "fin_digraph G = (wf_digraph G \<and> (card (verts G) > 0 \<or> verts G = {})
   \<and> ((card (arcs G) > 0 \<or> arcs G = {})))" 
  using card_ge_0_finite fin_digraph_def fin_digraph_axioms_def
  by (metis card_gt_0_iff finite.emptyI)


fun vote_Spectre_Int:: "(integer, integer\<times>integer) pre_digraph \<Rightarrow>
 integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer"
  where "vote_Spectre_Int V a b c = integer_of_int (vote_Spectre V a b c)"

fun SpectreOrder_Int:: "(integer, integer\<times>integer) pre_digraph \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> bool"
  where "SpectreOrder_Int G = Spectre_Order G"

fun OrderDAG_Int::  "(integer, integer\<times>integer) pre_digraph \<Rightarrow>
 integer \<Rightarrow> (integer set \<times> integer list)" 
 where " OrderDAG_Int V a =  (OrderDAG V (nat_of_integer a))"
 

export_code top_sort anticone set blockDAG pre_digraph_ext snd fst vote_Spectre_Int
 SpectreOrder_Int OrderDAG_Int
 in Haskell module_name DAGS file "code/" 

notepad begin
  let ?G = "\<lparr>verts = {1::int,2,3,4,5,6,7,8,9,10}, arcs = {(2,1),(3,1),(4,1),
  (5,2),(6,3),(7,4),(8,5),(8,3),(9,6),(9,4),(10,7),(10,2)}, tail = fst, head = snd\<rparr>"
  let ?a = "2"
  let ?b = "3"
  let ?c = "4"
  value "blockDAG ?G"
  value "Spectre_Order ?G ?a ?b \<and> Spectre_Order ?G ?b ?c \<and> \<not> Spectre_Order ?G ?a ?c"
end


subsection \<open>Extend Graph\<close>

  
declare  pre_digraph.del_vert_def [code]
declare Append_One_axioms_def [code] 
declare Honest_Append_One_axioms_def[code] 
declare Append_One_def [code] 
declare Honest_Append_One_def [code] 
declare Append_One_Honest_Dishonest_axioms_def [code]
declare Append_One_Honest_Dishonest_def [code]




subsection \<open>GHOSTDAG Not One Appending Robust\<close>

datatype  FV = V1 | V2 | V3 | V4 | V5 | V6 | V7 | V8 | V9 | V10

fun FV_Suc ::" FV \<Rightarrow> FV set" 
  where 
  "FV_Suc V1 = {V1,V2,V3,V4,V5,V6,V7,V8,V9,V10}" |
  "FV_Suc V2 = {V2,V3,V4,V5,V6,V7,V8,V9,V10}" |
  "FV_Suc V3 = {V3,V4,V5,V6,V7,V8,V9,V10}" |
  "FV_Suc V4 = {V4,V5,V6,V7,V8,V9,V10}" |
  "FV_Suc V5 = {V5,V6,V7,V8,V9,V10}" |
  "FV_Suc V6 = {V6,V7,V8,V9,V10}" |
  "FV_Suc V7 = {V7,V8,V9,V10}" |
  "FV_Suc V8 = {V8,V9,V10}" |
  "FV_Suc V9 = {V9,V10}" |
  "FV_Suc V10 = {V10}"
fun less_eq_FV:: "FV \<Rightarrow> FV \<Rightarrow> bool" 
  where "less_eq_FV a b = (b \<in> FV_Suc a)"

fun less_FV :: "FV \<Rightarrow> FV \<Rightarrow> bool"
  where "less_FV a b = (a \<noteq> b \<and> less_eq_FV a b)"

lemma FV_cases:
  fixes x::FV
  obtains "x = V1" | "x = V2" | "x = V3" | "x = V4" | "x = V5" | "x = V6" | "x = V7" | "x = V8" 
  | "x = V9" | "x = V10" 
proof(cases x, auto) qed

instantiation FV ::linorder 
begin 
definition "less_eq \<equiv> less_eq_FV" 
definition "less \<equiv> less_FV" 

instance 
proof(standard)
  fix x y z ::FV
  show "x \<le> x" unfolding less_eq_FV_def less_eq_FV.simps 
  proof(cases x, auto) qed
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_FV_def less_eq_FV.simps 
    by(cases x rule: FV_cases) (cases y rule: FV_cases, auto)+
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  unfolding less_FV_def less_FV.simps less_eq_FV_def less_eq_FV.simps 
  by(cases x rule: FV_cases) (cases y rule: FV_cases, auto)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  unfolding less_FV_def less_FV.simps less_eq_FV_def less_eq_FV.simps 
  by (cases x rule: FV_cases)(cases y rule: FV_cases, auto)+
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  unfolding less_FV_def less_FV.simps less_eq_FV_def less_eq_FV.simps 
  by (cases x rule: FV_cases)(cases y rule: FV_cases, auto)+
qed
end

instantiation FV ::enum
begin

definition "enum_FV \<equiv> [V1,V2,V3,V4,V5,V6,V7,V8,V9,V10]"

fun enum_all_FV:: "(FV \<Rightarrow> bool) \<Rightarrow> bool "
where "enum_all_FV P = Ball {V1,V2,V3,V4,V5,V6,V7,V8,V9,V10} P"

fun enum_ex_FV:: "(FV \<Rightarrow> bool) \<Rightarrow> bool "
where "enum_ex_FV P = Bex {V1,V2,V3,V4,V5,V6,V7,V8,V9,V10} P"
  
instance 
  apply(standard)
     apply(simp_all) 
  unfolding enum_FV_def UNIV_def 
proof -
  show "{x. True} = set [V1, V2, V3, V4, V5, V6, V7, V8, V9, V10]"
  proof safe 
    fix x::FV
    show " x \<in> set [V1, V2, V3, V4, V5, V6, V7, V8, V9, V10]"
      using FV_cases by auto
  qed
  show " distinct [V1, V2, V3, V4, V5, V6, V7, V8, V9, V10]" by auto
  fix P 
  show A: "(P V1 \<and> P V2 \<and> P V3 \<and> P V4 \<and> P V5 \<and> P V6 \<and> P V7 \<and> P V8 \<and> P V9 \<and> P V10) = All P"
    unfolding All_def 
  proof(standard, auto, standard)
    fix x 
    show "P V1 \<Longrightarrow>
         P V2 \<Longrightarrow> P V3 \<Longrightarrow> P V4 \<Longrightarrow> P V5 \<Longrightarrow> P V6 \<Longrightarrow> P V7 \<Longrightarrow> 
    P V8 \<Longrightarrow> P V9 \<Longrightarrow> P V10 \<Longrightarrow> P x = True"
    proof(cases x rule: FV_cases, auto) qed
  qed
  show "(P V1 \<or> P V2 \<or> P V3 \<or> P V4 \<or> P V5 \<or> P V6 \<or> P V7 \<or> P V8 \<or> P V9 \<or> P V10) = Ex P"
  proof(safe, auto)
    fix x::FV
    show "P x \<Longrightarrow>
         \<not> P V1 \<Longrightarrow>
         \<not> P V2 \<Longrightarrow> \<not> P V3 \<Longrightarrow> \<not> P V4 \<Longrightarrow> \<not> P V5 \<Longrightarrow> \<not> P V6 \<Longrightarrow> \<not> P V7 \<Longrightarrow> \<not> P V8 \<Longrightarrow> 
          \<not> P V10 \<Longrightarrow> P V9 " 
    proof(cases x rule: FV_cases, auto) qed
  qed
qed

end 

notepad 
begin
  let ?G = "\<lparr>verts = {V1,V2,V3,V4,V5,V6,V7,V8}, arcs = {(V2,V1),(V3,V2),(V4,V2),(V5,V2),
  (V6,V1),(V7,V6),(V8,V7)}, tail = fst, head = snd\<rparr>"
  value "blockDAG ?G"
  value "OrderDAG ?G 2"
  let ?G2 = "\<lparr>verts = {V1,V2,V3,V4,V5,V6,V7,V8,V9}, arcs = {(V2,V1),(V3,V2),(V4,V2),(V5,V2),
  (V6,V1),(V7,V6),(V8,V7),(V9,V3),(V9,V4),(V9,V5),(V9,V8)}, tail = fst, head = snd\<rparr>"
  value "blockDAG ?G2"
  value "OrderDAG ?G2 2"
  value "Append_One ?G ?G2 V9"
  value "Honest_Append_One ?G ?G2 V9"
  let ?G3 = "\<lparr>verts = {V1,V2,V3,V4,V5,V6,V7,V8,V9,V10}, arcs = {(V2,V1),(V3,V2),(V4,V2),(V5,V2),
  (V6,V1),(V7,V6),(V8,V7),(V9,V3),(V9,V4),(V9,V5),(V9,V8),(V10,V3),(V10,V4),(V10,V5)},
   tail = fst, head = snd\<rparr>"
  value "blockDAG ?G3"
  value "Append_One ?G2 ?G3 V10"
  value "Append_One_Honest_Dishonest ?G ?G2 V9 ?G3 V10"
  value "OrderDAG ?G3 2"
  value "(V6,V2) \<in> GHOSTDAG 2 ?G" 
  value "(V6,V2) \<notin> GHOSTDAG 2 ?G3"


  let ?G4 = "\<lparr>verts = {V1,V2,V3,V4}, arcs = {(V2,V1),(V3,V1),(V4,V2)}, tail = fst, head = snd\<rparr>"
  value "blockDAG ?G4"
  value "top_sort ?G4 (sorted_list_of_set (verts ?G4 - {V4,V1}))"
  value "top_sort ?G4 (sorted_list_of_set (verts ?G4 - {V1}))"
  
  value "Depth_first_search ?G3"

end


end
