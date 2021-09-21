(* 
    Author:     Joern Kussmaul
*)

theory blockDAG_Type      
  imports blockDAG Spectre Codegen
begin

locale  simp_pre_digraph = 
  fixes G::"('a,'a \<times> 'a) pre_digraph"
  assumes tail_fst: "tail G = fst"
  and head_snd: "head G = snd"

locale simp_digraph = simp_pre_digraph + 
  assumes "digraph G"

locale simp_blockDAG =
  simp_pre_digraph  + 
  assumes bD: "blockDAG G"

sublocale simp_pre_digraph \<subseteq> pre_digraph .

sublocale simp_blockDAG \<subseteq> blockDAG using bD by simp

lemma ssubs: "simp_blockDAG G \<Longrightarrow> blockDAG G" using simp_blockDAG.bD by auto


definition empty_graph :: "('a,'a \<times> 'a) pre_digraph" 
  where "empty_graph = \<lparr>verts = {}, arcs = {}, tail = fst, head =  snd\<rparr>"

global_interpretation  simp_digraph empty_graph 
  unfolding simp_digraph_def simp_pre_digraph_def simp_digraph_axioms_def
    digraph_def fin_digraph_def wf_digraph_def  empty_graph_def
  fin_digraph_axioms_def loopfree_digraph_def loopfree_digraph_axioms_def nomulti_digraph_def
  nomulti_digraph_axioms_def by force
  

fun balance_BD :: "('a,'a \<times> 'a) pre_digraph \<Rightarrow> ('a,'a \<times> 'a) pre_digraph"
  where "balance_BD G = (if (simp_blockDAG G) then G else empty_graph)"


text \<open>Rewrite to get better performance (including base subgraph inducing)\<close>
definition reduce_past_empty:: "('a,'a \<times> 'a) pre_digraph \<Rightarrow> 'a \<Rightarrow> ('a,'a \<times> 'a) pre_digraph"
  where "reduce_past_empty G a = balance_BD (reduce_past G a)"

definition some_genesis :: "'a \<Rightarrow> ('a,'b) pre_digraph" 
  where "some_genesis a = \<lparr>verts = {a}, arcs = {}, tail = \<lambda>x. a, head =  \<lambda>x. a\<rparr>"

lemma some_bD:  "blockDAG (some_genesis a)"
unfolding some_genesis_def blockDAG_def blockDAG_axioms_def DAG_def DAG_axioms_def 
  digraph_def loopfree_digraph_def loopfree_digraph_axioms_def nomulti_digraph_def 
  nomulti_digraph_axioms_def wf_digraph_def fin_digraph_def fin_digraph_axioms_def 
  pre_digraph.del_arc_simps
  proof(safe,simp_all, simp add: arcs_ends_def)
    fix u::'a fix  v::'a fix e::'d
    have "\<not>  u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc (some_genesis a) e\<^esub> v " 
      unfolding some_genesis_def
      by (simp add: arcs_ends_def pre_digraph.del_arc_in) 
    then show "wf_digraph.arc \<lparr>verts = {a}, arcs = {}, tail = \<lambda>x. a, head = \<lambda>x. a\<rparr> e (u, v) \<Longrightarrow>
       u \<rightarrow>\<^sup>+\<^bsub>pre_digraph.del_arc \<lparr>verts = {a}, arcs = {}, tail = \<lambda>x. a, head = \<lambda>x. a\<rparr> e\<^esub> v \<Longrightarrow> False"
      unfolding some_genesis_def by auto
  qed

typedef 'a BlockDAG = "{x. simp_blockDAG x \<or> x = empty_graph}::('a,'a \<times> 'a) pre_digraph set"
  morphisms pre_digraph_of_BlockDAG Abs_BlockDAG 
proof
  show "empty_graph \<in> {x. simp_blockDAG x \<or> x = empty_graph}" by simp
qed

declare [[coercion BlockDAG.pre_digraph_of_BlockDAG]]

lemma BD_cases:
  obtains "simp_blockDAG ((A::'a BlockDAG))" 
  | "empty_graph =  (A::'a BlockDAG) "
  using pre_digraph_of_BlockDAG  by fastforce 

setup_lifting BlockDAG.type_definition_BlockDAG 
context begin

qualified definition abs_BlockDAG :: "('a,'a \<times> 'a) pre_digraph \<Rightarrow> 'a BlockDAG"
  where "abs_BlockDAG = Abs_BlockDAG o balance_BD"

qualified definition BlockDAG_eq where "BlockDAG_eq = BNF_Def.vimage2p balance_BD balance_BD (=)"

qualified lemma equivp_dlist_eq: "equivp BlockDAG_eq"
  unfolding BlockDAG_eq_def by(rule equivp_vimage2p)(rule identity_equivp)

definition qcr_BlockDAG :: "('a,'a \<times> 'a) pre_digraph \<Rightarrow> 'a BlockDAG \<Rightarrow> bool" 
  where "qcr_BlockDAG x y \<longleftrightarrow> y = abs_BlockDAG x"

qualified lemma Quotient_dlist_remdups: "Quotient BlockDAG_eq abs_BlockDAG pre_digraph_of_BlockDAG qcr_BlockDAG"
  unfolding Quotient_def BlockDAG_eq_def qcr_BlockDAG_def vimage2p_def abs_BlockDAG_def
proof (auto simp add: fun_eq_iff Abs_BlockDAG_inject
    pre_digraph_of_BlockDAG[simplified] pre_digraph_of_BlockDAG_inverse)
  fix a ::"'a  BlockDAG" 
  assume "\<not> simp_blockDAG (pre_digraph_of_BlockDAG a)"
  thus "Abs_BlockDAG empty_graph = a"
    by (metis BD_cases pre_digraph_of_BlockDAG_inverse)
qed
    
end
lift_definition past_nodes :: " ('a) BlockDAG  \<Rightarrow> 'a \<Rightarrow> 'a set"
is "DAGs.past_nodes" .

lift_definition reduce_past :: " ('a) BlockDAG  \<Rightarrow> 'a \<Rightarrow> ('a) BlockDAG"
is "reduce_past_empty" 
  unfolding reduce_past_empty_def balance_BD.simps by auto

lemma (in simp_blockDAG) simp_blockDAG_reduce_sound:
  assumes "\<not> is_genesis_node a"
  and "a \<in> verts G"
shows "simp_blockDAG (DAGs.reduce_past G a)"
  unfolding simp_blockDAG_def simp_blockDAG_axioms_def simp_pre_digraph_def
proof safe 
  show "blockDAG (DAGs.reduce_past G a)" using assms reduce_past_dagbased  by auto
  show  "tail (DAGs.reduce_past G a) = fst" 
    unfolding DAGs.reduce_past.simps using tail_fst induce_subgraph_tail by auto
  show  "head (DAGs.reduce_past G a) = snd" 
    unfolding DAGs.reduce_past.simps using head_snd induce_subgraph_head by auto
qed

lemma (in simp_blockDAG) reduce_lifted_sound:
  assumes "a \<in> verts G"
  and "\<not> is_genesis_node a"
  shows "reduce_past_empty G a = DAGs.reduce_past G a"
  unfolding reduce_past_empty_def balance_BD.simps 
  using assms simp_blockDAG_reduce_sound by auto
 
  

lift_definition  vote_Spectre_typed  :: "('a::linorder) BlockDAG  \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> int"
is "Spectre.vote_Spectre".

lift_definition empty_graph_typed :: "('a) BlockDAG"
is "blockDAG_Type.empty_graph" by simp

lemma vote_Spectre_typed_eq: "vote_Spectre_typed G a b c = vote_Spectre G a b c"
  by (simp add: vote_Spectre_typed.rep_eq)  


lemma empty_no_bD: "\<not> blockDAG empty_graph_typed" 
  unfolding empty_graph_typed_def empty_graph_def
  by (metis blockDAG.genesis_in_verts empty_graph_def
 empty_graph_typed.abs_eq empty_graph_typed.rep_eq empty_iff pre_digraph.select_convs(1))

lemma  empty_no_sbD: "\<not> simp_blockDAG empty_graph_typed" 
  unfolding simp_blockDAG_def simp_blockDAG_axioms_def using empty_no_bD by auto

lemma BD_head: 
  fixes G:: "'a BlockDAG"
  shows "head G = snd"
  by (metis BD_cases simp_blockDAG.axioms(1) simp_pre_digraph.head_snd simp_pre_digraph_axioms)
  
lemma BD_tail: 
  fixes G:: "'a BlockDAG"
  shows "tail G = fst"
  by (metis BD_cases simp_blockDAG.axioms(1) simp_pre_digraph.tail_fst simp_pre_digraph_axioms)

lemma blockDAG_simp:
  fixes G:: "'a BlockDAG"
  shows "blockDAG G \<longleftrightarrow> simp_blockDAG G"
  unfolding simp_blockDAG_def simp_blockDAG_axioms_def simp_pre_digraph_def
  using BD_head BD_tail by auto

lemma empty_eq_nbD: 
  "G = empty_graph_typed \<longleftrightarrow> \<not> blockDAG G"
  using blockDAG_simp empty_no_sbD BD_cases pre_digraph_of_BlockDAG_inject
  by metis 
  

lemma vote_Spectre_typed_code [code] : "vote_Spectre_typed G a b c = (
  if (G = empty_graph_typed \<or> a \<notin> verts  G \<or> b \<notin> verts G \<or> c \<notin> verts G)
 then 0 else 
  if (b=c)  then 1 else 
  if (((a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) \<or> a = b) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c)) then 1  else
  if (((a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c) \<or> a = c) \<and> \<not>(a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b)) then -1 else
  if ((a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b) \<and> (a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> c)) then 
   (tie_break_int b c (signum (sum_list (map (\<lambda>i.
 (vote_Spectre_typed (reduce_past G a) i b c)) (sorted_list_of_set (past_nodes G a))))))
 else 
   signum (sum_list (map (\<lambda>i.
   (vote_Spectre_typed G i b c)) (sorted_list_of_set (future_nodes G a)))))" 
proof(induct "pre_digraph_of_BlockDAG G" a b c rule: vote_Spectre.induct)
  case (1 a b c)
  then show ?case 
proof(cases a b c "pre_digraph_of_BlockDAG G" rule: Spectre_casesAlt)
  case no_bD
  then show ?thesis
    unfolding vote_Spectre_typed_eq empty_eq_nbD
    by fastforce 
next
case equal
  then show ?thesis unfolding vote_Spectre_typed_eq empty_eq_nbD by simp
next
  case one
  then show ?thesis  unfolding vote_Spectre_typed_eq empty_eq_nbD
    by simp 
next
  case two
  then show ?thesis unfolding vote_Spectre_typed_eq empty_eq_nbD
    by auto
next
  case three
  then interpret bD: blockDAG "(pre_digraph_of_BlockDAG G)" by auto
  have "\<not> blockDAG.is_genesis_node (pre_digraph_of_BlockDAG G) a" 
    using bD.genesis_reaches_nothing three by auto
  then have rrr: "reduce_past_empty (pre_digraph_of_BlockDAG G) a
   = DAGs.reduce_past (pre_digraph_of_BlockDAG G) a" using three 
    by (simp add: simp_blockDAG.reduce_lifted_sound blockDAG_simp) 
  show ?thesis unfolding vote_Spectre_typed_eq empty_eq_nbD reduce_past.rep_eq rrr
  past_nodes.rep_eq
      using  three
      by simp        
next
  case four
  show ?thesis unfolding vote_Spectre_typed_eq empty_eq_nbD 
    by (simp add: 1 four vote_Spectre.elims) 
qed
qed



instantiation BlockDAG :: (type) equal 
begin
definition  equal_BlockDAG ::"'a BlockDAG \<Rightarrow> 'a BlockDAG \<Rightarrow> bool" 
  where " equal_BlockDAG B1 B2 = (
 (verts B1 =  verts B2) \<and>  (arcs B1 =   arcs B2))
 "

instance proof
  fix x y ::"'a BlockDAG"
  show "equal_class.equal x y = (x = y)" unfolding equal_BlockDAG_def 
    using pre_digraph_of_BlockDAG_inject BD_head BD_tail
    by (metis (full_types) old.unit.exhaust pre_digraph.equality)  
qed



end

declare equal_BlockDAG_def [code]
declare simp_pre_digraph_def [code]
declare simp_blockDAG_axioms_def [code]
declare simp_blockDAG_def [code]

lift_definition vote_Spectre_typed_FV ::
 "FV BlockDAG \<Rightarrow> FV \<Rightarrow> FV \<Rightarrow> FV \<Rightarrow> integer"
  is "(\<lambda>G a b c. integer_of_int (vote_Spectre_typed G a b c))".

export_code  top_sort anticone set blockDAG pre_digraph_ext snd fst vote_Spectre_Int
 SpectreOrder_Int OrderDAG_Int vote_Spectre_typed_FV  in Haskell module_name BD
file "code/"
end