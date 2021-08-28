theory Spectre_Properties
  imports Spectre ExtendblockDAG Properties
begin


section \<open>SPECTRE properties\<close>

subsection \<open>SPECTRE Order Preserving\<close>

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


lemma SPECTRE_Preserving:
  assumes "blockDAG G"
    and "b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a"
  shows "(a,b) \<in> (SPECTRE G)"   
  unfolding SPECTRE_def
  using assms  wf_digraph.reachable1_in_verts subs
    Spectre_Order_Preserving
    SigmaI case_prodI mem_Collect_eq by fastforce 


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

lemma SPECTRE_total:
  assumes "blockDAG G"
  shows "total_on (verts G) (SPECTRE G)"
  unfolding total_on_def SPECTRE_def 
  using Spectre_Order_total assms
  by fastforce 

lemma SPECTRE_reflexive:
  assumes "blockDAG G"
  shows "refl_on (verts G) (SPECTRE G)" 
  unfolding refl_on_def SPECTRE_def 
  using Spectre_Order_reflexive assms by fastforce

lemma SPECTRE_antisym:
  assumes "blockDAG G"
  shows "antisym (SPECTRE G)" 
  unfolding antisym_def SPECTRE_def 
  using Spectre_Order_antisym assms by fastforce

lemma SPECTRE_not_trans:
  shows "\<exists>G. blockDAG G \<and> \<not> trans (SPECTRE G)" 
  unfolding trans_def SPECTRE_def 
proof 
  let ?G = "\<lparr>verts = {1::int,2,3,4,5,6,7,8,9,10}, arcs = {(2,1),(3,1),(4,1),
  (5,2),(6,3),(7,4),(8,5),(8,3),(9,6),(9,4),(10,7),(10,2)}, tail = fst, head = snd\<rparr>"
  let ?a = "2"
  let ?b = "3"
  let ?c = "4"
  have vert_G: "verts ?G = {1,2,3,4,5,6,7,8,9,10}" by simp
  have tail_G: "tail ?G = fst" by simp
  have head_G: "head ?G = snd" by simp
  have arc_G: "\<And>e. arc_to_ends ?G e = e" unfolding arc_to_ends_def by simp
  then have arcs_G: "arcs_ends ?G = {(2,1),(3,1),(4,1),
  (5,2),(6,3),(7,4),(8,5),(8,3),(9,6),(9,4),(10,7),(10,2)}" unfolding arcs_ends_def by simp
  have wf_G: "wf_digraph ?G" unfolding wf_digraph_def 
  proof(safe, auto) qed
  then have "fin_digraph ?G" unfolding fin_digraph_def fin_digraph_axioms_def
    by simp
  moreover have "loopfree_digraph ?G" unfolding loopfree_digraph_def loopfree_digraph_axioms_def
    using wf_G by simp
  moreover have " nomulti_digraph ?G" unfolding nomulti_digraph_def nomulti_digraph_axioms_def
    arc_to_ends_def using wf_G by simp
  ultimately have d_G: "digraph ?G" unfolding digraph_def by simp
  obtain E where E_in: "E = {(2::int,1::int),(3,1),(4,1),
  (5,2),(6,3),(7,4),(8,5),(8,3),(9,6),(9,4),(10,7),(10,2)}" by simp
  have dag_G: "DAG ?G" unfolding DAG_def DAG_axioms_def arcs_G     
  proof (safe, rule d_G)
    fix v::int
    have le: "\<forall> a b. (a,b) \<in> E \<longrightarrow> b < a" unfolding E_in by simp
    have "acyclic (E\<^sup>+)"
    proof(rule acyclicI_order)
      let ?f = id
      fix a b ::int
      assume "(a,b) \<in> (E\<^sup>+)"
      then show "?f a > ?f b" unfolding id_def 
      proof(induct  rule: trancl_induct )
      case (base y)
      then show ?case unfolding E_in proof(cases, auto) qed
      next
        case (step y z)
        then have "z < y" using le by simp
      then show ?case using step(3) by simp
    qed
  qed
  then have "\<forall> x. (x,x) \<notin> E\<^sup>+ "
    unfolding acyclic_def by simp
  then show "(v, v)
         \<in> {(2, 1), (3, 1), (4, 1), (5, 2), (6, 3), (7, 4), (8, 5), (8, 3), (9, 6), (9, 4), (10, 7),
             (10, 2)}\<^sup>+ \<Longrightarrow>
         False" unfolding E_in by auto
qed
  have E_c: "(card E - 1) = 11" unfolding E_in by simp 
  have sss: "{i. 0 < i \<and> i \<le> Suc 11} = {1,2,3,4,5,6,7,8,9,10,11,12}" 
  proof(standard, simp_all, standard)
    fix x::nat
    assume x_in: "x \<in>  {i. 0 < i \<and> i \<le> 12}"
    then have "0 < x \<and> x < 13" by auto
    then have "x \<in> {1,2,3,4,5,6,7,8,9} \<or> 9 < x \<and> x < 13" by auto
    then have "x \<in> {1,2,3,4,5,6,7,8,9,10,11,12} \<or> 13 < x \<and> x < 13" by auto
    then have "x \<in> {1,2,3,4,5,6,7,8,9,10,11,12}" by auto
    then show "x \<in> {Suc 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}"
      using x_in by auto
  qed
  have "finite E" using E_in by simp
  moreover have 
    "ntrancl 11 E = {(2::int, 1), (3, 1), (4, 1), (5, 2), (6, 3), (7, 4), (8, 5), (8, 3), (9, 6), (9, 4), (10, 7),
             (10, 2), (5,1),(6,1),(7,1),(8,2),(9,3),(10,4),(10,1),(8,1),(9,1)}" 
    unfolding E_in unfolding ntrancl_def sss image_def sorry
    using  funpow_code_def 
  have " E \<union> {(5,1),(6,1),(7,1),(8,2),(9,3),(10,4)} \<subseteq>  E\<^sup>+"
    unfolding E_in by (simp add: r_into_trancl', auto)
      (induct rule:  trancl_into_trancl , auto)+ 
  then have  tr_ex: "E \<union> {(5,1),(6,1),(7,1),(8,2),(9,3),(10,4)} \<union> {(10,1),(8,1),(9,1)} \<subseteq>  E\<^sup>+"  
  unfolding E_in by (simp add: r_into_trancl', auto) 
  have "blockDAG ?G"  
    unfolding blockDAG_def blockDAG_axioms_def
  proof(safe, rule dag_G)
    show "\<exists>p\<in>verts ?G. \<forall>r. r \<in> verts ?G \<longrightarrow> r \<rightarrow>\<^sup>+\<^bsub>?G\<^esub> p \<or> r = p"
    proof
      let ?p = 1 
      show "?p \<in> verts ?G" by simp
      show "\<forall>r. r \<in> verts ?G \<longrightarrow> r \<rightarrow>\<^sup>+\<^bsub>?G\<^esub> ?p \<or> r = ?p"
      proof(safe)
        fix r
        assume "r \<in> verts ?G"
        and "r \<noteq> 1"
        then have r_in: "r \<in> {2,3,4,5,6,7,8,9,10}"
          by simp
        then consider 
           "r = 2" | "r = 3" | "r = 4" | "r = 5" | "r = 6" | "r = 7" | "r = 8" | "r = 9" | "r = 10"
          by auto
        then show "(r,1) \<in> (arcs_ends ?G)^+" 
          using  tr_ex 
          unfolding E_in arcs_G proof(cases, auto) qed
      qed
    qed
  next
    fix u v a b 
  have "blockDAG ?G" sorry*)
    
  have "Spectre_Order ?G ?a ?b \<and> Spectre_Order ?G ?b ?c \<and> \<not> Spectre_Order ?G ?a ?c" sorry
  oops

end 