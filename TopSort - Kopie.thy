theory TopSort
  imports DAGs Utils "HOL-Library.Comparator"
begin


text \<open>Function to sort a list $L$ under a graph G such if $a$ references $b$,
$b$ precedes $a$ in the list\<close>


fun top_insert:: "('a::linorder,'b) pre_digraph \<Rightarrow>'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "top_insert G [] a = [a]"
  | "top_insert G (b # L) a = (if (b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) then  (a # ( b # L)) else (b # top_insert G L a))"

fun top_sort:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "top_sort G []= [] "
  | "top_sort G (a # L) =  top_insert G (top_sort G L) a"

subsubsection \<open>Soundness of the topological sort algorithm\<close>
lemma top_insert_set: "set (top_insert G L a) = set L \<union> {a}" 
proof(induct L, simp_all, auto) qed 


lemma top_sort_con: "set (top_sort G L) = set L"
proof(induct L)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case using top_sort.simps(2) top_insert_set insert_is_Un list.simps(15) sup_commute
    by (metis) 
qed


lemma top_insert_len: "length (top_insert G L a) = Suc (length L)"
proof(induct L)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case using top_insert.simps(2) by auto
qed

lemma top_insert_not_nil: "top_insert G L a \<noteq> []"
proof(induct L, auto) qed


lemma top_sort_len: "length (top_sort G L) = length L"
proof(induct L, simp)
  case (Cons a L)
  then have "length (a#L) = Suc (length L)" by auto
  then show ?case using
      top_insert_len top_sort.simps(2) Cons
    by (simp add: top_insert_len)  
qed


lemma top_sort_nil: "top_sort G L = [] \<longleftrightarrow> L = []" 
proof(auto, induct L, auto simp: top_insert_not_nil) qed

lemma top_insert_mono:
  assumes "(y, x) \<in> list_to_rel ls"
  shows "(y, x) \<in> list_to_rel (top_insert G ls l)"
  using assms 
proof(induct ls, simp)
  case (Cons a ls)
  consider (rec) "a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> l" | (nrec) "\<not> a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> l" by auto
  then show ?case 
  proof(cases)
    case rec
    then have sinse: "(top_insert G (a # ls) l)  = l # a # ls"
      unfolding top_insert.simps by simp
    show ?thesis unfolding sinse list_to_rel.simps  using Cons
      by auto
  next
    case nrec
    then have sinse: "(top_insert G (a # ls) l)  = a # top_insert G ls l"
      unfolding top_insert.simps by simp
    consider (ya) "y = a" | (yan) "(y, x) \<in> list_to_rel ls" using Cons by auto
    then show ?thesis proof(cases)
      case ya
      then show ?thesis unfolding sinse list_to_rel.simps
        by (metis Cons.prems SigmaI UnI1 top_insert_set insertCI list_to_rel_in sinse) 
    next
      case yan
      then show ?thesis using Cons unfolding sinse list_to_rel.simps by auto 
    qed
  qed
qed

lemma top_insert_cases:
  assumes "(y, x) \<in> list_to_rel (top_insert G ls l)"
  shows  "(y, x) \<in> list_to_rel ls \<or> x = l \<or> y = l" 
  using assms 
proof(induct "(top_insert G ls l)" arbitrary: ls l, simp)
  case (Cons a ls2)
  consider "a # ls2 = l # ls" |  "a # ls2 = (hd ls) # top_insert G (tl ls) l" 
    using Cons(2) top_insert.simps
    by (metis list.sel(1) list.sel(3) top_insert.elims) 
  then show ?case proof(cases)
    case 1
    then show ?thesis unfolding Cons(2) using Cons(3) list_to_rel_cases
      by auto
  next
    case 2
    then consider (ay) "a = y" |  (bb) "(y, x) \<in> list_to_rel ls2" 
      using list_to_rel_elim Cons(2,3)
      by metis 
    then show ?thesis proof(cases)
      case ay
      then have "y = hd ls" using 2 by auto
      moreover have "x \<in> set (a # ls2)" using list_to_rel_in Cons
        by metis 
      then show ?thesis  using  Cons
        by (metis (no_types, lifting) "2" SigmaI UnI1 Un_iff ay calculation 
    empty_iff empty_set list.inject list.sel(1) list.sel(2) list.set_intros(1) 
    list.simps(15) list_to_rel.elims not_Cons_self2 set_ConsD  top_insert_set) 
    next
      case bb
      then have "(y, x) \<in> list_to_rel (top_insert G (tl ls) l)"
        using 2 by auto
      then have "(y, x) \<in> list_to_rel (tl ls) \<or> x = l \<or> y = l"
        using Cons 2
        by blast 
      then show ?thesis using list_to_rel_mono3 hd_Cons_tl list.sel(2)
        by (metis) 
    qed  
  qed
qed


lemma top_insert_elims:
  assumes "(y, x) \<notin> list_to_rel ls"
  and "x \<noteq> l"
  and "y \<noteq> l"
  shows "(y, x) \<notin> list_to_rel (top_insert G ls l)"
  using assms top_insert_cases by metis

lemma top_sort_mono:
  assumes "(y, x) \<in> list_to_rel (top_sort G ls)"
  shows "(y, x) \<in> list_to_rel (top_sort G (l # ls))"
  using assms 
  by (simp add: top_insert_mono) 



lemma top_sort_mono2:
 "list_to_rel (top_sort G ls) \<subseteq>  list_to_rel (top_sort G (l # ls))"
  using top_sort_mono
  by (metis subrelI)

lemma top_sort_one:
  assumes "top_sort G L = [l]"
  shows "L = [l]"
proof -
  have l_in: "l \<in> set L" using assms(1) top_sort_con
    by (metis list.set_intros(1))   
  have ll: "length L = length (top_sort G L) " using top_sort_len by metis
  have "length L = 1" unfolding ll using assms by auto 
  then show "L = [l]"  using l_in
    by (metis append_butlast_last_id diff_is_0_eq'
        le_numeral_extra(4) length_0_conv length_butlast
        length_pos_if_in_set less_numeral_extra(3) self_append_conv2 set_ConsD) 
qed

lemma top_sort_cases:
  assumes "(y, x) \<in> list_to_rel (top_sort G (l # ls))"
  shows "(y, x) \<in> list_to_rel (top_sort G ls) \<or> y = l \<or> x = l" 
  using assms
proof(induct ls arbitrary: l, simp)
  case (Cons a ls)
  then show ?case 
    unfolding top_sort.simps using top_insert_cases 
    by metis 
qed

fun (in DAG) top_sorted :: "'a list \<Rightarrow> bool" where
  "top_sorted [] = True" |
  "top_sorted (x # ys) = ((\<forall>y \<in> set ys. \<not> x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y) \<and> top_sorted ys)"

lemma (in DAG) top_sorted_sub:
  assumes "S = drop k L"
    and "top_sorted L"  
  shows "top_sorted S"
  using assms
proof(induct k arbitrary: L S)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case unfolding drop_Suc using top_sorted.simps
    by (metis Suc.prems(1) drop_Nil list.sel(3) top_sorted.elims(2)) 
qed


lemma top_insert_part_ord:
  assumes "DAG G"
    and "DAG.top_sorted G L"
  shows "DAG.top_sorted G (top_insert G L a)" 
  using assms 
proof(induct L)
  case Nil
  then show ?case  
    by (simp add: DAG.top_sorted.simps)  
next
  case (Cons b list)
  consider (re) "b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a" | (nre) "\<not> b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a " by auto
  then show ?case proof(cases)
    case re
    have "(\<forall>y\<in>set (b # list). \<not> a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y )" 
    proof(rule ccontr)
      assume "\<not> (\<forall>y\<in>set (b # list). \<not> a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y)"
      then obtain wit where wit_in: "wit \<in> set  (b # list) \<and> a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> wit" by auto
      then have "b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> wit" using re
        by auto 
      then have "\<not> DAG.top_sorted G  (b # list)"
        using wit_in using DAG.top_sorted.simps(2) Cons(2)
        by (metis DAG.cycle_free set_ConsD) 
      then show "False" using Cons by auto 
    qed
    then show ?thesis using assms(1) DAG.top_sorted.simps Cons
      by (simp add: DAG.top_sorted.simps(2) re) 
  next
    case nre
    have "DAG.top_sorted G list" using Cons(2,3)
      by (metis DAG.top_sorted.simps(2)) 
    then have "DAG.top_sorted G (top_insert G list a)" 
      using  Cons(1,2) by auto
    moreover have "(\<forall>y\<in>set (top_insert G list a). \<not> b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y )" using top_insert_set 
        Cons DAG.top_sorted.simps(2) nre
      by (metis Un_iff empty_iff empty_set list.simps(15) set_ConsD)  
    ultimately show ?thesis using Cons(2)
      by (simp add: DAG.top_sorted.simps(2) nre)  
  qed 
qed


lemma top_sort_sorted:
  assumes "DAG G"
  shows "DAG.top_sorted G (top_sort G L)" 
  using assms 
proof(induct L)
  case Nil
  then show ?case
    by (simp add: DAG.top_sorted.simps(1)) 
  case (Cons a L)
  then show ?case unfolding top_sort.simps using top_insert_part_ord by auto
qed

lemma top_sorted_rel: 
  assumes "DAG G"
    and "y \<rightarrow>\<^sup>+\<^bsub>G\<^esub> x"
    and "x \<in> set L"
    and "y \<in> set L"
    and "DAG.top_sorted G L"
  shows "(x,y) \<in> list_to_rel L"
  using assms
proof(induct L, simp)
  have une:"x \<noteq> y" using assms
    by (metis DAG.cycle_free) 
  case (Cons a L)
  then consider "x = a \<and> y \<in> set (a # L)" | "y = a \<and> x \<in> set L" | "x \<in> set L \<and> y \<in> set L"
    using une by auto
  then show ?case proof(cases)
    case 1
    then show ?thesis unfolding list_to_rel.simps by auto
  next
    case 2
    then have "\<not> DAG.top_sorted G (a # L)"
      using assms DAG.top_sorted.simps(2)
      by fastforce  
    then show ?thesis using Cons by auto
  next
    case 3
    then show ?thesis unfolding list_to_rel.simps using Cons DAG.top_sorted.simps(2) Un_iff
      by metis  
  qed
qed

lemma top_sort_rel: 
  assumes "DAG G"
    and "y \<rightarrow>\<^sup>+\<^bsub>G\<^esub> x"
    and "x \<in> set L"
    and "y \<in> set L"
  shows "(x,y) \<in> list_to_rel (top_sort G L)"
  using assms top_sort_sorted top_sorted_rel top_sort_con
  by metis  

lemma top_sorted_rel2: 
  assumes "DAG G"
    and "(x,y) \<in> list_to_rel L"
    and "x \<in> set L"
    and "y \<in> set L"
    and "DAG.top_sorted G L"
  shows "\<not> x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y"
proof(rule ccontr)
  assume " \<not> (x, y) \<notin> (arcs_ends G)\<^sup>+"
  then show "False"
    using assms(2,3,4,5)
  proof(induct L, simp)
   interpret D: DAG G using assms(1) by auto
   case (Cons a L)
   then consider "x = a \<and> y = a"
     |"x = a \<and> y \<in> set L" | "y = a \<and> x \<in> set L" | "x \<in> set L \<and> y \<in> set L"
    using Cons by auto
    then show ?case proof(cases)
      case 1
      then show ?thesis using Cons
        using D.cycle_free by blast 
    next
      case 2
      then show ?thesis
        using Cons.prems(1) Cons.prems(5) D.top_sorted.simps(2) by blast 
    next
      case 3
      then show ?thesis
        by (metis Cons.hyps Cons.prems(1) Cons.prems(2)
            Cons.prems(5) D.top_sorted.simps(2) list_to_rel_elim list_to_rel_in) 
    next
      case 4
      then show ?thesis
        using Cons.hyps Cons.prems(1) Cons.prems(2) Cons.prems(5) by auto 
    qed
  qed
qed


lemma top_sort_rel2: 
  assumes "DAG G"
    and "(x,y) \<in> list_to_rel (top_sort G L)"
    and "x \<in> set L"
    and "y \<in> set L"
  shows "\<not> x \<rightarrow>\<^sup>+\<^bsub>G\<^esub> y"
  using assms top_sort_sorted top_sorted_rel2 top_sort_con by metis

lemma top_sort_mono3:
  assumes "DAG G"
  assumes "list_to_rel (top_sort G L) \<subseteq> list_to_rel (top_sort G L2)"
  shows "list_to_rel (top_sort G (s1 # L)) \<subseteq> list_to_rel (top_sort G (s1 # L2))"
  using assms(2) 
proof(induct "top_sort G L" arbitrary: L2 L s1)
  case Nil 
  then have LE: "L = []" 
    using top_sort_nil by metis
  have sin: "s1 \<in> set (top_sort G (s1 # L2))" using top_sort_con 
    by (metis list.set_intros(1)) 
  have TTT: "top_sort G [s1] = [s1]"
    by simp 
  have "(s1,s1) \<in> list_to_rel (top_sort G (s1 # L2))"
    using list_to_rel_reflexive sin by auto
  then show ?case  unfolding TTT LE list_to_rel.simps
    by force 
next
  case (Cons a x)
  then show ?case sorry
qed
  
  
   

lemma insort_add_mono:
  assumes "DAG G"
  and "(x,y) \<in> list_to_rel (L)"
shows "(x,y) \<in> list_to_rel (insort a L)"
proof-
  have " (insort a L) \<noteq> []" using insort_not_Nil by auto
  then show ?thesis 
    using assms(2)
proof(induct "(insort a L)" arbitrary: L a rule: list_nonempty_induct)
  case (single x)
  then show ?case
    by (metis Suc_length_conv length_0_conv length_insort
        list.inject list_to_rel_mono self_append_conv2) 
next
  case (cons x2 xs)
  have lS: "length (insort a L) = length L + 1"
    by auto 
  have "1 \<le> length xs" using cons(1)
    using not_less_eq_eq by auto 
  then have "2 \<le> length (x2 # xs)" by auto
  then have "2 \<le> length (insort a L)" using cons(3) by auto 
  then have "1 \<le> length L" using lS by auto
  then obtain s1 sr where s1_sr_def: "L = s1 # sr"
    by (metis One_nat_def Suc_le_length_iff) 
  then consider "a \<le> s1" | "\<not> a \<le> s1" by auto
  then show ?case proof(cases) 
  case 1
    then have iii: "(insort a L) = a # L" unfolding s1_sr_def by auto 
    show ?thesis using cons(4) unfolding iii by auto
  next
    case 2 
    then have iii: "(insort a L) = s1 # insort a sr" unfolding s1_sr_def
      by simp 
    then have "xs = insort a sr" using cons(3) by auto
    consider (xs1) "x = s1" | (xyr) "(x,y) \<in> list_to_rel ( insort a sr)"
      using list_to_rel_cases cons iii
      unfolding s1_sr_def by auto
    then show ?thesis proof(cases)
      have "y \<in> set L" 
        using list_to_rel_in cons(4)
        by metis 
      then have y_in: "y \<in> set (insort a L)"  unfolding set_insort_key
        by auto 
      case xs1      
      then show ?thesis using y_in unfolding iii xs1 list_to_rel.simps(2)
        by auto 
    next
      case xyr
      then have "(x, y) \<in> list_to_rel (s1 # (insort a sr))"
        by simp 
      then show ?thesis unfolding iii by simp
      qed   
    qed
  qed
qed

lemma list_to_rel_top_sort_subset:
  assumes "DAG G"
  shows "list_to_rel (top_sort G L) \<subseteq> list_to_rel (top_sort G (insort a L))"
proof -
  have "(insort a L) \<noteq> []" using insort_not_Nil 
    by (metis) 
  then show ?thesis 
proof(induction " (insort a L)" arbitrary: L a rule: list_nonempty_induct)
  case (single x)
  have "length [x] = length (insort a L)" unfolding single(1) top_sort_len by simp
  then have "L = []" using set_insort_key by auto
  then show ?case using single by auto
next
  case (cons x2 xs)
  have lS: "length (insort a L) = length L + 1"
    by auto 
  have "1 \<le> length xs" using cons(1)
    using not_less_eq_eq by auto 
  then have "2 \<le> length (x2 # xs)" by auto
  then have "2 \<le> length (insort a L)" using cons(3)
    by (simp add: top_sort_len) 
  then have "1 \<le> length L" using lS by auto
  then obtain s1 sr where s1_sr_def: "L = s1 # sr"
    by (metis One_nat_def Suc_le_length_iff) 
  then consider "a \<le> s1" | "\<not> a \<le> s1" by auto
  then show ?case proof(cases)
    case 1
    then have iii: "(insort a L) = a # L" unfolding s1_sr_def by auto 
    show ?thesis using cons unfolding iii using top_sort_mono by auto
  next
    have lll: "list_to_rel (top_sort G L) = list_to_rel (top_sort G (s1 # sr))"
      using s1_sr_def by auto
    case 2 
    then have bbb: "(insort a L) = s1 # insort a sr" unfolding s1_sr_def
      by simp 
    then have "list_to_rel (top_sort G sr) \<subseteq> list_to_rel (top_sort G (insort a sr))"
      using cons
      by auto 
    then show ?thesis unfolding bbb lll using top_sort_mono3 assms
      by blast 
  qed
 qed
qed



lemma top_sort_add_mono:
  assumes "DAG G"
  and "(x,y) \<in> list_to_rel (top_sort G L)"
shows "(x,y) \<in> list_to_rel (top_sort G (insort a L))"   
  using assms  list_to_rel_top_sort_subset
  by auto 


lemma top_sort_add_mono2:
  assumes "DAG G"
  and "finite S"
  and "(x,y) \<in> list_to_rel (top_sort G (sorted_list_of_set S))"
shows "(x,y) \<in> list_to_rel (top_sort G (sorted_list_of_set (insert a S)))"
proof -
have  "(sorted_list_of_set (insert a S)) =  insort a (sorted_list_of_set (S - {a}))"
  by (simp add: assms(2)) 
  moreover have "distinct (sorted_list_of_set (S - {a}))" by auto
  moreover have "a \<notin> set  (sorted_list_of_set (S - {a}))"
    using assms(2) by auto 
  ultimately show ?thesis using top_sort_add_mono
    by (metis Diff_empty Diff_insert0 assms(1) assms(3) insert_Diff insert_Diff_single) 
qed



lemma top_sort_add_mono3:
  assumes "DAG G"
  and "finite S2"
  and "S \<subseteq> S2"
  and "(x,y) \<in> list_to_rel (top_sort G (sorted_list_of_set S))"
shows "(x,y) \<in> list_to_rel (top_sort G (sorted_list_of_set (S2)))" 
proof -
  have "finite(S2 - S)"
    by (simp add: assms(2))
  then show ?thesis
    using assms(3,4)
  proof(induct "S2 - S" arbitrary: S S2 rule: finite_induct)
    case empty
    then have "S = S2"
      by auto 
    then show ?case using empty
      by auto 
  next
    case (insert x2 F)
    then have fS: "finite S"
      by (metis emptyE list_to_rel.simps(1) sorted_list_of_set.infinite top_sort.simps(1)) 
   have "F = S2 - (insert x2 S)"
      by (metis insert(2,4) Diff_insert Diff_insert_absorb)
   moreover have "(x, y) \<in> list_to_rel (top_sort G (sorted_list_of_set (insert x2 S)))"
      using assms(1) top_sort_add_mono2 insert(6) fS
      by (metis)  
    moreover have "(insert x2 S) \<subseteq> S2" using insert
      by (metis Diff_subset insert_subset) 
    ultimately show ?case
      by (simp add: insert.hyps(3)) 
  qed
qed  

end