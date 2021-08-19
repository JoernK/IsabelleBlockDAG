theory TopSort
  imports DAGs Utils
begin


text \<open>Function to sort a list $L$ under a graph G such if $a$ references $b$,
$b$ precedes $a$ in the list\<close>

fun top_insert:: "('a::linorder,'b) pre_digraph \<Rightarrow>'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "top_insert G [] a = [a]"
  | "top_insert G (b # L) a = (if (b \<rightarrow>\<^sup>+\<^bsub>G\<^esub> a) then  (a # ( b # L)) else (b # top_insert G L a))"

fun top_sort:: "('a::linorder,'b) pre_digraph \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "top_sort G []= [] "
  | "top_sort G (a # L) = top_insert G (top_sort G L) a"

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

lemma top_sort_len: "length (top_sort G L) = length L"
proof(induct L, simp)
  case (Cons a L)
  then have "length (a#L) = Suc (length L)" by auto
  then show ?case using
      top_insert_len top_sort.simps(2) Cons
    by (simp add: top_insert_len)  
qed

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

lemma top_sort_mono:
  assumes "(y, x) \<in> list_to_rel (top_sort G ls)"
  shows "(y, x) \<in> list_to_rel (top_sort G (l # ls))"
  using assms 
  by (simp add: top_insert_mono) 



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

end