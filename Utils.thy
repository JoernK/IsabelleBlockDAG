
theory Utils
  imports Main
begin


text \<open>The following functions transform a list L to a relation containing a  tuple $(a,b)$
  iff $a = b$ or $a$ precedes $b$ in the list L \<close>

fun list_to_rel:: "'a list \<Rightarrow> 'a rel"
  where "list_to_rel [] = {}"
  | "list_to_rel (x#xs) = {x} \<times> (set (x#xs)) \<union> list_to_rel xs"


lemma list_to_rel_empty : " list_to_rel L = {} \<Longrightarrow> L = []" 
proof(induct L, auto) qed

lemma list_to_rel_in : " (a,b)  \<in> (list_to_rel L) \<Longrightarrow> a \<in> set L \<and> b \<in> set L" 
proof(induct L, auto) qed



lemma list_to_rel_reflexive : "a \<in> set L \<Longrightarrow> (a,a)  \<in> (list_to_rel L)" 
proof(induct L, auto) qed

text \<open>Show soundness of list-to-rel\<close>
lemma list_to_rel_equal: 
  "(a,b) \<in> list_to_rel L \<longleftrightarrow> (\<exists>k::nat. hd (drop k L) = a \<and> b \<in> set (drop k L))"
proof(safe)
  assume "(a, b) \<in> list_to_rel L"
  then show "\<exists>k. hd (drop k L) = a \<and> b \<in> set  (drop k L)"
  proof(induct L)
    case Nil
    then show ?case by auto
  next
    case (Cons a2 L)
    then consider "(a, b) \<in> {a2} \<times> set (a2 # L) " | "(a,b) \<in>  list_to_rel L" by auto
    then show ?case unfolding list_to_rel.simps(2)  
    proof(cases)
      case 1
      then have "a = hd (a2 # L)" by auto
      moreover have "b \<in> set (a2 # L)" using 1 by auto
      ultimately show ?thesis using drop0
        by metis 
    next
      case 2
      then obtain k where k_in : "hd (drop k (L)) = a \<and> b \<in> set (drop k (L))" 
        using Cons(1) by auto
      show ?thesis proof
        let ?k = "Suc k"
        show "hd (drop ?k (a2 # L)) = a \<and> b \<in> set (drop ?k (a2 # L))"
          unfolding drop_Suc using k_in by auto 
      qed
    qed
  qed
next
  fix k 
  assume "b \<in> set (drop k L)"
    and "a = hd (drop k L)"
  then show "(hd (drop k L), b) \<in> list_to_rel L"
  proof(induct L arbitrary: k)
    case Nil
    then show ?case by auto
  next
    case (Cons a L)
    consider (zero) "k = 0" | (more) "k > 0" by auto    
    then show ?case 
    proof(cases)
      case zero
      then show ?thesis using Cons drop_0 by auto
    next
      case more
      then obtain k2 where k2_in:  "k = Suc k2"
        using gr0_implies_Suc by auto 
      show ?thesis using Cons unfolding k2_in drop_Suc list_to_rel.simps(2) by auto
    qed
  qed
qed

lemma list_to_rel_append:
  assumes "a \<in> set L"
  shows "(a,b) \<in> list_to_rel (L @ [b])" 
  using assms
proof(induct L, simp, auto) qed 

text \<open>For every distinct L, list-to-rel L return a linear order on set L\<close>
lemma list_order_linear:
  assumes "distinct L"
  shows "linear_order_on (set L)  (list_to_rel L)" 
  unfolding linear_order_on_def total_on_def partial_order_on_def preorder_on_def refl_on_def
    trans_def antisym_def 
proof(safe)
  fix a b
  assume "(a, b) \<in> list_to_rel L"
  then show "a \<in> set L" 
  proof(induct L, auto) qed
next 
  fix a b
  assume "(a, b) \<in> list_to_rel L"
  then show "b \<in> set L" 
  proof(induct L, auto) qed
next 
  fix x 
  assume "x \<in> set L"
  then show "(x, x) \<in> list_to_rel L"
  proof(induct L, auto) qed
next
  fix x y z 
  assume as1: "(x,y) \<in> list_to_rel L"
    and  as2: "(y, z) \<in> list_to_rel L"
  then show "(x, z) \<in> list_to_rel L"
    using assms
  proof(induct L)
    case Nil
    then show ?case by auto
  next
    case (Cons a L)
    then consider (nor) "(x, y) \<in> {a} \<times> set (a # L) \<and> (y, z) \<in> {a} \<times> set (a # L)" 
      | (xy) "(x,y) \<in> list_to_rel L \<and> (y, z) \<in> {a} \<times> set (a # L)" 
      | (yz) "(y,z) \<in> list_to_rel L \<and> (x, y) \<in> {a} \<times> set (a # L)"
      | (both) "(y,z) \<in> list_to_rel L \<and> (x,y) \<in> list_to_rel L" by auto
    then show ?case proof(cases)
      case nor
      then show ?thesis by auto
    next
      case xy 
      then have "y \<in> set L" using list_to_rel_in by metis
      also have "y = a" using xy by auto
      ultimately have "\<not> distinct (a # L)"
        by simp 
      then show ?thesis using Cons by auto
    next
      case yz
      then show ?thesis using list_to_rel.simps(2)
        by (metis Cons.prems(2) SigmaD1 SigmaI UnI1 list_to_rel_in)  
    next
      case both
      then show ?thesis unfolding list_to_rel.simps(2) using Cons by auto
    qed
  qed 
next
  fix x y 
  assume "(x, y) \<in> list_to_rel L"
    and "(y, x) \<in> list_to_rel L"
  then show "x = y"
    using assms
  proof(induct L, simp)
    case (Cons a L)
    then consider (nor) "(x, y) \<in> {a} \<times> set (a # L) \<and> (y, x) \<in> {a} \<times> set (a # L)" 
      | (xy) "(x,y) \<in> list_to_rel L \<and> (y, x) \<in> {a} \<times> set (a # L)" 
      | (yz) "(y,x) \<in> list_to_rel L \<and> (x, y) \<in> {a} \<times> set (a # L)"
      | (both) "(y,x) \<in> list_to_rel L \<and> (x,y) \<in> list_to_rel L" by auto
    then show ?case unfolding list_to_rel.simps 
    proof(cases)
      case nor
      then show ?thesis by auto
    next
      case xy
      then show ?thesis
        by (metis Cons.prems(3) SigmaD1 distinct.simps(2) list_to_rel_in singletonD) 
    next
      case yz
      then show ?thesis  
        by (metis Cons.prems(3) SigmaD1 distinct.simps(2) list_to_rel_in singletonD) 
    next
      case both
      then show ?thesis using Cons by auto 
    qed
  qed
next
  fix x y 
  assume "x \<in> set L"
    and "y \<in> set L"
    and "x \<noteq> y"
    and "(y, x) \<notin> list_to_rel L"
  then show "(x, y) \<in> list_to_rel L"
  proof(induct L, auto) qed    
qed


lemma list_to_rel_mono:
  assumes "(a,b) \<in> list_to_rel (L)"
  shows "(a,b) \<in> list_to_rel (L @ L2)"
  using assms
proof(induct L2 arbitrary: L, simp)
  case (Cons a L2)
  then show ?case 
  proof(induct L, auto)
  qed
qed

lemma list_to_rel_mono3:
  assumes "(a,b) \<in> list_to_rel (L)"
  shows  "(a,b) \<in> list_to_rel (c # L)"
  using assms unfolding list_to_rel.simps by auto


lemma list_to_rel_mono4:
  assumes "(a,b) \<in> list_to_rel (L)"
    and "set L2 = set L"
  shows  "(a,b) \<in> list_to_rel (a # L2)"
proof -
  have "b \<in> set (a # L2)"
    by (metis assms(1) assms(2) list.set_intros(2) list_to_rel_in)  
  then show ?thesis by auto
qed

lemma list_to_rel_cases:
  assumes "(a,b) \<in> list_to_rel (c # L)"
  shows "(a,b) \<in> list_to_rel (L) \<or> a = c"
  using assms unfolding list_to_rel.simps by auto

lemma list_to_rel_elim:
  assumes "(a,b) \<in> list_to_rel (c # L)"
    and "a \<noteq> c"
  shows "(a,b) \<in> list_to_rel (L)"
  using assms unfolding list_to_rel.simps by auto

lemma list_to_rel_elim2:
  assumes "(a,b) \<notin> list_to_rel (L)"
    and "a \<noteq> c"
  shows "(a,b) \<notin> list_to_rel (c # L)"
  using assms unfolding list_to_rel.simps by auto

lemma list_to_rel_equiv:
  assumes "a \<in> set L"
    and "b \<in> set L"
  obtains "(a,b) \<in>  list_to_rel (L)" | "(b,a) \<in>  list_to_rel (L)"
  using assms
proof(induct L, auto) qed

lemma list_to_rel_mono2:
  assumes "(a,b) \<in> list_to_rel (L2)"
  shows "(a,b) \<in> list_to_rel (L @ L2)"
  using assms
proof(induct L2 arbitrary: L, simp)
  case (Cons a L2)
  then show ?case 
  proof(induct L, auto)
  qed
qed


lemma map_snd_map: "\<And>L. (map snd (map (\<lambda>i. (P i , i)) L)) =  L" 
proof -
  fix L
  show "map snd (map (\<lambda>i. (P i, i)) L) = L"
  proof(induct L)
    case Nil
    then show ?case by auto
  next
    case (Cons a L)
    then show ?case by auto
  qed
qed
end