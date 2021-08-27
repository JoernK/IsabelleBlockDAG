theory Properties
  imports blockDAG ExtendblockDAG
begin

definition Linear_Order:: "(('a,'b) pre_digraph \<Rightarrow> 'a rel) \<Rightarrow> bool"
  where "Linear_Order A \<equiv> (\<forall>G. blockDAG G  \<longrightarrow> linear_order_on (verts G) (A G))"


definition Order_Preserving:: "(('a,'b) pre_digraph \<Rightarrow> 'a rel) \<Rightarrow> bool "
  where "Order_Preserving A \<equiv> (\<forall>G a b. blockDAG G \<longrightarrow> a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b \<longrightarrow> (b,a) \<in> (A G))"




definition One_Appending_Monotone:: "(('a,'b) pre_digraph \<Rightarrow> 'a rel) \<Rightarrow> bool "
  where "One_Appending_Monotone A \<equiv>
         (\<forall>G G' a b c. Honest_Append_One G G' a \<longrightarrow> ((b,c) \<in> (A G) \<longleftrightarrow> (b,c) \<in> (A G')))"


definition One_Appending_Robust:: "(('a,'b) pre_digraph \<Rightarrow> 'a rel) \<Rightarrow> bool "
  where "One_Appending_Robust A \<equiv>
         (\<forall>G G' G'' a b c d. Append_One_Honest_Dishonest G G' a G'' b
          \<longrightarrow> ((c,d) \<in> (A G) \<longleftrightarrow> (c,d) \<in> (A G'')))"


end