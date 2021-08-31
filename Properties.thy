theory Properties
  imports blockDAG Extend_blockDAG Spectre Ghostdag
begin

definition Linear_Order:: "(('a,'b) pre_digraph \<Rightarrow> 'a rel) \<Rightarrow> bool"
  where "Linear_Order A \<equiv> (\<forall>G. blockDAG G  \<longrightarrow> linear_order_on (verts G) (A G))"


definition Order_Preserving:: "(('a,'b) pre_digraph \<Rightarrow> 'a rel) \<Rightarrow> bool "
  where "Order_Preserving A \<equiv> (\<forall>G a b. blockDAG G \<longrightarrow> a \<rightarrow>\<^sup>+\<^bsub>G\<^esub> b \<longrightarrow> (b,a) \<in> (A G))"


definition One_Appending_Monotone:: "(('a,'b) pre_digraph \<Rightarrow> 'a rel) \<Rightarrow> bool "
  where "One_Appending_Monotone A \<equiv>
         (\<forall>G G_A a b c. Honest_Append_One G G_A a \<longrightarrow> ((b,c) \<in> (A G) \<longrightarrow> (b,c) \<in> (A G_A)))"


definition One_Appending_Robust:: "(('a,'b) pre_digraph \<Rightarrow> 'a rel) \<Rightarrow> bool "
  where "One_Appending_Robust A \<equiv>
         (\<forall>G G_A G_AB a b c d. Append_One_Honest_Dishonest G G_A a G_AB b
          \<longrightarrow> ((c,d) \<in> (A G) \<longrightarrow> (c,d) \<in> (A G_AB)))"




end