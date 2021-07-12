
theory Ghostdag  
  imports blockDAG Spectre
begin

function OrderDAG :: "('a::linorder,'b) pre_digraph \<Rightarrow> int \<Rightarrow> ('a list \<times> 'a list)" 
  where
  "OrderDAG G k =  
  (if (\<not> blockDAG G) then ([],[]) else 
  if (card (verts G) = 1)  then ([blockDAG.genesis_node G],[blockDAG.genesis_node G]) else
   ([],[]))"
  using blockDAG.unique_genesis by auto





end