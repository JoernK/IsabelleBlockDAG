module Test where
import Spectre



v = Set [1,2,3,4,5,6]
e = Set [(2,1),(3,1),(4,2),(4,3),(5,4),(6,1)]

tl = fst

hd = snd

g = Pre_digraph_ext v e tl hd ()



