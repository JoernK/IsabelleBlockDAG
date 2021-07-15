module Test where
import Spectre



v = Set [12,22,3,40,50,6]
e = Set [(22,12),(3,12),(40,22),(40,3),(50,40),(6,12)]

tl = fst

hd = snd

g = Pre_digraph_ext v e tl hd ()



