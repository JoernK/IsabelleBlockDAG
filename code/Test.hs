module Test where
import DAGS


instance Show a => Show (Set a)  where 
    show (Set l) = "Set " ++ (show l)
    show (Coset l) = "CoSet " ++ (show l)

v = Set [12,22,3,48,40,50,6]
e = Set [(22,12),(3,12),(48,3),(40,22),(40,48),(50,40),(6,12)]

tl = fst

hd = snd

g = Pre_digraph_ext v e tl hd ()


-- gen = 13, B = 2, C = 40, D = 27, E = 30, F = 26, H = 14, I = 29,
-- J = 5, K = 55, L = 60, M = 6, 
v2 = Set [13, 2, 40, 27, 30, 26, 14, 29, 55, 60, 5, 6]
e2 = Set
        [(2,13),(40,13),(27,13),(30,13) --gen
        ,(26,2),(55,2) -- B
        ,(26,40),(14,40) -- C
        ,(14,27),(60,27) -- D
        ,(14,30),(29,30) -- E 
        ,(5,26),(6,26) -- F
        ,(5,14),(55,14) -- H
        ,(55,29),(60,29) -- I
        ,(6,55) --K
        ]

g2 = Pre_digraph_ext v2 e2 tl hd ()

