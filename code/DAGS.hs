{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  DAGS(Int, Linorder, Nat, Set(..), Pre_digraph_ext(..), anticone, blockDAG,
        top_sort, orderDAG_Int, spectreOrder_Int, vote_Spectre_Int)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Num = One | Bit0 Num | Bit1 Num;

data Int = Zero_int | Pos Num | Neg Num;

one_int :: Int;
one_int = Pos One;

class One a where {
  one :: a;
};

instance One Int where {
  one = one_int;
};

plus_num :: Num -> Num -> Num;
plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One);
plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n);
plus_num (Bit1 m) One = Bit0 (plus_num m One);
plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n);
plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n);
plus_num (Bit0 m) One = Bit1 m;
plus_num One (Bit1 n) = Bit0 (plus_num n One);
plus_num One (Bit0 n) = Bit1 n;
plus_num One One = Bit0 One;

uminus_int :: Int -> Int;
uminus_int (Neg m) = Pos m;
uminus_int (Pos m) = Neg m;
uminus_int Zero_int = Zero_int;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

dup :: Int -> Int;
dup (Neg n) = Neg (Bit0 n);
dup (Pos n) = Pos (Bit0 n);
dup Zero_int = Zero_int;

plus_int :: Int -> Int -> Int;
plus_int (Neg m) (Neg n) = Neg (plus_num m n);
plus_int (Neg m) (Pos n) = sub n m;
plus_int (Pos m) (Neg n) = sub m n;
plus_int (Pos m) (Pos n) = Pos (plus_num m n);
plus_int Zero_int l = l;
plus_int k Zero_int = k;

sub :: Num -> Num -> Int;
sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) one_int;
sub (Bit1 m) (Bit0 n) = plus_int (dup (sub m n)) one_int;
sub (Bit1 m) (Bit1 n) = dup (sub m n);
sub (Bit0 m) (Bit0 n) = dup (sub m n);
sub One (Bit1 n) = Neg (Bit0 n);
sub One (Bit0 n) = Neg (bitM n);
sub (Bit1 m) One = Pos (Bit0 m);
sub (Bit0 m) One = Pos (bitM m);
sub One One = Zero_int;

minus_int :: Int -> Int -> Int;
minus_int (Neg m) (Neg n) = sub n m;
minus_int (Neg m) (Pos n) = Neg (plus_num m n);
minus_int (Pos m) (Neg n) = Pos (plus_num m n);
minus_int (Pos m) (Pos n) = sub m n;
minus_int Zero_int l = uminus_int l;
minus_int k Zero_int = k;

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Int where {
  plus = plus_int;
};

class Zero a where {
  zero :: a;
};

instance Zero Int where {
  zero = Zero_int;
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

instance Semigroup_add Int where {
};

instance Monoid_add Int where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

instance Zero_neq_one Int where {
};

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Integer where {
};

instance Order Integer where {
};

class (Order a) => Linorder a where {
};

instance Linorder Integer where {
};

data Nat = Zero_nat | Suc Nat;

data Set a = Set [a] | Coset [a];

data Pre_digraph_ext a b c =
  Pre_digraph_ext (Set a) (Set b) (b -> a) (b -> a) c;

bex :: forall a. Set a -> (a -> Bool) -> Bool;
bex (Set xs) p = any p xs;

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero_nat n = Zero_nat;
minus_nat m Zero_nat = m;

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

relcomp :: forall a b c. (Eq b) => Set (a, b) -> Set (b, c) -> Set (a, c);
relcomp (Set xys) (Set yzs) =
  Set (concatMap
        (\ xy ->
          concatMap
            (\ yz -> (if snd xy == fst yz then [(fst xy, snd yz)] else [])) yzs)
        xys);

ntrancl :: forall a. (Eq a) => Nat -> Set (a, a) -> Set (a, a);
ntrancl (Suc n) r = let {
                      ra = ntrancl n r;
                    } in sup_set ra (relcomp ra r);
ntrancl Zero_nat r = r;

one_nat :: Nat;
one_nat = Suc Zero_nat;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

card :: forall a. (Eq a) => Set a -> Nat;
card (Set xs) = size_list (remdups xs);

trancl :: forall a. (Eq a) => Set (a, a) -> Set (a, a);
trancl (Set xs) = ntrancl (minus_nat (card (Set xs)) one_nat) (Set xs);

verts :: forall a b c. Pre_digraph_ext a b c -> Set a;
verts (Pre_digraph_ext verts arcs tail head more) = verts;

arcs :: forall a b c. Pre_digraph_ext a b c -> Set b;
arcs (Pre_digraph_ext verts arcs tail head more) = arcs;

tail :: forall a b c. Pre_digraph_ext a b c -> b -> a;
tail (Pre_digraph_ext verts arcs tail head more) = tail;

head :: forall a b c. Pre_digraph_ext a b c -> b -> a;
head (Pre_digraph_ext verts arcs tail head more) = head;

arc_to_ends :: forall a b. Pre_digraph_ext a b () -> b -> (a, a);
arc_to_ends g e = (tail g e, head g e);

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

arcs_ends :: forall a b. Pre_digraph_ext a b () -> Set (a, a);
arcs_ends g = image (arc_to_ends g) (arcs g);

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

wf_digraph :: forall a b. (Eq a) => Pre_digraph_ext a b () -> Bool;
wf_digraph g =
  ball (arcs g) (\ e -> member (tail g e) (verts g)) &&
    ball (arcs g) (\ e -> member (head g e) (verts g));

loopfree_digraph :: forall a b. (Eq a) => Pre_digraph_ext a b () -> Bool;
loopfree_digraph g =
  wf_digraph g && ball (arcs g) (\ e -> not (tail g e == head g e));

nomulti_digraph :: forall a b. (Eq a, Eq b) => Pre_digraph_ext a b () -> Bool;
nomulti_digraph g =
  wf_digraph g &&
    ball (arcs g)
      (\ e1 ->
        ball (arcs g)
          (\ e2 ->
            (if arc_to_ends g e1 == arc_to_ends g e2 then e1 == e2 else True)));

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

is_empty :: forall a. Set a -> Bool;
is_empty (Set xs) = null xs;

fin_digraph :: forall a b. (Eq a, Eq b) => Pre_digraph_ext a b () -> Bool;
fin_digraph g =
  wf_digraph g &&
    (less_nat Zero_nat (card (verts g)) || is_empty (verts g)) &&
      (less_nat Zero_nat (card (arcs g)) || is_empty (arcs g));

digraph :: forall a b. (Eq a, Eq b) => Pre_digraph_ext a b () -> Bool;
digraph g = fin_digraph g && loopfree_digraph g && nomulti_digraph g;

dag :: forall a b. (Eq a, Eq b) => Pre_digraph_ext a b () -> Bool;
dag g =
  digraph g &&
    ball (verts g) (\ v -> not (member (v, v) (trancl (arcs_ends g))));

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) (Suc n) = nth xs n;
nth (x : xs) Zero_nat = x;

is_tip :: forall a b. (Eq a) => Pre_digraph_ext a b () -> a -> Bool;
is_tip g a =
  member a (verts g) &&
    ball (verts g) (\ x -> not (member (x, a) (trancl (arcs_ends g))));

filtera :: forall a. (a -> Bool) -> Set a -> Set a;
filtera p (Set xs) = Set (filter p xs);

tips :: forall a b. (Eq a) => Pre_digraph_ext a b () -> Set a;
tips g = filtera (is_tip g) (verts g);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Coset xs) = Coset (inserta x xs);
remove x (Set xs) = Set (removeAll x xs);

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

anticone :: forall a b. (Eq a) => Pre_digraph_ext a b () -> a -> Set a;
anticone g a =
  filtera
    (\ b ->
      not (member (a, b) (trancl (arcs_ends g)) ||
            (member (b, a) (trancl (arcs_ends g)) || a == b)))
    (verts g);

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset []) (Set []) = False;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

kCluster ::
  forall a b. (Eq a) => Pre_digraph_ext a b () -> Nat -> Set a -> Bool;
kCluster g k c =
  (if less_eq_set c (verts g)
    then ball c (\ a -> less_eq_nat (card (inf_set (anticone g a) c)) k)
    else False);

arcAlt ::
  forall a b. (Eq a, Eq b) => Pre_digraph_ext a b () -> b -> (a, a) -> Bool;
arcAlt g e uv = member e (arcs g) && tail g e == fst uv && head g e == snd uv;

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

nat_of_num :: Num -> Nat;
nat_of_num (Bit1 n) = let {
                        m = nat_of_num n;
                      } in Suc (plus_nat m m);
nat_of_num (Bit0 n) = let {
                        m = nat_of_num n;
                      } in plus_nat m m;
nat_of_num One = one_nat;

past_nodes :: forall a b. (Eq a) => Pre_digraph_ext a b () -> a -> Set a;
past_nodes g a =
  filtera (\ b -> member (a, b) (trancl (arcs_ends g))) (verts g);

induce_subgraph ::
  forall a b.
    (Eq a) => Pre_digraph_ext a b () -> Set a -> Pre_digraph_ext a b ();
induce_subgraph g vs =
  Pre_digraph_ext vs
    (filtera (\ e -> member (tail g e) vs && member (head g e) vs) (arcs g))
    (tail g) (head g) ();

reduce_past ::
  forall a b. (Eq a) => Pre_digraph_ext a b () -> a -> Pre_digraph_ext a b ();
reduce_past g a = induce_subgraph g (past_nodes g a);

future_nodes :: forall a b. (Eq a) => Pre_digraph_ext a b () -> a -> Set a;
future_nodes g a =
  filtera (\ b -> member (b, a) (trancl (arcs_ends g))) (verts g);

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat m n =
  (if equal_nat n Zero_nat || less_nat m n then (Zero_nat, m)
    else let {
           a = divmod_nat (minus_nat m n) n;
         } in (case a of {
                (q, aa) -> (Suc q, aa);
              }));

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = fst (divmod_nat m n);

part :: forall a b. (Linorder b) => (a -> b) -> b -> [a] -> ([a], ([a], [a]));
part f pivot (x : xs) =
  (case part f pivot xs of {
    (lts, (eqs, gts)) ->
      let {
        xa = f x;
      } in (if less xa pivot then (x : lts, (eqs, gts))
             else (if less pivot xa then (lts, (eqs, x : gts))
                    else (lts, (x : eqs, gts))));
  });
part f pivot [] = ([], ([], []));

sort_key :: forall a b. (Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs =
  (case xs of {
    [] -> [];
    [_] -> xs;
    [x, y] -> (if less_eq (f x) (f y) then xs else [y, x]);
    _ : _ : _ : _ ->
      (case part f
              (f (nth xs (divide_nat (size_list xs) (nat_of_num (Bit0 One)))))
              xs
        of {
        (lts, (eqs, gts)) -> sort_key f lts ++ eqs ++ sort_key f gts;
      });
  });

sorted_list_of_set :: forall a. (Eq a, Linorder a) => Set a -> [a];
sorted_list_of_set (Set xs) = sort_key (\ x -> x) (remdups xs);

bot_set :: forall a. Set a;
bot_set = Set [];

add_set_list_tuple ::
  forall a. (Eq a, Linorder a) => ((Set a, [a]), a) -> (Set a, [a]);
add_set_list_tuple ((s, l), a) = (sup_set s (insert a bot_set), l ++ [a]);

app_if_blue_else_add_end ::
  forall a b.
    (Eq a,
      Linorder a) => Pre_digraph_ext a b () ->
                       Nat -> a -> (Set a, [a]) -> (Set a, [a]);
app_if_blue_else_add_end g k a (s, l) =
  (if kCluster g k (sup_set s (insert a bot_set))
    then add_set_list_tuple ((s, l), a) else (s, l ++ [a]));

larger_blue_tuple ::
  forall a.
    (Eq a,
      Linorder a) => ((Set a, [a]), a) ->
                       ((Set a, [a]), a) -> ((Set a, [a]), a);
larger_blue_tuple a b =
  (if less_nat (card (fst (fst b))) (card (fst (fst a))) ||
        less_eq_nat (card (fst (fst b))) (card (fst (fst a))) &&
          less_eq (snd a) (snd b)
    then a else b);

choose_max_blue_set ::
  forall a. (Eq a, Linorder a) => [((Set a, [a]), a)] -> ((Set a, [a]), a);
choose_max_blue_set l = fold larger_blue_tuple l (hd l);

del_arc ::
  forall a b. (Eq b) => Pre_digraph_ext a b () -> b -> Pre_digraph_ext a b ();
del_arc g a =
  Pre_digraph_ext (verts g) (remove a (arcs g)) (tail g) (head g) ();

blockDAG :: forall a b. (Eq a, Eq b) => Pre_digraph_ext a b () -> Bool;
blockDAG g =
  dag g &&
    bex (verts g)
      (\ p ->
        ball (verts g)
          (\ r -> member (r, p) (trancl (arcs_ends g)) || r == p)) &&
      ball (arcs g)
        (\ e ->
          ball (verts g)
            (\ u ->
              ball (verts g)
                (\ v ->
                  (if member (u, v) (trancl (arcs_ends (del_arc g e)))
                    then not (arcAlt g e (u, v)) else True))));

tie_breakingDAG ::
  forall a b. (Eq a, Linorder a, Eq b) => Pre_digraph_ext a b () -> Bool;
tie_breakingDAG g = blockDAG g;

genesis_nodeAlt ::
  forall a b. (Eq a, Linorder a, Eq b) => Pre_digraph_ext a b () -> a;
genesis_nodeAlt g =
  (if not (blockDAG g) then error "undefined"
    else (if equal_nat (card (verts g)) one_nat
           then hd (sorted_list_of_set (verts g))
           else genesis_nodeAlt
                  (reduce_past g (hd (sorted_list_of_set (tips g))))));

orderDAG ::
  forall a b.
    (Eq a, Linorder a, Eq b) => Pre_digraph_ext a b () -> Nat -> (Set a, [a]);
orderDAG g k =
  (if not (tie_breakingDAG g) then (bot_set, [])
    else (if equal_nat (card (verts g)) one_nat
           then (insert (genesis_nodeAlt g) bot_set, [genesis_nodeAlt g])
           else let {
                  m = choose_max_blue_set
                        (map (\ i -> (orderDAG (reduce_past g i) k, i))
                          (sorted_list_of_set (tips g)));
                  current = (add_set_list_tuple m, snd m);
                } in fold (app_if_blue_else_add_end g k)
                       (sorted_list_of_set (anticone g (snd m)))
                       (fst current)));

top_insert ::
  forall a b. (Eq a, Linorder a) => Pre_digraph_ext a b () -> [a] -> a -> [a];
top_insert g [] a = [a];
top_insert g (b : l) a =
  (if member (a, b) (trancl (arcs_ends g)) then b : top_insert g l a
    else a : b : l);

top_sort ::
  forall a b. (Eq a, Linorder a) => Pre_digraph_ext a b () -> [a] -> [a];
top_sort g [] = [];
top_sort g (a : l) = top_insert g (top_sort g l) a;

of_bool :: forall a. (Zero_neq_one a) => Bool -> a;
of_bool True = one;
of_bool False = zero;

equal_num :: Num -> Num -> Bool;
equal_num (Bit0 x2) (Bit1 x3) = False;
equal_num (Bit1 x3) (Bit0 x2) = False;
equal_num One (Bit1 x3) = False;
equal_num (Bit1 x3) One = False;
equal_num One (Bit0 x2) = False;
equal_num (Bit0 x2) One = False;
equal_num (Bit1 x3) (Bit1 y3) = equal_num x3 y3;
equal_num (Bit0 x2) (Bit0 y2) = equal_num x2 y2;
equal_num One One = True;

equal_int :: Int -> Int -> Bool;
equal_int (Neg k) (Neg l) = equal_num k l;
equal_int (Neg k) (Pos l) = False;
equal_int (Neg k) Zero_int = False;
equal_int (Pos k) (Neg l) = False;
equal_int (Pos k) (Pos l) = equal_num k l;
equal_int (Pos k) Zero_int = False;
equal_int Zero_int (Neg l) = False;
equal_int Zero_int (Pos l) = False;
equal_int Zero_int Zero_int = True;

adjust_div :: (Int, Int) -> Int;
adjust_div (q, r) = plus_int q (of_bool (not (equal_int r Zero_int)));

adjust_mod :: Int -> Int -> Int;
adjust_mod l r = (if equal_int r Zero_int then Zero_int else minus_int l r);

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

nat_of_integer :: Integer -> Nat;
nat_of_integer k =
  (if k <= (0 :: Integer) then Zero_nat
    else (case divmod_integer k (2 :: Integer) of {
           (l, j) ->
             let {
               la = nat_of_integer l;
               lb = plus_nat la la;
             } in (if j == (0 :: Integer) then lb else plus_nat lb one_nat);
         }));

orderDAG_Int ::
  Pre_digraph_ext Integer (Integer, Integer) () ->
    Integer -> (Set Integer, [Integer]);
orderDAG_Int v a = orderDAG v (nat_of_integer a);

sum_list :: forall a. (Monoid_add a) => [a] -> a;
sum_list xs = foldr plus xs zero;

less_num :: Num -> Num -> Bool;
less_num (Bit1 m) (Bit0 n) = less_num m n;
less_num (Bit1 m) (Bit1 n) = less_num m n;
less_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_num (Bit0 m) (Bit0 n) = less_num m n;
less_num One (Bit1 n) = True;
less_num One (Bit0 n) = True;
less_num m One = False;

less_eq_num :: Num -> Num -> Bool;
less_eq_num (Bit1 m) (Bit0 n) = less_num m n;
less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n;
less_eq_num (Bit1 m) One = False;
less_eq_num (Bit0 m) One = False;
less_eq_num One n = True;

less_int :: Int -> Int -> Bool;
less_int (Neg k) (Neg l) = less_num l k;
less_int (Neg k) (Pos l) = True;
less_int (Neg k) Zero_int = True;
less_int (Pos k) (Neg l) = False;
less_int (Pos k) (Pos l) = less_num k l;
less_int (Pos k) Zero_int = False;
less_int Zero_int (Neg l) = False;
less_int Zero_int (Pos l) = True;
less_int Zero_int Zero_int = False;

tie_break_int :: forall a. (Linorder a) => a -> a -> Int -> Int;
tie_break_int a b i =
  (if equal_int i Zero_int
    then (if less b a then uminus_int one_int else one_int)
    else (if less_int Zero_int i then one_int else uminus_int one_int));

sumlist_break :: forall a. (Linorder a) => a -> a -> [Int] -> Int;
sumlist_break a b [] = Zero_int;
sumlist_break a b (x : xs) = tie_break_int a b (sum_list (x : xs));

vote_Spectre ::
  forall a b.
    (Eq a, Linorder a, Eq b) => Pre_digraph_ext a b () -> a -> a -> a -> Int;
vote_Spectre v a b c =
  (if not (blockDAG v) ||
        (not (member a (verts v)) ||
          (not (member b (verts v)) || not (member c (verts v))))
    then Zero_int
    else (if b == c then one_int
           else (if (member (a, b) (trancl (arcs_ends v)) || a == b) &&
                      not (member (a, c) (trancl (arcs_ends v)))
                  then one_int
                  else (if (member (a, c) (trancl (arcs_ends v)) || a == c) &&
                             not (member (a, b) (trancl (arcs_ends v)))
                         then uminus_int one_int
                         else (if member (a, b) (trancl (arcs_ends v)) &&
                                    member (a, c) (trancl (arcs_ends v))
                                then sumlist_break b c
                                       (map
 (\ i -> vote_Spectre (reduce_past v a) i b c)
 (sorted_list_of_set (past_nodes v a)))
                                else sumlist_break b c
                                       (map (\ i -> vote_Spectre v i b c)
 (sorted_list_of_set (future_nodes v a))))))));

spectreOrderAlt ::
  forall a b.
    (Eq a, Linorder a, Eq b) => Pre_digraph_ext a b () -> a -> a -> Bool;
spectreOrderAlt g a b =
  (if not (blockDAG g) then error "undefined"
    else equal_int (vote_Spectre g (genesis_nodeAlt g) a b) one_int);

spectreOrder_Int ::
  Pre_digraph_ext Integer (Integer, Integer) () -> Integer -> Integer -> Bool;
spectreOrder_Int g = spectreOrderAlt g;

times_num :: Num -> Num -> Num;
times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));
times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n);
times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n));
times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n));
times_num One n = n;
times_num m One = m;

times_int :: Int -> Int -> Int;
times_int (Neg m) (Neg n) = Pos (times_num m n);
times_int (Neg m) (Pos n) = Neg (times_num m n);
times_int (Pos m) (Neg n) = Neg (times_num m n);
times_int (Pos m) (Pos n) = Pos (times_num m n);
times_int Zero_int l = Zero_int;
times_int k Zero_int = Zero_int;

less_eq_int :: Int -> Int -> Bool;
less_eq_int (Neg k) (Neg l) = less_eq_num l k;
less_eq_int (Neg k) (Pos l) = True;
less_eq_int (Neg k) Zero_int = True;
less_eq_int (Pos k) (Neg l) = False;
less_eq_int (Pos k) (Pos l) = less_eq_num k l;
less_eq_int (Pos k) Zero_int = False;
less_eq_int Zero_int (Neg l) = False;
less_eq_int Zero_int (Pos l) = True;
less_eq_int Zero_int Zero_int = True;

divmod_step_int :: Num -> (Int, Int) -> (Int, Int);
divmod_step_int l (q, r) =
  (if less_eq_int (Pos l) r
    then (plus_int (times_int (Pos (Bit0 One)) q) one_int, minus_int r (Pos l))
    else (times_int (Pos (Bit0 One)) q, r));

divmod_int :: Num -> Num -> (Int, Int);
divmod_int (Bit1 m) (Bit1 n) =
  (if less_num m n then (Zero_int, Pos (Bit1 m))
    else divmod_step_int (Bit1 n) (divmod_int (Bit1 m) (Bit0 (Bit1 n))));
divmod_int (Bit0 m) (Bit1 n) =
  (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
    else divmod_step_int (Bit1 n) (divmod_int (Bit0 m) (Bit0 (Bit1 n))));
divmod_int (Bit1 m) (Bit0 n) =
  (case divmod_int m n of {
    (q, r) -> (q, plus_int (times_int (Pos (Bit0 One)) r) one_int);
  });
divmod_int (Bit0 m) (Bit0 n) = (case divmod_int m n of {
                                 (q, r) -> (q, times_int (Pos (Bit0 One)) r);
                               });
divmod_int One (Bit1 n) = (Zero_int, Pos One);
divmod_int One (Bit0 n) = (Zero_int, Pos One);
divmod_int m One = (Pos m, Zero_int);

modulo_int :: Int -> Int -> Int;
modulo_int (Neg m) (Neg n) = uminus_int (snd (divmod_int m n));
modulo_int (Pos m) (Neg n) =
  uminus_int (adjust_mod (Pos n) (snd (divmod_int m n)));
modulo_int (Neg m) (Pos n) = adjust_mod (Pos n) (snd (divmod_int m n));
modulo_int (Pos m) (Pos n) = snd (divmod_int m n);
modulo_int k (Neg One) = Zero_int;
modulo_int k (Pos One) = Zero_int;
modulo_int Zero_int k = Zero_int;
modulo_int k Zero_int = k;

divide_int :: Int -> Int -> Int;
divide_int (Neg m) (Neg n) = fst (divmod_int m n);
divide_int (Pos m) (Neg n) = uminus_int (adjust_div (divmod_int m n));
divide_int (Neg m) (Pos n) = uminus_int (adjust_div (divmod_int m n));
divide_int (Pos m) (Pos n) = fst (divmod_int m n);
divide_int k (Neg One) = uminus_int k;
divide_int k (Pos One) = k;
divide_int Zero_int k = Zero_int;
divide_int k Zero_int = Zero_int;

integer_of_int :: Int -> Integer;
integer_of_int k =
  (if less_int k Zero_int then negate (integer_of_int (uminus_int k))
    else (if equal_int k Zero_int then (0 :: Integer)
           else let {
                  l = (2 :: Integer) *
                        integer_of_int (divide_int k (Pos (Bit0 One)));
                  j = modulo_int k (Pos (Bit0 One));
                } in (if equal_int j Zero_int then l else l + (1 :: Integer))));

vote_Spectre_Int ::
  Pre_digraph_ext Integer (Integer, Integer) () ->
    Integer -> Integer -> Integer -> Integer;
vote_Spectre_Int v a b c = integer_of_int (vote_Spectre v a b c);

}
