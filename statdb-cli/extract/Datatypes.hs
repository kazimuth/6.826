{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Datatypes where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

type Empty_set = () -- empty inductive

coq_Empty_set_rect :: Empty_set -> a1
coq_Empty_set_rect _ =
  Prelude.error "absurd case"

coq_Empty_set_rec :: Empty_set -> a1
coq_Empty_set_rec =
  coq_Empty_set_rect

unit_rect :: a1 -> () -> a1
unit_rect f _ =
  f

unit_rec :: a1 -> () -> a1
unit_rec =
  unit_rect

bool_rect :: a1 -> a1 -> Prelude.Bool -> a1
bool_rect f f0 b =
  case b of {
   Prelude.True -> f;
   Prelude.False -> f0}

bool_rec :: a1 -> a1 -> Prelude.Bool -> a1
bool_rec =
  bool_rect

implb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
implb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.True}

xorb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
xorb b1 b2 =
  case b1 of {
   Prelude.True ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True};
   Prelude.False -> b2}

eq_true_rect :: a1 -> Prelude.Bool -> a1
eq_true_rect f _ =
  f

eq_true_rec :: a1 -> Prelude.Bool -> a1
eq_true_rec =
  eq_true_rect

eq_true_rec_r :: Prelude.Bool -> a1 -> a1
eq_true_rec_r _ h =
  h

eq_true_rect_r :: Prelude.Bool -> a1 -> a1
eq_true_rect_r _ h =
  h

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

nat_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rec =
  nat_rect

option_rect :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
option_rect f f0 o =
  case o of {
   Prelude.Just x -> f x;
   Prelude.Nothing -> f0}

option_rec :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
option_rec =
  option_rect

option_map :: (a1 -> a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
option_map f o =
  case o of {
   Prelude.Just a -> Prelude.Just (f a);
   Prelude.Nothing -> Prelude.Nothing}

sum_rect :: (a1 -> a3) -> (a2 -> a3) -> (Prelude.Either a1 a2) -> a3
sum_rect f f0 s =
  case s of {
   Prelude.Left x -> f x;
   Prelude.Right x -> f0 x}

sum_rec :: (a1 -> a3) -> (a2 -> a3) -> (Prelude.Either a1 a2) -> a3
sum_rec =
  sum_rect

prod_rect :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_rect f p =
  case p of {
   (,) x x0 -> f x x0}

prod_rec :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_rec =
  prod_rect

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

prod_uncurry :: (((,) a1 a2) -> a3) -> a1 -> a2 -> a3
prod_uncurry f x y =
  f ((,) x y)

prod_curry :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_curry f p =
  case p of {
   (,) x y -> f x y}

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of {
   ([]) -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rec =
  list_rect

length :: (([]) a1) -> Prelude.Integer
length l =
  case l of {
   ([]) -> 0;
   (:) _ l' -> Prelude.succ (length l')}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Coq_comparison =
   Eq
 | Lt
 | Gt

comparison_rect :: a1 -> a1 -> a1 -> Coq_comparison -> a1
comparison_rect f f0 f1 c =
  case c of {
   Eq -> f;
   Lt -> f0;
   Gt -> f1}

comparison_rec :: a1 -> a1 -> a1 -> Coq_comparison -> a1
comparison_rec =
  comparison_rect

coq_CompOpp :: Coq_comparison -> Coq_comparison
coq_CompOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

coq_CompareSpecT_rect :: (() -> a1) -> (() -> a1) -> (() -> a1) ->
                         Coq_comparison -> CompareSpecT -> a1
coq_CompareSpecT_rect f f0 f1 _ c =
  case c of {
   CompEqT -> f __;
   CompLtT -> f0 __;
   CompGtT -> f1 __}

coq_CompareSpecT_rec :: (() -> a1) -> (() -> a1) -> (() -> a1) ->
                        Coq_comparison -> CompareSpecT -> a1
coq_CompareSpecT_rec =
  coq_CompareSpecT_rect

coq_CompareSpec2Type :: Coq_comparison -> CompareSpecT
coq_CompareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

coq_CompSpec2Type :: a1 -> a1 -> Coq_comparison -> CompSpecT a1
coq_CompSpec2Type _ _ =
  coq_CompareSpec2Type

identity_rect :: a1 -> a2 -> a1 -> a2
identity_rect _ f _ =
  f

identity_rec :: a1 -> a2 -> a1 -> a2
identity_rec =
  identity_rect

type ID = () -> Any -> Any

id :: a1 -> a1
id x =
  x

