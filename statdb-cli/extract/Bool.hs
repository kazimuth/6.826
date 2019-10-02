{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Bool where

import qualified Prelude
import qualified Datatypes
import qualified Logic

__ :: any
__ = Prelude.error "Logical or arity value used"

bool_dec :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
bool_dec b1 b2 =
  Datatypes.bool_rec (\x ->
    case x of {
     Prelude.True -> Prelude.True;
     Prelude.False -> Prelude.False}) (\x ->
    case x of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}) b1 b2

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

ifb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool
ifb b1 b2 b3 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> b3}

orb_true_elim :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb_true_elim b1 _ =
  case b1 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

andb_false_elim :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb_false_elim b1 _ =
  case b1 of {
   Prelude.True -> Prelude.False;
   Prelude.False -> Prelude.True}

data Coq_reflect =
   ReflectT
 | ReflectF

reflect_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> Coq_reflect -> a1
reflect_rect f f0 _ r =
  case r of {
   ReflectT -> f __;
   ReflectF -> f0 __}

reflect_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> Coq_reflect -> a1
reflect_rec =
  reflect_rect

iff_reflect :: Prelude.Bool -> Coq_reflect
iff_reflect b =
  case b of {
   Prelude.True -> Logic.and_rec (\_ _ -> ReflectT);
   Prelude.False -> Logic.and_rec (\_ _ -> ReflectF)}

reflect_dec :: Prelude.Bool -> Coq_reflect -> Prelude.Bool
reflect_dec _ h =
  case h of {
   ReflectT -> Prelude.True;
   ReflectF -> Prelude.False}

eqb_spec :: Prelude.Bool -> Prelude.Bool -> Coq_reflect
eqb_spec b b' =
  case b of {
   Prelude.True ->
    case b' of {
     Prelude.True -> ReflectT;
     Prelude.False -> ReflectF};
   Prelude.False ->
    case b' of {
     Prelude.True -> ReflectF;
     Prelude.False -> ReflectT}}

