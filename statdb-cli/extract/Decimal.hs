{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Decimal where

import qualified Prelude

data Coq_uint =
   Nil
 | D0 Coq_uint
 | D1 Coq_uint
 | D2 Coq_uint
 | D3 Coq_uint
 | D4 Coq_uint
 | D5 Coq_uint
 | D6 Coq_uint
 | D7 Coq_uint
 | D8 Coq_uint
 | D9 Coq_uint

uint_rect :: a1 -> (Coq_uint -> a1 -> a1) -> (Coq_uint -> a1 -> a1) ->
             (Coq_uint -> a1 -> a1) -> (Coq_uint -> a1 -> a1) -> (Coq_uint ->
             a1 -> a1) -> (Coq_uint -> a1 -> a1) -> (Coq_uint -> a1 -> a1) ->
             (Coq_uint -> a1 -> a1) -> (Coq_uint -> a1 -> a1) -> (Coq_uint ->
             a1 -> a1) -> Coq_uint -> a1
uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u =
  case u of {
   Nil -> f;
   D0 u0 -> f0 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0);
   D1 u0 -> f1 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0);
   D2 u0 -> f2 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0);
   D3 u0 -> f3 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0);
   D4 u0 -> f4 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0);
   D5 u0 -> f5 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0);
   D6 u0 -> f6 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0);
   D7 u0 -> f7 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0);
   D8 u0 -> f8 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0);
   D9 u0 -> f9 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)}

uint_rec :: a1 -> (Coq_uint -> a1 -> a1) -> (Coq_uint -> a1 -> a1) ->
            (Coq_uint -> a1 -> a1) -> (Coq_uint -> a1 -> a1) -> (Coq_uint ->
            a1 -> a1) -> (Coq_uint -> a1 -> a1) -> (Coq_uint -> a1 -> a1) ->
            (Coq_uint -> a1 -> a1) -> (Coq_uint -> a1 -> a1) -> (Coq_uint ->
            a1 -> a1) -> Coq_uint -> a1
uint_rec =
  uint_rect

data Coq_int =
   Pos Coq_uint
 | Neg Coq_uint

int_rect :: (Coq_uint -> a1) -> (Coq_uint -> a1) -> Coq_int -> a1
int_rect f f0 i =
  case i of {
   Pos x -> f x;
   Neg x -> f0 x}

int_rec :: (Coq_uint -> a1) -> (Coq_uint -> a1) -> Coq_int -> a1
int_rec =
  int_rect

nzhead :: Coq_uint -> Coq_uint
nzhead d =
  case d of {
   D0 d0 -> nzhead d0;
   _ -> d}

unorm :: Coq_uint -> Coq_uint
unorm d =
  case nzhead d of {
   Nil -> D0 Nil;
   x -> x}

norm :: Coq_int -> Coq_int
norm d =
  case d of {
   Pos d0 -> Pos (unorm d0);
   Neg d0 -> case nzhead d0 of {
              Nil -> Pos (D0 Nil);
              x -> Neg x}}

opp :: Coq_int -> Coq_int
opp d =
  case d of {
   Pos d0 -> Neg d0;
   Neg d0 -> Pos d0}

revapp :: Coq_uint -> Coq_uint -> Coq_uint
revapp d d' =
  case d of {
   Nil -> d';
   D0 d0 -> revapp d0 (D0 d');
   D1 d0 -> revapp d0 (D1 d');
   D2 d0 -> revapp d0 (D2 d');
   D3 d0 -> revapp d0 (D3 d');
   D4 d0 -> revapp d0 (D4 d');
   D5 d0 -> revapp d0 (D5 d');
   D6 d0 -> revapp d0 (D6 d');
   D7 d0 -> revapp d0 (D7 d');
   D8 d0 -> revapp d0 (D8 d');
   D9 d0 -> revapp d0 (D9 d')}

rev :: Coq_uint -> Coq_uint
rev d =
  revapp d Nil

_Little__succ :: Coq_uint -> Coq_uint
_Little__succ d =
  case d of {
   Nil -> D1 Nil;
   D0 d0 -> D1 d0;
   D1 d0 -> D2 d0;
   D2 d0 -> D3 d0;
   D3 d0 -> D4 d0;
   D4 d0 -> D5 d0;
   D5 d0 -> D6 d0;
   D6 d0 -> D7 d0;
   D7 d0 -> D8 d0;
   D8 d0 -> D9 d0;
   D9 d0 -> D0 (_Little__succ d0)}

_Little__double :: Coq_uint -> Coq_uint
_Little__double d =
  case d of {
   Nil -> Nil;
   D0 d0 -> D0 (_Little__double d0);
   D1 d0 -> D2 (_Little__double d0);
   D2 d0 -> D4 (_Little__double d0);
   D3 d0 -> D6 (_Little__double d0);
   D4 d0 -> D8 (_Little__double d0);
   D5 d0 -> D0 (_Little__succ_double d0);
   D6 d0 -> D2 (_Little__succ_double d0);
   D7 d0 -> D4 (_Little__succ_double d0);
   D8 d0 -> D6 (_Little__succ_double d0);
   D9 d0 -> D8 (_Little__succ_double d0)}

_Little__succ_double :: Coq_uint -> Coq_uint
_Little__succ_double d =
  case d of {
   Nil -> D1 Nil;
   D0 d0 -> D1 (_Little__double d0);
   D1 d0 -> D3 (_Little__double d0);
   D2 d0 -> D5 (_Little__double d0);
   D3 d0 -> D7 (_Little__double d0);
   D4 d0 -> D9 (_Little__double d0);
   D5 d0 -> D1 (_Little__succ_double d0);
   D6 d0 -> D3 (_Little__succ_double d0);
   D7 d0 -> D5 (_Little__succ_double d0);
   D8 d0 -> D7 (_Little__succ_double d0);
   D9 d0 -> D9 (_Little__succ_double d0)}

uint_of_uint :: Coq_uint -> Coq_uint
uint_of_uint i =
  i

int_of_int :: Coq_int -> Coq_int
int_of_int i =
  i

