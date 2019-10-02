{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module PeanoNat where

import qualified Prelude
import qualified Bool
import qualified Datatypes
import qualified Decimal
import qualified Logic

__ :: any
__ = Prelude.error "Logical or arity value used"

type Nat__Coq_t = Prelude.Integer

_Nat__zero :: Prelude.Integer
_Nat__zero =
  0

_Nat__one :: Prelude.Integer
_Nat__one =
  Prelude.succ 0

_Nat__two :: Prelude.Integer
_Nat__two =
  Prelude.succ (Prelude.succ 0)

_Nat__succ :: Prelude.Integer -> Prelude.Integer
_Nat__succ x =
  Prelude.succ x

_Nat__pred :: Prelude.Integer -> Prelude.Integer
_Nat__pred = (\n -> Prelude.max 0 (Prelude.pred n))

_Nat__double :: Prelude.Integer -> Prelude.Integer
_Nat__double n =
  (Prelude.+) n n

_Nat__sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__sub = (\n m -> Prelude.max 0 (n Prelude.- m))

_Nat__ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
_Nat__ltb n m =
  (Prelude.<=) (Prelude.succ n) m

_Nat__compare :: Prelude.Integer -> Prelude.Integer ->
                 Datatypes.Coq_comparison
_Nat__compare n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Datatypes.Eq)
      (\_ -> Datatypes.Lt)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Datatypes.Gt)
      (\m' -> _Nat__compare n' m')
      m)
    n

_Nat__even :: Prelude.Integer -> Prelude.Bool
_Nat__even n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.True)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\n' -> _Nat__even n')
      n0)
    n

_Nat__odd :: Prelude.Integer -> Prelude.Bool
_Nat__odd n =
  Prelude.not (_Nat__even n)

_Nat__pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__pow n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.succ 0)
    (\m0 -> (Prelude.*) n (_Nat__pow n m0))
    m

_Nat__tail_add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__tail_add n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\n0 -> _Nat__tail_add n0 (Prelude.succ m))
    n

_Nat__tail_addmul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
                     Prelude.Integer
_Nat__tail_addmul r n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> r)
    (\n0 -> _Nat__tail_addmul (_Nat__tail_add m r) n0 m)
    n

_Nat__tail_mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__tail_mul n m =
  _Nat__tail_addmul 0 n m

_Nat__of_uint_acc :: Decimal.Coq_uint -> Prelude.Integer -> Prelude.Integer
_Nat__of_uint_acc d acc =
  case d of {
   Decimal.Nil -> acc;
   Decimal.D0 d0 ->
    _Nat__of_uint_acc d0
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc);
   Decimal.D1 d0 ->
    _Nat__of_uint_acc d0 (Prelude.succ
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc));
   Decimal.D2 d0 ->
    _Nat__of_uint_acc d0 (Prelude.succ (Prelude.succ
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc)));
   Decimal.D3 d0 ->
    _Nat__of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc))));
   Decimal.D4 d0 ->
    _Nat__of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc)))));
   Decimal.D5 d0 ->
    _Nat__of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc))))));
   Decimal.D6 d0 ->
    _Nat__of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc)))))));
   Decimal.D7 d0 ->
    _Nat__of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc))))))));
   Decimal.D8 d0 ->
    _Nat__of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc)))))))));
   Decimal.D9 d0 ->
    _Nat__of_uint_acc d0 (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ
      (_Nat__tail_mul (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
        (Prelude.succ 0)))))))))) acc))))))))))}

_Nat__of_uint :: Decimal.Coq_uint -> Prelude.Integer
_Nat__of_uint d =
  _Nat__of_uint_acc d 0

_Nat__to_little_uint :: Prelude.Integer -> Decimal.Coq_uint ->
                        Decimal.Coq_uint
_Nat__to_little_uint n acc =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> acc)
    (\n0 -> _Nat__to_little_uint n0 (Decimal._Little__succ acc))
    n

_Nat__to_uint :: Prelude.Integer -> Decimal.Coq_uint
_Nat__to_uint n =
  Decimal.rev (_Nat__to_little_uint n (Decimal.D0 Decimal.Nil))

_Nat__of_int :: Decimal.Coq_int -> Prelude.Maybe Prelude.Integer
_Nat__of_int d =
  case Decimal.norm d of {
   Decimal.Pos u -> Prelude.Just (_Nat__of_uint u);
   Decimal.Neg _ -> Prelude.Nothing}

_Nat__to_int :: Prelude.Integer -> Decimal.Coq_int
_Nat__to_int n =
  Decimal.Pos (_Nat__to_uint n)

_Nat__divmod :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
                Prelude.Integer -> (,) Prelude.Integer Prelude.Integer
_Nat__divmod x y q u =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (,) q u)
    (\x' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> _Nat__divmod x' y (Prelude.succ q) y)
      (\u' -> _Nat__divmod x' y q u')
      u)
    x

_Nat__modulo :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__modulo = (\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)

_Nat__gcd :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__gcd a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> b)
    (\a' -> _Nat__gcd (_Nat__modulo b (Prelude.succ a')) (Prelude.succ a'))
    a

_Nat__square :: Prelude.Integer -> Prelude.Integer
_Nat__square n =
  (Prelude.*) n n

_Nat__sqrt_iter :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
                   Prelude.Integer -> Prelude.Integer
_Nat__sqrt_iter k p q r =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\k' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      _Nat__sqrt_iter k' (Prelude.succ p) (Prelude.succ (Prelude.succ q))
        (Prelude.succ (Prelude.succ q)))
      (\r' -> _Nat__sqrt_iter k' p q r')
      r)
    k

_Nat__sqrt :: Prelude.Integer -> Prelude.Integer
_Nat__sqrt n =
  _Nat__sqrt_iter n 0 0 0

_Nat__log2_iter :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
                   Prelude.Integer -> Prelude.Integer
_Nat__log2_iter k p q r =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\k' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> _Nat__log2_iter k' (Prelude.succ p) (Prelude.succ q) q)
      (\r' -> _Nat__log2_iter k' p (Prelude.succ q) r')
      r)
    k

_Nat__log2 :: Prelude.Integer -> Prelude.Integer
_Nat__log2 n =
  _Nat__log2_iter (_Nat__pred n) 0 (Prelude.succ 0) 0

_Nat__iter :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
_Nat__iter n f x =
  Datatypes.nat_rect x (\_ -> f) n

_Nat__div2 :: Prelude.Integer -> Prelude.Integer
_Nat__div2 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> 0)
      (\n' -> Prelude.succ (_Nat__div2 n'))
      n0)
    n

_Nat__testbit :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
_Nat__testbit a n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> _Nat__odd a)
    (\n0 -> _Nat__testbit (_Nat__div2 a) n0)
    n

_Nat__shiftl :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__shiftl a =
  Datatypes.nat_rect a (\_ -> _Nat__double)

_Nat__shiftr :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__shiftr a =
  Datatypes.nat_rect a (\_ -> _Nat__div2)

_Nat__bitwise :: (Prelude.Bool -> Prelude.Bool -> Prelude.Bool) ->
                 Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
                 Prelude.Integer
_Nat__bitwise op n a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n' ->
    (Prelude.+)
      (case op (_Nat__odd a) (_Nat__odd b) of {
        Prelude.True -> Prelude.succ 0;
        Prelude.False -> 0})
      ((Prelude.*) (Prelude.succ (Prelude.succ 0))
        (_Nat__bitwise op n' (_Nat__div2 a) (_Nat__div2 b))))
    n

_Nat__land :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__land a b =
  _Nat__bitwise (Prelude.&&) a a b

_Nat__lor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__lor a b =
  _Nat__bitwise (Prelude.||) (Prelude.max a b) a b

_Nat__ldiff :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__ldiff a b =
  _Nat__bitwise (\b0 b' -> (Prelude.&&) b0 (Prelude.not b')) a a b

_Nat__lxor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__lxor a b =
  _Nat__bitwise Datatypes.xorb (Prelude.max a b) a b

_Nat__recursion :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer ->
                   a1
_Nat__recursion =
  Datatypes.nat_rect

_Nat__leb_spec0 :: Prelude.Integer -> Prelude.Integer -> Bool.Coq_reflect
_Nat__leb_spec0 x y =
  Bool.iff_reflect ((Prelude.<=) x y)

_Nat__ltb_spec0 :: Prelude.Integer -> Prelude.Integer -> Bool.Coq_reflect
_Nat__ltb_spec0 x y =
  Bool.iff_reflect (_Nat__ltb x y)

_Nat__Private_Dec__max_case_strong :: Prelude.Integer -> Prelude.Integer ->
                                      (Prelude.Integer -> Prelude.Integer ->
                                      () -> a1 -> a1) -> (() -> a1) -> (() ->
                                      a1) -> a1
_Nat__Private_Dec__max_case_strong n m compat hl hr =
  let {c = Datatypes.coq_CompSpec2Type n m (_Nat__compare n m)} in
  case c of {
   Datatypes.CompGtT -> compat n (Prelude.max n m) __ (hl __);
   _ -> compat m (Prelude.max n m) __ (hr __)}

_Nat__Private_Dec__max_case :: Prelude.Integer -> Prelude.Integer ->
                               (Prelude.Integer -> Prelude.Integer -> () ->
                               a1 -> a1) -> a1 -> a1 -> a1
_Nat__Private_Dec__max_case n m x x0 x1 =
  _Nat__Private_Dec__max_case_strong n m x (\_ -> x0) (\_ -> x1)

_Nat__Private_Dec__max_dec :: Prelude.Integer -> Prelude.Integer ->
                              Prelude.Bool
_Nat__Private_Dec__max_dec n m =
  _Nat__Private_Dec__max_case n m (\_ _ _ h0 -> h0) Prelude.True
    Prelude.False

_Nat__Private_Dec__min_case_strong :: Prelude.Integer -> Prelude.Integer ->
                                      (Prelude.Integer -> Prelude.Integer ->
                                      () -> a1 -> a1) -> (() -> a1) -> (() ->
                                      a1) -> a1
_Nat__Private_Dec__min_case_strong n m compat hl hr =
  let {c = Datatypes.coq_CompSpec2Type n m (_Nat__compare n m)} in
  case c of {
   Datatypes.CompGtT -> compat m (Prelude.min n m) __ (hr __);
   _ -> compat n (Prelude.min n m) __ (hl __)}

_Nat__Private_Dec__min_case :: Prelude.Integer -> Prelude.Integer ->
                               (Prelude.Integer -> Prelude.Integer -> () ->
                               a1 -> a1) -> a1 -> a1 -> a1
_Nat__Private_Dec__min_case n m x x0 x1 =
  _Nat__Private_Dec__min_case_strong n m x (\_ -> x0) (\_ -> x1)

_Nat__Private_Dec__min_dec :: Prelude.Integer -> Prelude.Integer ->
                              Prelude.Bool
_Nat__Private_Dec__min_dec n m =
  _Nat__Private_Dec__min_case n m (\_ _ _ h0 -> h0) Prelude.True
    Prelude.False

_Nat__max_case_strong :: Prelude.Integer -> Prelude.Integer -> (() -> a1) ->
                         (() -> a1) -> a1
_Nat__max_case_strong n m x x0 =
  _Nat__Private_Dec__max_case_strong n m (\_ _ _ x1 ->
    Logic.eq_rect __ x1 __) x x0

_Nat__max_case :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
_Nat__max_case n m x x0 =
  _Nat__max_case_strong n m (\_ -> x) (\_ -> x0)

_Nat__max_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
_Nat__max_dec =
  _Nat__Private_Dec__max_dec

_Nat__min_case_strong :: Prelude.Integer -> Prelude.Integer -> (() -> a1) ->
                         (() -> a1) -> a1
_Nat__min_case_strong n m x x0 =
  _Nat__Private_Dec__min_case_strong n m (\_ _ _ x1 ->
    Logic.eq_rect __ x1 __) x x0

_Nat__min_case :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
_Nat__min_case n m x x0 =
  _Nat__min_case_strong n m (\_ -> x) (\_ -> x0)

_Nat__min_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
_Nat__min_dec =
  _Nat__Private_Dec__min_dec

_Nat__sqrt_up :: Prelude.Integer -> Prelude.Integer
_Nat__sqrt_up a =
  case _Nat__compare 0 a of {
   Datatypes.Lt -> Prelude.succ (_Nat__sqrt (_Nat__pred a));
   _ -> 0}

_Nat__log2_up :: Prelude.Integer -> Prelude.Integer
_Nat__log2_up a =
  case _Nat__compare (Prelude.succ 0) a of {
   Datatypes.Lt -> Prelude.succ (_Nat__log2 (_Nat__pred a));
   _ -> 0}

_Nat__lcm :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__lcm a b =
  (Prelude.*) a
    ((\n m -> if m Prelude.== 0 then 0 else Prelude.div n m) b
      (_Nat__gcd a b))

_Nat__eqb_spec :: Prelude.Integer -> Prelude.Integer -> Bool.Coq_reflect
_Nat__eqb_spec x y =
  Bool.iff_reflect ((Prelude.==) x y)

_Nat__b2n :: Prelude.Bool -> Prelude.Integer
_Nat__b2n b =
  case b of {
   Prelude.True -> Prelude.succ 0;
   Prelude.False -> 0}

_Nat__setbit :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__setbit a n =
  _Nat__lor a (_Nat__shiftl (Prelude.succ 0) n)

_Nat__clearbit :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__clearbit a n =
  _Nat__ldiff a (_Nat__shiftl (Prelude.succ 0) n)

_Nat__ones :: Prelude.Integer -> Prelude.Integer
_Nat__ones n =
  _Nat__pred (_Nat__shiftl (Prelude.succ 0) n)

_Nat__lnot :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
_Nat__lnot a n =
  _Nat__lxor a (_Nat__ones n)

