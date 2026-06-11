import Internship.Semiring.Base
import Internship.Semiring.UANaive

open Base
open SUANaive

namespace SUAExtended

@[grind cases]
inductive Arrow where
  | A_to_1
  | A_to_M
  | A_to_bot
  deriving DecidableEq, Repr, Fintype

open Arrow

@[grind cases]
inductive UAExtendedSemiring where
  | atom : UANaiveSemiring → UAExtendedSemiring
  | arrow : Arrow → UAExtendedSemiring
  deriving DecidableEq, Repr, Fintype

open UAExtendedSemiring

@[grind]
def add : UAExtendedSemiring → UAExtendedSemiring → UAExtendedSemiring
  | atom m, atom n  => atom (m + n)
  | atom 0, n       => n
  | n, atom 0       => n
  | _, _            => arrow A_to_bot

@[grind]
def mul : UAExtendedSemiring → UAExtendedSemiring → UAExtendedSemiring
  | atom m, atom n           => atom (m * n)
  | atom 0, _                => atom 0
  | _, atom 0                => atom 0
  | atom 1, n                => n
  | n, atom 1                => n
  | atom .A, arrow n         => arrow n
  | arrow A_to_1, arrow n    => arrow n
  | _, arrow _               => arrow A_to_bot
  | arrow A_to_1, atom .A    => atom .A
  | arrow _, atom .A         => atom .AM
  | arrow _, atom .AM        => atom .AM
  | arrow A_to_bot, atom .M  => arrow A_to_bot
  | arrow _, atom .M         => arrow A_to_M
  | arrow _, atom .bot       => arrow A_to_bot

@[grind]
def meet : UAExtendedSemiring → UAExtendedSemiring → UAExtendedSemiring
  | atom m, atom n           => atom (m ⊓ n)
  | arrow A_to_bot, n        => n
  | n, arrow A_to_bot        => n
  | arrow A_to_M, atom .bot  => atom .M
  | atom .bot, arrow A_to_M  => atom .M
  | arrow A_to_M, n          => n
  | n, arrow A_to_M          => n
  | arrow A_to_1, atom .bot  => atom 1
  | atom .bot, arrow A_to_1  => atom 1
  | arrow A_to_1, atom .M    => atom 1
  | atom .M, arrow A_to_1    => atom 1
  | arrow A_to_1, atom .AM   => atom .A
  | atom .AM, arrow A_to_1   => atom .A
  | arrow A_to_1, n          => n
  | n, arrow A_to_1          => n

instance : Zero UAExtendedSemiring where
  zero := atom .zero

@[grind =] theorem UAExtendedSemiring.zero_eq :
    (0 : UAExtendedSemiring) = atom .zero := rfl

instance : One UAExtendedSemiring where
  one := atom .one

@[grind =] theorem UAExtendedSemiring.one_eq :
    (1 : UAExtendedSemiring) = atom .one := rfl

instance : Add UAExtendedSemiring where
  add := add

@[grind =] theorem UAExtendedSemiring.hadd_eq (a b : UAExtendedSemiring) :
    a + b = add a b := rfl

instance : Mul UAExtendedSemiring where
  mul := mul

@[grind =] theorem UAExtendedSemiring.hmul_eq (a b : UAExtendedSemiring) :
    a * b = mul a b := rfl

instance : Min UAExtendedSemiring where
  min := meet

@[grind =] theorem UAExtendedSemiring.hmin_eq (a b : UAExtendedSemiring) :
    a ⊓ b = meet a b := rfl

instance : LE UAExtendedSemiring where
  le a b := a ⊓ b = a

@[grind =] theorem UAExtendedSemiring.hle_eq (a b : UAExtendedSemiring) :
    (a ≤ b) = (a ⊓ b = a) := rfl

instance : OrderedSemiring UAExtendedSemiring where
  add_assoc := by native_decide
  add_comm := by native_decide
  add_zero := by native_decide
  zero_add := by native_decide

  mul_assoc := by native_decide
  mul_one := by native_decide
  one_mul := by native_decide
  mul_zero := by native_decide
  zero_mul := by native_decide

  inf_assoc := by native_decide
  inf_comm := by native_decide
  inf_idem := by native_decide

  mul_add := by native_decide
  add_mul := by native_decide

  mul_inf := by sorry -- use 'grind' to see a counter-example
  inf_mul := by native_decide

  add_inf := by native_decide
  inf_add := by native_decide

theorem mult_monotone_left (a b c : UAExtendedSemiring) (h : a ≤ b) :
    a * c ≤ b * c := by grind

theorem mult_monotone_right (a b c : UAExtendedSemiring) (h : a ≤ b) :
    c * a ≤ c * b := by grind

theorem left_residual (q r : UAExtendedSemiring) :
    (.arrow A_to_1 * r) ≤ q ↔ r ≤ (.atom .A * q) := by grind
