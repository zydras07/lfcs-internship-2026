import Internship.Base
open Base

namespace UANaive

@[grind cases]
inductive UANaiveSemiring where
  | zero
  | one
  | A
  | M
  | AM
  | bot
  deriving DecidableEq, Repr, Fintype

open UANaiveSemiring

@[grind]
def add : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | zero, n  => n
  | n, zero  => n
  | one, _   => bot
  | _, one   => bot
  | bot, _   => bot
  | _, bot   => bot
  | M, _     => bot
  | _, M     => bot
  | A, A     => AM
  | A, AM    => AM
  | AM, A    => AM
  | AM, AM   => AM

@[grind]
def mul : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | zero, _   => zero
  | _, zero   => zero
  | one, n    => n
  | n, one    => n
  | A, A      => A
  | A, M      => AM
  | A, AM     => AM
  | A, bot    => AM
  | M, A      => AM
  | M, M      => M
  | M, AM     => AM
  | M, bot    => bot
  | AM, A     => AM   -- sorry
  | AM, M     => AM   -- sorry
  | AM, AM    => AM   -- sorry
  | AM, bot   => AM   -- sorry
  | bot, A    => AM
  | bot, M    => bot
  | bot, AM   => AM
  | bot, bot  => bot

@[grind]
def meet : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | zero, _    => zero
  | one, zero  => zero
  | one, one   => one
  | one, A     => A
  | one, M     => one
  | one, AM    => A
  | one, bot   => one
  | A, zero    => zero
  | A, _       => A
  | M, zero    => zero
  | M, one     => one
  | M, A       => A
  | M, M       => M
  | M, AM      => AM
  | M, bot     => M
  | AM, zero   => zero
  | AM, one    => A
  | AM, A      => A
  | AM, M      => AM
  | AM, AM     => AM
  | AM, bot    => AM
  | bot, n     => n

instance : Zero UANaiveSemiring where
  zero := zero

@[grind =] theorem UANaiveSemiring.zero_eq :
    (0 : UANaiveSemiring) = zero := rfl

instance : One UANaiveSemiring where
  one := one

@[grind =] theorem UANaiveSemiring.one_eq :
    (1 : UANaiveSemiring) = one := rfl

instance : Add UANaiveSemiring where
  add := add

@[grind =] theorem UANaiveSemiring.hadd_eq (a b : UANaiveSemiring) :
    a + b = add a b := rfl

instance : Mul UANaiveSemiring where
  mul := mul

@[grind =] theorem UANaiveSemiring.hmul_eq (a b : UANaiveSemiring) :
    a * b = mul a b := rfl

instance : Min UANaiveSemiring where
  min := meet

@[grind =] theorem UANaiveSemiring.hmin_eq (a b : UANaiveSemiring) :
    a ⊓ b = meet a b := rfl

instance : OrderedSemiring UANaiveSemiring where
  add_assoc := by grind
  add_comm := by decide
  add_zero := by decide
  zero_add := by decide

  mul_assoc := by decide
  mul_one := by decide
  one_mul := by decide
  mul_zero := by decide
  zero_mul := by decide

  inf_assoc := by decide
  inf_comm := by decide
  inf_idem := by decide

  mul_add := by decide
  add_mul := by decide

  mul_inf := by decide
  inf_mul := by decide

  add_inf := by decide
  inf_add := by decide
