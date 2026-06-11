import Internship.Quantale.Base
open Base

namespace QUANaive

@[grind cases]
inductive UANaiveSemiring where
  | bot
  | zero
  | one
  | A
  | M
  | AM
  | top
  deriving DecidableEq, Repr, Fintype

open UANaiveSemiring

@[grind]
def add : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | bot, _   => bot
  | _, bot   => bot
  | zero, n  => n
  | n, zero  => n
  | top, _   => top
  | _, top   => top
  | one, one => M
  | one, M   => M
  | M, one   => M
  | M, M     => M
  | one, A   => M
  | M, A     => M
  | A, one   => M
  | one, AM  => M
  | M, AM    => M
  | AM, one  => M
  | AM, M    => M
  | A, M     => M
  | A, A     => AM
  | A, AM    => AM
  | AM, A    => AM
  | AM, AM   => AM

@[grind]
def act : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | bot, _   => bot
  | _, bot   => bot
  | zero, _   => zero
  | _, zero   => zero
  | top, _    => top
  | _, top    => top
  | one, n    => n
  | n, one    => n
  | A, A      => A
  | M, M      => M
  | A, M      => AM
  | A, AM     => AM
  | M, A      => AM
  | M, AM     => AM
  | AM, A     => AM
  | AM, M     => AM
  | AM, AM    => AM

@[grind]
def meet : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | bot, _    => bot
  | _, bot    => bot
  | zero, _   => zero
  | _, zero   => zero
  | one, one  => one
  | one, A    => A
  | one, M    => one
  | one, AM   => A
  | A, _      => A
  | M, one    => one
  | M, A      => A
  | M, M      => M
  | M, AM     => AM
  | AM, one   => A
  | AM, A     => A
  | AM, M     => AM
  | AM, AM    => AM
  | n, top    => n
  | top, n    => n

instance : Bot UANaiveSemiring where
  bot := bot

@[grind =] theorem UANaiveSemiring.bot_eq :
    (⊥ : UANaiveSemiring) = bot := rfl

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

instance : Min UANaiveSemiring where
  min := meet

@[grind =] theorem UANaiveSemiring.hmin_eq (a b : UANaiveSemiring) :
    a ⊓ b = meet a b := rfl

instance : LE UANaiveSemiring where
  le a b := a ⊓ b = a

@[grind =] theorem UANaiveSemiring.hle_eq (a b : UANaiveSemiring) :
    (a ≤ b) = (a ⊓ b = a) := rfl

instance : Quantale UANaiveSemiring where
  inf_assoc := by native_decide
  inf_comm := by native_decide
  inf_idem := by native_decide
  inf_zero := by native_decide
  zero_inf := by native_decide

  seq_assoc := by native_decide
  zero_seq := by native_decide
  seq_zero := by native_decide
  bot_seq := by native_decide
  seq_bot := by native_decide

  seq_inf := by native_decide
  inf_seq := by native_decide

instance : Action UANaiveSemiring where
  act := act

  act_one := by native_decide
  one_act := by native_decide

  act_inf := by native_decide
  inf_act := by native_decide

  act_seq_monotone := by native_decide
