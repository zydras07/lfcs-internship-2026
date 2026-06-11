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

@[grind cases]
inductive UANaiveMonoid where
  | one
  | A
  | M
  | AM
  deriving DecidableEq, Repr, Fintype

@[grind]
def meet : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | .bot, _    => .bot
  | _, .bot    => .bot
  | .zero, _   => .zero
  | _, .zero   => .zero
  | .one, .one => .one
  | .one, .A   => .A
  | .one, .M   => .one
  | .one, .AM  => .A
  | .A, _      => .A
  | .M, .one   => .one
  | .M, .A     => .A
  | .M, .M     => .M
  | .M, .AM    => .AM
  | .AM, .one  => .A
  | .AM, .A    => .A
  | .AM, .M    => .AM
  | .AM, .AM   => .AM
  | n, .top    => n
  | .top, n    => n

@[grind]
def seq : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | .bot, _   => .bot
  | _, .bot   => .bot
  | .zero, n  => n
  | n, .zero  => n
  | .top, _   => .top
  | _, .top   => .top
  | .one, .one => .M
  | .one, .M   => .M
  | .M, .one   => .M
  | .M, .M     => .M
  | .one, .A   => .M
  | .M, .A     => .M
  | .A, .one   => .M
  | .one, .AM  => .M
  | .M, .AM    => .M
  | .AM, .one  => .M
  | .AM, .M    => .M
  | .A, .M     => .M
  | .A, .A     => .AM
  | .A, .AM    => .AM
  | .AM, .A    => .AM
  | .AM, .AM   => .AM

@[grind]
def mul : UANaiveMonoid → UANaiveMonoid → UANaiveMonoid
  | .one, n    => n
  | n, .one    => n
  | .A, .A      => .A
  | .M, .M      => .M
  | .A, .M      => .AM
  | .A, .AM     => .AM
  | .M, .A      => .AM
  | .M, .AM     => .AM
  | .AM, .A     => .AM
  | .AM, .M     => .AM
  | .AM, .AM    => .AM

@[grind]
def act : UANaiveMonoid → UANaiveSemiring → UANaiveSemiring
  | _, .bot   => .bot
  | _, .zero   => .zero
  | _, .top    => .top
  | .one, n    => n
  | .A, .one   => .A
  | .A, .A      => .A
  | .A, .M      => .AM
  | .A, .AM     => .AM
  | .M, .one   => .M
  | .M, .M      => .M
  | .M, .A      => .AM
  | .M, .AM     => .AM
  | .AM, .one   => .AM
  | .AM, .A     => .AM
  | .AM, .M     => .AM
  | .AM, .AM    => .AM

instance : Bot UANaiveSemiring where
  bot := .bot

@[grind =] theorem UANaiveSemiring.bot_eq :
    (⊥ : UANaiveSemiring) = .bot := rfl

instance : Zero UANaiveSemiring where
  zero := .zero

@[grind =] theorem UANaiveSemiring.zero_eq :
    (0 : UANaiveSemiring) = .zero := rfl

instance : One UANaiveSemiring where
  one := .one

@[grind =] theorem UANaiveSemiring.one_eq :
    (1 : UANaiveSemiring) = .one := rfl

instance : Add UANaiveSemiring where
  add := seq

@[grind =] theorem UANaiveSemiring.hadd_eq (a b : UANaiveSemiring) :
    a + b = seq a b := rfl

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

instance : Monoid UANaiveMonoid where
  one := .one
  mul := mul

  mul_assoc := by native_decide
  one_mul := by native_decide
  mul_one := by native_decide

instance : ModeTheory UANaiveMonoid UANaiveSemiring where
  ε := .one
  act := act

  act_mul := by native_decide
  act_one := by native_decide

  bot_act := by native_decide
  zero_act := by native_decide

  act_inf := by native_decide
  act_seq_monotone := by native_decide
