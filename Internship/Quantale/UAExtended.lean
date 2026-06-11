import Internship.Quantale.Base
open Base

namespace QUAExtended

@[grind cases]
inductive UAExtendedSemiring where
  |          bot
  |          zero
  |           A
  |       one
  |               AM
  |             M
  |     CA
  |          CAM
  |          CAb
  |          top
  deriving DecidableEq, Repr, Fintype

open UAExtendedSemiring

@[grind]
def add : UAExtendedSemiring → UAExtendedSemiring → UAExtendedSemiring
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
  | CA, _    => top
  | CAM, _   => top
  | CAb, _   => top
  | _, CA    => top
  | _, CAM   => top
  | _, CAb   => top

@[grind]
def act : UAExtendedSemiring → UAExtendedSemiring → UAExtendedSemiring
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

  | CA, CA   => CA
  | CA, CAM  => CAM
  | CA, M    => CAM
  | CA, A    => A
  | CA, AM   => AM
  | CAM, A   => AM
  | CAM, AM  => AM
  | CAM, M   => CAM

  | A, CA    => CA
  | A, CAM   => CAM
  | CAb, A   => AM
  | CAb, AM  => AM

  | CAM, CA  => CAb
  | CAM, CAM => CAb
  | M, CA    => CAb
  | AM, CA   => CAb
  | M, CAM   => CAb
  | AM, CAM  => CAb
  | CAb, _   => CAb
  | _, CAb   => CAb

@[grind]
def meet : UAExtendedSemiring → UAExtendedSemiring → UAExtendedSemiring
  | top, n => n
  | n, top => n
  | CAb, n => n
  | n, CAb => n
  | CAM, n => n
  | n, CAM => n
  | bot, _ => bot
  | _, bot => bot
  | zero, _ => zero
  | _, zero => zero
  | A, _ => A
  | _, A => A
  | one, AM => A
  | AM, one => A
  | CA, AM => A
  | AM, CA => A
  | CA, M => one
  | M, CA => one
  | one, _ => one
  | _, one => one
  | AM, _ => AM
  | _, AM => AM
  | CA, _ => CA
  | M, _ => M

instance : Bot UAExtendedSemiring where
  bot := bot

@[grind =] theorem UAExtendedSemiring.bot_eq :
    (⊥ : UAExtendedSemiring) = bot := rfl

instance : Zero UAExtendedSemiring where
  zero := zero

@[grind =] theorem UAExtendedSemiring.zero_eq :
    (0 : UAExtendedSemiring) = zero := rfl

instance : One UAExtendedSemiring where
  one := one

@[grind =] theorem UAExtendedSemiring.one_eq :
    (1 : UAExtendedSemiring) = one := rfl

instance : Add UAExtendedSemiring where
  add := add

@[grind =] theorem UAExtendedSemiring.hadd_eq (a b : UAExtendedSemiring) :
    a + b = add a b := rfl

instance : Min UAExtendedSemiring where
  min := meet

@[grind =] theorem UAExtendedSemiring.hmin_eq (a b : UAExtendedSemiring) :
    a ⊓ b = meet a b := rfl

instance : LE UAExtendedSemiring where
  le a b := a ⊓ b = a

@[grind =] theorem UAExtendedSemiring.hle_eq (a b : UAExtendedSemiring) :
    (a ≤ b) = (a ⊓ b = a) := rfl

instance : Quantale UAExtendedSemiring where
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

instance : Action UAExtendedSemiring where
  act := act

  act_one := by native_decide
  one_act := by native_decide

  act_inf := by native_decide
  inf_act := by native_decide

  act_seq_monotone := by native_decide

theorem left_residual (q r : UAExtendedSemiring) :
    (act .CA r) ≤ q ↔ r ≤ (act .A q) := by grind
