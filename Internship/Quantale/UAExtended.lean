import Internship.Quantale.Base
open Base

namespace QUAExtended

-- |
-- ({top, zero, bot} ∪ { A, U, M }^*) / { (MU, bot), (UA, A), (U, AU), (AM, MA), (UU, U), (AA, A), (MM, M) }

-- mode many with
--   many many = many
-- mode unique with
--   unique unique = unique
--   many unique = bottom
-- mode aliased with
--   aliased aliased = aliased
--   unique aliased = aliased
--   aliased unique = unique
--   many aliased = aliased many

@[grind cases]
inductive UAExtendedSemiring where
  |          top
  |          zero
  |           A
  |                AM
  |       one
  |              M
  |     CA
  |          CAM
  |          bot
  deriving DecidableEq, Repr, Fintype

@[grind]
def meet : UAExtendedSemiring → UAExtendedSemiring → UAExtendedSemiring
  | .top, n    => n
  | n, .top    => n
  | .zero, n   => n
  | n, .zero   => n
  | .A, n      => n
  | n, .A      => n
  | .one, .one => .one
  | .AM, .AM   => .AM
  | .one, .AM  => .M
  | .AM, .one  => .M
  | .M, .one   => .M
  | .one, .M   => .M
  | .AM, .M    => .M
  | .M, .AM    => .M
  | .M, .M     => .M
  | .one, .CA  => .CA
  | .CA, .one  => .CA
  | .CA, .CA   => .CA
  | .AM, .CA   => .CAM
  | .M, .CA    => .CAM
  | .CA, .M    => .CAM
  | .CA, .AM   => .CAM
  | .bot, _    => .bot
  | _, .bot    => .bot
  | .CAM, _    => .CAM
  | _, .CAM    => .CAM

@[grind]
def seq : UAExtendedSemiring → UAExtendedSemiring → UAExtendedSemiring
  | .top, _    => .top
  | _, .top    => .top
  | .bot, _    => .bot
  | _, .bot    => .bot
  | .zero, n   => n
  | n, .zero   => n
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
  | .CA, _     => .bot
  | .CAM, _    => .bot
  | _, .CA     => .bot
  | _, .CAM    => .bot

instance : Top UAExtendedSemiring where
  top := .top

@[grind =] theorem UAExtendedSemiring.top_eq :
    (⊤ : UAExtendedSemiring) = .top := rfl

instance : Zero UAExtendedSemiring where
  zero := .zero

@[grind =] theorem UAExtendedSemiring.zero_eq :
    (0 : UAExtendedSemiring) = .zero := rfl

instance : One UAExtendedSemiring where
  one := .one

@[grind =] theorem UAExtendedSemiring.one_eq :
    (1 : UAExtendedSemiring) = .one := rfl

instance : Add UAExtendedSemiring where
  add := seq

@[grind =] theorem UAExtendedSemiring.hadd_eq (a b : UAExtendedSemiring) :
    a + b = seq a b := rfl

instance : Min UAExtendedSemiring where
  min := meet

@[grind =] theorem UAExtendedSemiring.hmin_eq (a b : UAExtendedSemiring) :
    a ⊓ b = meet a b := rfl

instance : Quantale UAExtendedSemiring where
  meet_assoc := by native_decide
  meet_comm := by native_decide
  meet_idem := by native_decide
  meet_top := by native_decide
  top_meet := by native_decide

  seq_assoc := by native_decide
  zero_seq := by native_decide
  seq_zero := by native_decide
  top_seq := by native_decide
  seq_top := by native_decide

  seq_meet := by native_decide
  meet_seq := by native_decide

inductive Many where | many

instance : Modality Many UAExtendedSemiring where
  box n _ := match n with
  | .top => .top
  | .zero => .zero
  | .A => .AM
  | .one => .M
  | .AM => .AM
  | .M => .M
  | .CA => .CAM
  | .CAM => .CAM
  | .bot => .bot

  lock _ m := match m with
  | .top => .top
  | .zero => .zero
  | .A => .AM
  | .one => .M
  | .AM => .AM
  | .M => .M
  | .CA => .bot
  | .CAM => .bot
  | .bot => .bot

  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind

  lock_top := by grind
  lock_zero := by grind
  lock_meet := by grind
  lock_seq_monotone := by grind

  box_lock_assoc := by grind

instance : Comonadic Many UAExtendedSemiring where
  lock_dec := by
    simp [LE.le, UAExtendedSemiring.hmin_eq, Modality.lock]
    grind
  lock_idem := by simp [Modality.lock]; grind
  box_dec := by
    simp [LE.le, UAExtendedSemiring.hmin_eq, Modality.box]
    grind
  box_idem := by simp [Modality.box]; grind

inductive Aliased where | aliased

instance : Modality Aliased UAExtendedSemiring where
  box n _ := match n with
  | .top => .top
  | .zero => .zero
  | .A => .A
  | .one => .A
  | .AM => .AM
  | .M => .AM
  | .CA => .CA
  | .CAM => .CAM
  | .bot => .bot

  lock _ m := match m with
  | .top => .top
  | .zero => .zero
  | .A => .A
  | .one => .A
  | .AM => .AM
  | .M => .AM
  | .CA => .CA
  | .CAM => .CAM
  | .bot => .bot

  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind

  lock_top := by grind
  lock_zero := by grind
  lock_meet := by grind
  lock_seq_monotone := by grind

  box_lock_assoc := by grind

instance : Monadic Aliased UAExtendedSemiring where
  lock_inc := by
    simp [LE.le, UAExtendedSemiring.hmin_eq, Modality.lock]
    grind
  lock_idem := by simp [Modality.lock]; grind
  box_inc := by
    simp [LE.le, UAExtendedSemiring.hmin_eq, Modality.box]
    grind
  box_idem := by simp [Modality.box]; grind

inductive Unique where | unique

instance : Modality Unique UAExtendedSemiring where
  box n _ := match n with
  | .top => .top
  | .zero => .zero
  | .A => .CA
  | .one => .CA
  | .AM => .bot
  | .M => .bot
  | .CA => .CA
  | .CAM => .bot
  | .bot => .bot

  lock _ m := match m with
  | .top => .top
  | .zero => .zero
  | .A => .A
  | .one => .CA
  | .AM => .AM
  | .M => .CAM
  | .CA => .CA
  | .CAM => .CAM
  | .bot => .bot

  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind

  lock_top := by grind
  lock_zero := by grind
  lock_meet := by grind
  lock_seq_monotone := by
    simp [LE.le, UAExtendedSemiring.hmin_eq]
    grind

  box_lock_assoc := by grind

instance : Comonadic Unique UAExtendedSemiring where
  lock_dec := by
    simp [LE.le, UAExtendedSemiring.hmin_eq, Modality.lock]
    grind
  lock_idem := by simp [Modality.lock]; grind
  box_dec := by
    simp [LE.le, UAExtendedSemiring.hmin_eq, Modality.box]
    grind
  box_idem := by simp [Modality.box]; grind

theorem right_residual_lock (q r : UAExtendedSemiring) :
    Modality.lock Aliased.aliased q ≤ r ↔ q ≤ Modality.lock Unique.unique r := by
    simp [LE.le, UAExtendedSemiring.hmin_eq, Modality.lock]
    grind

instance : Distributive Many Aliased UAExtendedSemiring where
  swap_box_lock := by simp [Modality.lock, Modality.box]; grind
  swap_lock_box := by simp [Modality.lock, Modality.box]; grind

instance : Distributive Aliased Many UAExtendedSemiring where
  swap_box_lock := by simp [Modality.lock, Modality.box]; grind
  swap_lock_box := by simp [Modality.lock, Modality.box]; grind

instance : Distributive Aliased Unique UAExtendedSemiring where
  swap_box_lock := by simp [Modality.lock, Modality.box]; grind
  swap_lock_box := by simp [LE.le, Modality.lock, Modality.box]; grind

instance : Distributive Unique Aliased UAExtendedSemiring where
  swap_box_lock := by simp [LE.le, Modality.lock, Modality.box]; grind
  swap_lock_box := by simp [Modality.lock, Modality.box]; grind

instance : Distributive Many Unique UAExtendedSemiring where
  swap_box_lock := by simp [Modality.lock, Modality.box]; grind
  swap_lock_box := by simp [Modality.lock, Modality.box]; grind

instance : Distributive Unique Many UAExtendedSemiring where
  swap_box_lock := by simp [Modality.lock, Modality.box]; grind
  swap_lock_box := by simp [Modality.lock, Modality.box]; grind
