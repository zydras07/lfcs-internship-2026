import Internship.Quantale.Base
open Base

namespace QUAExtended

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

@[grind]
def scale : UAExtendedSemiring → UAExtendedSemiring → UAExtendedSemiring
  | .top, _    => .top
  | .zero, n   => match n with
    | .top => .top
    | _ => .zero
  | .one, n    => n
  | .M, n      => match n with
    | .top => .top
    | .zero => .zero
    | .A => .AM
    | .one => .M
    | .AM => .AM
    | .M => .M
    | .CA => .bot
    | .CAM => .bot
    | .bot => .bot
  | .A, n      => match n with
    | .top => .top
    | .zero => .zero
    | .A => .A
    | .one => .A
    | .AM => .AM
    | .M => .AM
    | .CA => .CA
    | .CAM => .CAM
    | .bot => .bot
  | .AM, n      => match n with
    | .top => .top
    | .zero => .zero
    | .A => .AM
    | .one => .AM
    | .AM => .AM
    | .M => .AM
    | .CA => .bot
    | .CAM => .bot
    | .bot => .bot
  | .CA, n     => match n with
    | .top => .top
    | .zero => .zero
    | .A => .A
    | .one => .CA
    | .AM => .AM
    | .M => .CAM
    | .CA => .CA
    | .CAM => .CAM
    | .bot => .bot
  | .CAM, n    => match n with
    | .top => .top
    | .zero => .zero
    | .A => .AM
    | .one => .CAM
    | .AM => .AM
    | .M => .CAM
    | .CA => .bot
    | .CAM => .bot
    | .bot => .bot
  | .bot, n    => match n with
    | .top => .top
    | .zero => .zero
    | _ => .bot

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

instance : Mode UAExtendedSemiring where
  scale := scale

  scale_assoc := by simp [LE.le]; native_decide
  scale_top := by native_decide
  top_scale := by native_decide
  scale_zero := by native_decide
  zero_scale := by native_decide
  scale_one := by native_decide
  one_scale := by native_decide

  scale_meet := by native_decide
  meet_scale := by grind
  scale_seq := by simp [LE.le]; native_decide
  seq_scale := by simp [LE.le]; native_decide

theorem right_residual_scale (q r : UAExtendedSemiring) :
  Mode.scale .A q ≤ r ↔ q ≤ Mode.scale .CA r := by
    simp [LE.le, UAExtendedSemiring.hmin_eq, Mode.scale]
    grind

lemma join_seq : ∀ a b c : UAExtendedSemiring,
    (a ⊔ b) + c = (a + c) ⊔ (b + c) := by native_decide

lemma seq_join : ∀ a b c : UAExtendedSemiring,
    a + (b ⊔ c) = (a + b) ⊔ (a + c) := by native_decide

lemma scale_join : ∀ (a b : UAExtendedSemiring),
    scale a b ≤ a ⊔ b := by native_decide

lemma scale_residual_div : ∀ (a b c : UAExtendedSemiring),
    (a ≤ scale b c ↔ CompleteMode.div a b ≤ c) := by native_decide

lemma div_one : ∀ (a b : UAExtendedSemiring),
    (CompleteMode.div a b ≤ 1 ↔ a ≤ b) := by native_decide

lemma scale_div : ∀ (a b : UAExtendedSemiring),
    a ≤ scale b (CompleteMode.div a b) := by native_decide

lemma div_scale : ∀ (a b : UAExtendedSemiring),
    a ≥ CompleteMode.div (scale b a) b := by native_decide

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

  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind

instance : Comonadic Many UAExtendedSemiring where
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

  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind

instance : Monadic Aliased UAExtendedSemiring where
  box_inc := by
    simp [LE.le, UAExtendedSemiring.hmin_eq, Modality.box]
    grind
  box_idem := by simp [Modality.box]; grind

#eval scale .AM (scale .CA .A)
#eval (scale .AM .CA)

-- counter-examples:
--  Law 7: q1 = aliased many, q2 = unique, q3 = aliased
--  Law 8: q1 = unique, q2 = many, q3 = aliased
--  Law 9: q1 = unique, q2 = aliased, q3 = aliased

-- theorem  scale_assoc : ∀ (a b c : UAExtendedSemiring), b = ⊤ ∨
    -- scale a (scale b c) ≤ scale (scale a b) c := by simp [LE.le]; grind
-- theorem scale_seq : ∀ (a b c : UAExtendedSemiring), b = 1 ∨ (b = .M) ∨ c = 1 ∨ (c = .M) ∨
    -- scale a (b + c) ≤ (scale a b) + (scale a c) := by simp [LE.le]; grind
-- theorem seq_scale : ∀ (a b c : UAExtendedSemiring), a = ⊤ ∨ b = ⊤ ∨
    -- scale (a + b) c ≥ (scale a c) + (scale b c) := by simp [LE.le]; grind
