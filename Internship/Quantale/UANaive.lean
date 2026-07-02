import Internship.Quantale.Base
open Base

namespace QUANaive

@[grind cases]
inductive UANaiveSemiring where
  |     top
  |     zero
  |      A
  |  one
  |          AM
  |      M
  |     bot
  deriving DecidableEq, Repr, Fintype

@[grind]
def meet : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | n, .top    => n
  | .top, n    => n
  | .zero, n   => n
  | n, .zero   => n
  | .A, n      => n
  | n, .A      => n
  | .one, .one => .one
  | .one, .AM  => .M
  | .AM, .one  => .M
  | .AM, .AM   => .AM
  | .bot, _    => .bot
  | _, .bot    => .bot
  | .M, _      => .M
  | _, .M      => .M

@[grind]
def seq : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | .top, _   => .top
  | _, .top   => .top
  | .zero, n  => n
  | n, .zero  => n
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
  | .bot, _   => .bot
  | _, .bot   => .bot

@[grind]
def scale : UANaiveSemiring → UANaiveSemiring → UANaiveSemiring
  | .top, _   => .top
  | .zero, n  => match n with
    | .top => .top
    | _ => .zero
  | .one, n   => n
  | .A, n     => match n with
    | .bot => .bot
    | .zero => .zero
    | .A => .A
    | .one => .A
    | .AM => .AM
    | .M => .AM
    | .top => .top
  | .M, n     => match n with
    | .top => .top
    | .zero => .zero
    | .A => .AM
    | .one => .M
    | .AM => .AM
    | .M => .M
    | .bot => .bot
  | .AM, n    => match n with
    | .top => .top
    | .zero => .zero
    | .A => .AM
    | .one => .AM
    | .AM => .AM
    | .M => .AM
    | .bot => .bot
  | .bot, n   => match n with
    | .top => .top
    | .zero => .zero
    | _ => .bot

instance : Top UANaiveSemiring where
  top := .top

@[grind =] theorem UANaiveSemiring.top_eq :
    (⊤ : UANaiveSemiring) = .top := rfl

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

instance : Quantale UANaiveSemiring where
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

instance : Mode UANaiveSemiring where
  scale := scale

  scale_assoc := by simp [LE.le]; native_decide
  scale_top := by native_decide
  top_scale := by native_decide
  scale_zero := by native_decide
  zero_scale := by native_decide
  scale_one := by native_decide
  one_scale := by native_decide
  scale_meet := by native_decide
  meet_scale := by native_decide
  scale_seq := by simp [LE.le]; native_decide
  seq_scale := by simp [LE.le]; native_decide

lemma join_seq : ∀ a b c : UANaiveSemiring,
    (a ⊔ b) + c = (a + c) ⊔ (b + c) := by native_decide

lemma seq_join : ∀ a b c : UANaiveSemiring,
    a + (b ⊔ c) = (a + b) ⊔ (a + c) := by native_decide

lemma scale_leq_join : ∀ (a b : UANaiveSemiring),
    scale a b ≤ a ⊔ b := by native_decide

lemma div_scale : ∀ (a b c : UANaiveSemiring),
    (a ≤ scale b c ↔ CompleteMode.div a b ≤ c) := by native_decide

lemma div_one : ∀ (a b : UANaiveSemiring),
    CompleteMode.div a b ≤ 1 ↔ a ≤ b := by native_decide

inductive Many where | default

instance : Modality Many UANaiveSemiring where
  box n _ := match n with
  | .top => .top
  | .zero => .zero
  | .A => .AM
  | .one => .M
  | .AM => .AM
  | .M => .M
  | .bot => .bot

  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind

instance : Comonadic Many UANaiveSemiring where
  box_dec := by
    simp [LE.le, UANaiveSemiring.hmin_eq, Modality.box]
    grind
  box_idem := by simp [Modality.box]; grind

inductive Aliased where | default

instance : Modality Aliased UANaiveSemiring where
  box n _ := match n with
  | .bot => .bot
  | .zero => .zero
  | .A => .A
  | .one => .A
  | .AM => .AM
  | .M => .AM
  | .top => .top

  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind

instance : Monadic Aliased UANaiveSemiring where
  box_inc := by
    simp [LE.le, UANaiveSemiring.hmin_eq, Modality.box]
    grind
  box_idem := by simp [Modality.box]; grind

end QUANaive
