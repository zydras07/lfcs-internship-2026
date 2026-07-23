import Internship.Quantale.Base
open Base

namespace QUAStandard

@[grind cases]
inductive UAStandardSemiring where
  |          top
  |          zero
  |           A
  |                AM
  |     CA
  |          CAM
  |          bot
  deriving DecidableEq, Repr, Fintype

@[simp, grind]
def meet : UAStandardSemiring → UAStandardSemiring → UAStandardSemiring
  | .top, n    => n
  | n, .top    => n
  | .zero, n   => n
  | n, .zero   => n
  | .A, n      => n
  | n, .A      => n
  | .AM, .AM   => .AM
  | .CA, .CA   => .CA
  | .AM, .CA   => .CAM
  | .CA, .AM   => .CAM
  | .bot, _    => .bot
  | _, .bot    => .bot
  | .CAM, _    => .CAM
  | _, .CAM    => .CAM

@[simp, grind]
def seq : UAStandardSemiring → UAStandardSemiring → UAStandardSemiring
  | .top, _    => .top
  | _, .top    => .top
  | .bot, _    => .bot
  | _, .bot    => .bot
  | .zero, n   => n
  | n, .zero   => n
  | .A, .A     => .AM
  | .A, .AM    => .AM
  | .AM, .A    => .AM
  | .AM, .AM   => .AM
  | .CA, _     => .bot
  | .CAM, _    => .bot
  | _, .CA     => .bot
  | _, .CAM    => .bot

@[simp, grind]
def scale : UAStandardSemiring → UAStandardSemiring → UAStandardSemiring
  | .top, _    => .top
  | .zero, n   => match n with
    | .top => .top
    | _ => .zero
  | .A, n      => match n with
    | .top => .top
    | .zero => .zero
    | .A => .A
    | .AM => .AM
    | .CA => .CA
    | .CAM => .CAM
    | .bot => .bot
  | .AM, n      => match n with
    | .top => .top
    | .zero => .zero
    | .A => .AM
    | .AM => .AM
    | .CA => .bot
    | .CAM => .bot
    | .bot => .bot
  | .CA, n     => match n with
    | .top => .top
    | .zero => .zero
    | .A => .A
    | .AM => .AM
    | .CA => .CA
    | .CAM => .CAM
    | .bot => .bot
  | .CAM, n    => match n with
    | .top => .top
    | .zero => .zero
    | .A => .AM
    | .AM => .AM
    | .CA => .bot
    | .CAM => .bot
    | .bot => .bot
  | .bot, n    => match n with
    | .top => .top
    | .zero => .zero
    | _ => .bot

instance : Top UAStandardSemiring where
  top := .top

@[simp, grind =] theorem UAStandardSemiring.top_eq :
    (⊤ : UAStandardSemiring) = .top := rfl

instance : Zero UAStandardSemiring where
  zero := .zero

@[simp, grind =] theorem UAStandardSemiring.zero_eq :
    (0 : UAStandardSemiring) = .zero := rfl

instance : One UAStandardSemiring where
  one := .A

@[simp, grind =] theorem UAStandardSemiring.one_eq :
    (1 : UAStandardSemiring) = .A := rfl

instance : Add UAStandardSemiring where
  add := seq

@[simp, grind =] theorem UAStandardSemiring.hadd_eq (a b : UAStandardSemiring) :
    a + b = seq a b := rfl

instance : Min UAStandardSemiring where
  min := meet

@[simp, grind =] theorem UAStandardSemiring.hmin_eq (a b : UAStandardSemiring) :
    a ⊓ b = meet a b := rfl

instance : Quantale UAStandardSemiring where
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

instance : Mode UAStandardSemiring where
  scale := scale

  scale_assoc := by simp [LE.le]; native_decide
  scale_top := by native_decide
  top_scale := by native_decide
  scale_zero := by native_decide
  zero_scale := by native_decide
  scale_one := by sorry
  one_scale := by native_decide

  scale_meet := by native_decide
  meet_scale := by grind
  scale_seq := by simp [LE.le]; native_decide
  seq_scale := by simp [LE.le]; native_decide

theorem right_residual_scale (q r : UAStandardSemiring) :
  Mode.scale .A q ≤ r ↔ q ≤ Mode.scale .CA r := by
    simp [LE.le, UAStandardSemiring.hmin_eq, Mode.scale]
    grind

lemma join_seq : ∀ a b c : UAStandardSemiring,
    (a ⊔ b) + c = (a + c) ⊔ (b + c) := by native_decide

lemma seq_join : ∀ a b c : UAStandardSemiring,
    a + (b ⊔ c) = (a + b) ⊔ (a + c) := by native_decide

lemma scale_join : ∀ (a b : UAStandardSemiring),
    scale a b ≤ a ⊔ b := by native_decide

open CompleteMode

lemma scale_residual_div : ∀ (a b c : UAStandardSemiring),
    (a ≤ scale b c ↔ div a b ≤ c) := by native_decide

lemma scale_div : ∀ (a b : UAStandardSemiring),
    a ≤ scale b (div a b) := by native_decide

lemma div_scale : ∀ (a b : UAStandardSemiring),
    a ≥ div (scale b a) b := by native_decide

lemma add_div : ∀ (a b q : UAStandardSemiring),
    ((div a q) + (div b q) ≥ div (a + b) q) := by native_decide

lemma scale_seq_eq : ∀ (a b c : UAStandardSemiring),
    scale a (b + c) = (scale a b) + (scale a c) := by grind

lemma div_eq_top : ∀ (a b : UAStandardSemiring),
    (div a b = ⊤ → a = ⊤) := by native_decide

-- lemma split_add : ∀ (a b c : UAStandardSemiring),
    -- a + b ≥ c → ∃ d e, c = d + e ∧ a ≥ d ∧ b ≥ e := by
    -- intros a b c h;
    -- cases ha : a <;> cases hb : b <;> cases hc : c <;>
      -- (first | rw [ha,hb,hc] at h; contradiction
             -- | exists a, b; rw [ha,hb]; decide
             -- | exists 0, c; rw [hc]; decide
             -- | exists c, 0; rw [hc]; decide
             -- | exists .AM, .AM; rw [hc]; decide
             -- | skip)
    -- exists 0, c; rw [hc]; decide

-- -- #eval scale .AM (scale .CA .A)
-- #eval (scale .AM .CA)

-- counter-examples:
--  Law 7: q1 = aliased many, q2 = unique, q3 = aliased
--  Law 8: q1 = unique, q2 = many, q3 = aliased
--  Law 9: q1 = unique, q2 = aliased, q3 = aliased

-- theorem  scale_assoc : ∀ (a b c : UAStandardSemiring), b = ⊤ ∨
    -- scale a (scale b c) ≤ scale (scale a b) c := by simp [LE.le]; grind
-- theorem scale_seq : ∀ (a b c : UAStandardSemiring), b = 1 ∨ (b = .M) ∨ c = 1 ∨ (c = .M) ∨
    -- scale a (b + c) ≤ (scale a b) + (scale a c) := by simp [LE.le]; grind
-- theorem seq_scale : ∀ (a b c : UAStandardSemiring), a = ⊤ ∨ b = ⊤ ∨
    -- scale (a + b) c ≥ (scale a c) + (scale b c) := by simp [LE.le]; grind

inductive Many where | many

instance : Modality Many UAStandardSemiring where
  box n _ := match n with
  | .zero => .zero
  | .A => .AM
  | .AM => .AM
  | .CA => .CAM
  | .CAM => .CAM
  | .bot => .bot

  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind
  box_scale a b c := by simp [Mode.scale]; grind

instance : Comonadic Many UAStandardSemiring where
  box_dec := by
    simp [LE.le, UAStandardSemiring.hmin_eq, Modality.box]
    grind
  box_idem := by simp [Modality.box]; grind

inductive Aliased where | aliased

instance : Modality Aliased UAStandardSemiring where
  box n _ := match n with
  | .zero => .zero
  | .A => .A
  | .AM => .AM
  | .CA => .A
  | .CAM => .AM
  | .bot => .bot

  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box a b c := by simp [LE.le]; grind
  box_scale a b c := by simp [Mode.scale, LE.le]; grind

instance : Monadic Aliased UAStandardSemiring where
  box_inc := by
    simp [LE.le, UAStandardSemiring.hmin_eq, Modality.box]
    grind
  box_idem := by simp [Modality.box]; grind

lemma aliased_box : ∀ (a : UAStandardSemiring),
  Modality.box a (.aliased : Aliased) = scale a .A := by
    intro a; cases a <;> simp [Modality.box, scale]

lemma scale_box_many : ∀ (a b : UAStandardSemiring), ∃ (c : UAStandardSemiring),
  scale (Modality.box a (.many : Many)) b = scale a c := by native_decide

lemma scale_box_aliased : ∀ (a b : UAStandardSemiring), ∃ (c : UAStandardSemiring),
  scale (Modality.box a (.aliased : Aliased)) b = scale a c := by native_decide

lemma meet_split : ∀ (a b c : UAStandardSemiring),
  c ≤ a ⊓ b ↔ c ≤ a ∧ c ≤ b := by native_decide

@[grind]
def pre_star (a : UAStandardSemiring) (fuel : ℕ) : UAStandardSemiring :=
  match fuel with
  | 0 => a
  | Nat.succ n => 0 ⊓ (a + (pre_star a n))

def star a := pre_star a 5

theorem test1 : ∀ a b : UAStandardSemiring,
  star (a + b) ≥ star a + star b := by native_decide

theorem test2 : ∀ a b : UAStandardSemiring,
  star (scale a b) ≥ scale (star a) b := by native_decide

@[grind]
def pre_exp (a : UAStandardSemiring) (b : UAStandardSemiring) (fuel : ℕ) : UAStandardSemiring :=
  match fuel with
  | 0 => a
  | Nat.succ n => a + (scale b (pre_exp a b n))

def exp a b := pre_exp a b 5

theorem test3 : ∀ a b c : UAStandardSemiring,
  exp (a + b) c = exp a c + exp b c := by native_decide

theorem test4 : ∀ a b c : UAStandardSemiring,
  exp (scale a b) c ≥ scale (exp a c) b := by native_decide
