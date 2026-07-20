import Internship.Quantale.Base
open Base
open Nat

namespace NatOmega


@[grind cases]
inductive ℕω where
  | nat : ℕ → ℕω
  | ω : ℕω
  deriving DecidableEq, Repr

@[grind]
def meet : ℕω → ℕω → ℕω 
  | .ω, .ω => .ω
  | .ω, .nat n => .nat n
  | .nat n, .ω => .nat n
  | .nat n1, .nat n2 => .nat (n1 ⊓ n2)

@[grind]
def seq : ℕω → ℕω → ℕω
  | .ω, _ => .ω
  | _, .ω => .ω
  | .nat n1, .nat n2 => .nat (n1 + n2)

@[grind]
def scale : ℕω → ℕω → ℕω
  | .ω, _ => .ω
  | _, .ω => .ω
  | .nat n1, .nat n2 => .nat (n1 * n2)


instance : Top ℕω where
  top := .ω

@[grind =] theorem ℕω.top_eq :
    (⊤ : ℕω) = .ω := rfl

instance : Zero ℕω where
  zero := .nat 0

@[grind =] theorem ℕω.zero_eq :
    (0 : ℕω) = .nat 0 := rfl

instance : One ℕω where
  one := .nat 1

@[grind =] theorem ℕω.one_eq :
    (1 : ℕω) = .nat 1 := rfl

instance : Add ℕω where
  add := seq

@[grind =] theorem ℕω.hadd_eq (a b : ℕω) :
    a + b = seq a b := rfl

instance : Min ℕω where
  min := meet

@[grind =] theorem ℕω.hmin_eq (a b : ℕω) :
    a ⊓ b = meet a b := rfl


instance : Quantale ℕω where
  meet_assoc := by grind
  meet_comm := by grind
  meet_idem := by grind
  meet_top := by grind
  top_meet := by grind

  seq_assoc := by grind
  zero_seq := by grind
  seq_zero := by grind
  top_seq := by grind
  seq_top := by grind

  seq_meet := by grind
  meet_seq := by grind


theorem Nat.mul_min_left (a b c : ℕ) : a * (b ⊓ c) = a * b ⊓ a * c := by
  rcases le_total b c with h | h
  rw [min_eq_left h, min_eq_left (mul_le_mul_right h a)]
  rw [min_eq_right h, min_eq_right (mul_le_mul_right h a)]

theorem Nat.mul_min_right (a b c : ℕ) : (a ⊓ b) * c = a * c ⊓ b * c := by
  rcases le_total a b with h | h
  rw [min_eq_left h, min_eq_left (mul_le_mul_left h c)]
  rw [min_eq_right h, min_eq_right (mul_le_mul_left h c)]


instance : Mode ℕω where
  scale := scale

  scale_assoc := by grind [Nat.mul_assoc]
  scale_top := by grind
  top_scale := by grind
  scale_zero := by grind
  zero_scale := by grind
  scale_one := by grind
  one_scale := by grind

  scale_meet := by grind [Nat.mul_min_left]
  meet_scale := by grind [Nat.mul_min_right]
  scale_seq := by grind
  seq_scale := by grind [Nat.add_mul]


@[grind]
def div : ℕω → ℕω → ℕω
  | .ω, _ => .ω
  | _, .ω => .nat 0
  | .nat n1, .nat n2 => .nat (n1 / n2)

instance : CompleteMode ℕω where
  div := div
  scale_div := by sorry  -- TODO
