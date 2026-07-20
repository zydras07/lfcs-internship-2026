import Internship.Quantale.Base
open Base
open Nat

namespace Combined


@[grind cases]
inductive CombinedMode where
  | top
  | zero 
  | one
  | at
  | one_plus
  | ω
  deriving DecidableEq, Repr, Fintype


@[grind]
def meet : CombinedMode → CombinedMode → CombinedMode 
  | .top, n => n
  | n, .top => n
  | .ω, _ => .ω
  | _, .ω => .ω
  | .at, .one_plus => .ω
  | .one_plus, .at => .ω
  | .at, _ => .at
  | _, .at => .at
  | .one_plus, .one_plus => .one_plus
  | .one_plus, .zero => .ω
  | .one_plus, .one => .one_plus
  | .zero, .one_plus => .ω
  | .zero, .zero => .zero
  | .zero, .one => .at
  | .one, .one_plus => .one_plus
  | .one, .zero => .at
  | .one, .one => .one

@[grind]
def seq : CombinedMode → CombinedMode → CombinedMode
  | .top, _ => .top
  | _, .top => .top
  | .one_plus, _ => .one_plus
  | _, .one_plus => .one_plus
  | .zero, n => n
  | n, .zero => n
  | .one, _ => .one_plus
  | _, .one => .one_plus
  | .at, _ => .ω 
  | _, .at => .ω 
  | .ω, .ω => .ω

@[grind]
def scale : CombinedMode → CombinedMode → CombinedMode
  | .top, _ => .top
  | _, .top => .top
  | .zero, _ => .zero
  | _, .zero => .zero
  | .ω, _ => .ω
  | _, .ω => .ω
  | .at, .one_plus => .ω 
  | .one_plus, .at => .ω 
  | .at, _ => .at
  | _, .at => .at
  | .one_plus, _ => .one_plus
  | _, .one_plus => .one_plus
  | .one, .one => .one


instance : Top CombinedMode where
  top := .top

@[grind =] theorem CombinedMode.top_eq :
    (⊤ : CombinedMode) = .top := rfl

instance : Zero CombinedMode where
  zero := .zero

@[grind =] theorem CombinedMode.zero_eq :
    (0 : CombinedMode) = .zero := rfl

instance : One CombinedMode where
  one := .one

@[grind =] theorem CombinedMode.one_eq :
    (1 : CombinedMode) = .one := rfl

instance : Add CombinedMode where
  add := seq

@[grind =] theorem CombinedMode.hadd_eq (a b : CombinedMode) :
    a + b = seq a b := rfl

instance : Min CombinedMode where
  min := meet

@[grind =] theorem CombinedMode.hmin_eq (a b : CombinedMode) :
    a ⊓ b = meet a b := rfl


instance : Quantale CombinedMode where
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


instance : Mode CombinedMode where
  scale := scale

  scale_assoc := by native_decide
  scale_top := by native_decide
  top_scale := by native_decide
  scale_zero := by native_decide
  zero_scale := by native_decide
  scale_one := by native_decide
  one_scale := by native_decide

  scale_meet := by native_decide
  meet_scale := by native_decide
  scale_seq := by native_decide
  seq_scale := by native_decide


inductive Zero where | zero

instance : Modality Zero CombinedMode where
  box n _ := scale n .zero
  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind
  box_scale := by sorry

inductive One where | one

instance : Modality One CombinedMode where
  box n _ := scale n .one
  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind
  box_scale := by sorry

inductive At where | at

instance : Modality At CombinedMode where
  box n _ := scale n .at
  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind
  box_scale := by sorry

inductive Ω where | ω

instance : Modality Ω CombinedMode where
  box n _ := scale n .ω
  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind
  box_scale := by sorry

inductive OnePlus where | one_plus

instance : Modality OnePlus CombinedMode where
  box n _ := scale n .one_plus
  zero_box := by grind
  top_box := by grind
  meet_box := by grind
  seq_box := by grind
  box_scale := by sorry
