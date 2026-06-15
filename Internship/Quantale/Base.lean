import Mathlib

namespace Base

class Quantale (α : Type*)
    extends Top α, Zero α, Min α, Add α where

  meet_assoc : ∀ a b c : α, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)
  meet_comm : ∀ a b : α, a ⊓ b = b ⊓ a
  meet_idem : ∀ a : α, a ⊓ a = a
  meet_top : ∀ a : α, a ⊓ ⊤ = a
  top_meet : ∀ a : α, ⊤ ⊓ a = a

  seq_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  zero_seq : ∀ a : α, 0 + a = a
  seq_zero : ∀ a : α, a + 0 = a
  top_seq : ∀ a : α, ⊤ + a = ⊤
  seq_top : ∀ a : α, a + ⊤ = ⊤

  seq_meet : ∀ a b c : α,
    a + (b ⊓ c) = (a + b) ⊓ (a + c)

  meet_seq : ∀ a b c : α,
    (a ⊓ b) + c = (a + c) ⊓ (b + c)

open Quantale

instance [Quantale α] : Preorder α where
  le a b := a ⊓ b = a
  le_refl := by simp [meet_idem]
  le_trans := by
    intro a b c h1 h2
    rw [←h1,←h2]
    simp [meet_assoc, meet_idem]

class Modality (α : Type*) (β : Type*) [Quantale β] where

  box : β → α → β
  lock : α → β → β

  zero_box : ∀ a : α, box 0 a = 0
  top_box : ∀ a : α, box ⊤ a = ⊤
  meet_box : ∀ (a : α) (b c : β),
    box (b ⊓ c) a = box b a ⊓ box c a
  seq_box : ∀ (a : α) (b c : β),
    box (b + c) a = box b a + box c a

  lock_top : ∀ a : α, lock a ⊤ = ⊤
  lock_zero : ∀ a : α, lock a 0 = 0
  lock_meet : ∀ (a : α) (b c : β),
    lock a (b ⊓ c) = lock a b ⊓ lock a c
  lock_seq_monotone : ∀ (a : α) (b c : β),
    lock a (b + c) ≥ (lock a b) + (lock a c)

  box_lock_assoc : ∀ (a1 a2 : α) (b : β),
    box (lock a1 b) a2 ≤ lock a1 (box b a2)

open Modality

theorem lock_monotone {α β} [Quantale β] [Modality α β] (a : α) (b c : β) :
    b ≤ c → lock a b ≤ lock a c := by
    simp [LE.le]
    intro h
    simp [←lock_meet,h]

theorem box_monotone {α β} [Quantale β] [Modality α β] (a : α) (b c : β) :
    b ≤ c → box b a ≤ box c a := by
    simp [LE.le]
    intro h
    simp [←meet_box,h]

class Distributive (α1 α2 : Type*) (β : Type*)
    [Quantale β] [Modality α1 β] [Modality α2 β] where
  swap_box_lock : ∀ (a1 : α1) (a2 : α2) (b : β),
    box (lock a1 b) a2 ≤ lock a1 (box b a2)
  swap_lock_box : ∀ (a1 : α1) (a2 : α2) (b : β),
    lock a2 (box b a1) ≥ box (lock a2 b) a1

instance swap_refl [Quantale β] [Modality α β] : Distributive α α β where
  swap_box_lock := by simp [box_lock_assoc]
  swap_lock_box := by simp [box_lock_assoc]

class Comonadic (α : Type*) (β : Type*) [Quantale β]
    extends Modality α β where

  lock_dec : ∀ (a : α) (b : β), lock a b ≤ b
  lock_idem : ∀ (a : α) (b : β), lock a (lock a b) = lock a b
  box_dec : ∀ (a : α) (b : β), box b a ≤ b
  box_idem : ∀ (a : α) (b : β), box (box b a) a = box b a

class Monadic (α : Type*) (β : Type*) [Quantale β]
    extends Modality α β where

  lock_inc : ∀ (a : α) (b : β), lock a b ≥ b
  lock_idem : ∀ (a : α) (b : β), lock a (lock a b) = lock a b
  box_inc : ∀ (a : α) (b : β), box b a ≥ b
  box_idem : ∀ (a : α) (b : β), box (box b a) a = box b a

inductive Id where | default

instance [Quantale α] : Modality Id α where
  box a _ := a
  lock _ a := a

  zero_box := by simp
  top_box := by simp
  meet_box := by simp
  seq_box := by simp

  lock_top := by simp
  lock_zero := by simp
  lock_meet := by simp
  lock_seq_monotone := by simp

  box_lock_assoc := by simp

instance [Quantale α] : Comonadic Id α where
  lock_dec := by simp [lock]
  lock_idem := by simp [lock]
  box_dec := by simp [box]
  box_idem := by simp [box]

instance [Quantale α] : Monadic Id α where
  lock_inc := by simp [lock]
  lock_idem := by simp [lock]
  box_inc := by simp [box]
  box_idem := by simp [box]

inductive Comp (α1 α2 : Type*)
| comp : α1 → α2 → Comp α1 α2

instance [Quantale β] [Modality α1 β] [Modality α2 β] [Distributive α1 α2 β] : Modality (Comp α1 α2) β where
  box := λ b (.comp a1 a2) => box (box b a1) a2
  lock := λ (.comp a1 a2) b => lock a1 (lock a2 b)

  top_box := by simp [top_box]
  zero_box := by simp [zero_box]
  meet_box := by simp [meet_box]
  seq_box := by simp [seq_box]

  lock_top := by simp [lock_top]
  lock_zero := by simp [lock_zero]
  lock_meet := by simp [lock_meet]
  lock_seq_monotone := by
    intro (.comp a1 a2) b c; simp
    apply (le_trans (lock_seq_monotone a1 (lock a2 b) (lock a2 c)))
    apply (lock_monotone a1)
    exact (lock_seq_monotone a2 b c)

  box_lock_assoc := by
    intro (.comp a1 a2) (.comp a3 a4) b
    simp
    apply (le_trans (box_monotone a4 _ _ (box_lock_assoc a1 a3 _)))
    apply (le_trans (Distributive.swap_box_lock a1 a4 _))
    apply (lock_monotone a1)
    apply (le_trans (box_monotone a4 _ _ (Distributive.swap_lock_box a3 a2 _)))
    apply (le_trans (box_lock_assoc _ _ _))
    exact (le_refl _)

end Base
