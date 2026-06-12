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

class Comonadic (α : Type*) (β : Type*) [Quantale β]
    extends Modality α β where

  lock_dec : ∀ (a : α) (b : β), lock a b ≤ b
  box_dec : ∀ (a : α) (b : β), box b a ≤ b

class Monadic (α : Type*) (β : Type*) [Quantale β]
    extends Modality α β where

  lock_inc : ∀ (a : α) (b : β), lock a b ≥ b
  box_inc : ∀ (a : α) (b : β), box b a ≥ b

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

instance [Quantale α] : Comonadic Id α where
  lock_dec := by simp [lock]
  box_dec := by simp [box]

instance [Quantale α] : Monadic Id α where
  lock_inc := by simp [lock]
  box_inc := by simp [box]

inductive Comp (α1 α2 : Type*)
| comp : α1 → α2 → Comp α1 α2

instance [Quantale β] [Modality α1 β] [Modality α2 β] : Modality (Comp α1 α2) β where
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
    intro (.comp a1 a2) b c
    have h1 := lock_seq_monotone a1 (lock a2 b) (lock a2 c)
    have h2 := lock_monotone a1 _ _ (lock_seq_monotone a2 b c)
    exact (le_trans h1 h2)

instance [Quantale β]  [Comonadic α1 β] [Comonadic α2 β] : Comonadic (Comp α1 α2) β where
  lock_dec := by
    intro (.comp a1 a2) b
    exact (le_trans (Comonadic.lock_dec a1 _) (Comonadic.lock_dec a2 b))
  box_dec := by
    intro (.comp a1 a2) b
    exact (le_trans (Comonadic.box_dec a2 _) (Comonadic.box_dec a1 b))

instance [Quantale β]  [Monadic α1 β] [Monadic α2 β] : Monadic (Comp α1 α2) β where
  lock_inc := by
    intro (.comp a1 a2) b
    exact (le_trans (Monadic.lock_inc a2 b) (Monadic.lock_inc a1 _))
  box_inc := by
    intro (.comp a1 a2) b
    exact (le_trans (Monadic.box_inc a1 b) (Monadic.box_inc a2 _))

end Base
