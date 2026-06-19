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

instance [Quantale α] : Std.Commutative (α := α) (· ⊓ ·) := ⟨meet_comm⟩
instance [Quantale α] : Std.Associative (α := α) (· ⊓ ·) := ⟨meet_assoc⟩
instance [Quantale α] : Std.Associative (α := α) (· + ·) := ⟨seq_assoc⟩

instance [Quantale α] : Preorder α where
  le a b := a ⊓ b = a
  le_refl := by simp [meet_idem]
  le_trans := by
    intro a b c h1 h2
    rw [←h1,←h2]
    simp [meet_assoc, meet_idem]

instance [Quantale α] [DecidableEq α] : DecidableRel (α := α) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a ⊓ b = a))

class CompleteQuantale (α : Type*)
    extends Quantale α, Max α, Bot α where

  join_assoc : ∀ a b c : α, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  join_comm : ∀ a b : α, a ⊔ b = b ⊔ a
  join_idem : ∀ a : α, a ⊔ a = a
  join_bot : ∀ a : α, a ⊔ ⊥ = a
  bot_join : ∀ a : α, ⊥ ⊔ a = a

  -- seq_join : ∀ a b c : α,
    -- a + (b ⊔ c) = (a + b) ⊔ (a + c)

  -- join_seq : ∀ a b c : α,
    -- (a ⊔ b) + c = (a + c) ⊔ (b + c)

open CompleteQuantale

instance [CompleteQuantale α] : Std.Commutative (α := α) (· ⊔ ·) := ⟨join_comm⟩
instance [CompleteQuantale α] : Std.Associative (α := α) (· ⊔ ·) := ⟨join_assoc⟩

class Mode (α : Type*)
    extends Quantale α, One α where

  scale : α → α → α

  scale_assoc : ∀ (a b c : α), b = ⊤ ∨
    scale a (scale b c) ≥ scale (scale a b) c
  scale_top : ∀ a : α, scale a ⊤ = ⊤
  top_scale : ∀ a : α, scale ⊤ a = a
  scale_zero : ∀ a : α, scale a 0 = 0
  zero_scale : ∀ a : α, a = ⊤ ∨ scale 0 a = 0
  scale_one : ∀ a : α, a = ⊤ ∨ scale a 1 = a
  one_scale : ∀ a : α, scale 1 a = a

  scale_meet : ∀ (a b c : α),
    scale a (b ⊓ c) = scale a b ⊓ scale a c
  meet_scale : ∀ (a b c : α), a = ⊤ ∨ b = ⊤ ∨
    scale (a ⊓ b) c = scale a c ⊓ scale b c
  scale_seq : ∀ (a b c : α),
    scale a (b + c) ≥ (scale a b) + (scale a c)
  seq_scale : ∀ (a b c : α), a = ⊤ ∨ b = ⊤ ∨
    scale (a + b) c ≤ (scale a c) + (scale b c)

open Mode

class CompleteMode (α : Type*)
    extends Mode α, CompleteQuantale α where

  div : α → α → α

  scale_div : ∀ (a b c : α), b = 0 ∨ (scale b c ≤ a ↔ c ≤ div a b)

open CompleteMode

class Modality (α : Type*) (β : Type*) [Mode β] where

  box : β → α → β

  zero_box : ∀ a : α, box 0 a = 0
  top_box : ∀ a : α, box ⊤ a = ⊤
  meet_box : ∀ (a : α) (b c : β),
    box (b ⊓ c) a = box b a ⊓ box c a
  seq_box : ∀ (a : α) (b c : β),
    box (b + c) a = box b a + box c a

open Modality

class Comonadic (α : Type*) (β : Type*) [Mode β]
    extends Modality α β where

  box_dec : ∀ (a : α) (b : β), box b a ≤ b
  box_idem : ∀ (a : α) (b : β), box (box b a) a = box b a

class Monadic (α : Type*) (β : Type*) [Mode β]
    extends Modality α β where

  box_inc : ∀ (a : α) (b : β), box b a ≥ b
  box_idem : ∀ (a : α) (b : β), box (box b a) a = box b a

-- Lemmas

theorem box_monotone {α β} [Mode β] [Modality α β] (a : α) (b c : β) :
    b ≤ c → box b a ≤ box c a := by
    simp [LE.le]
    intro h
    simp [←meet_box,h]

-- Meet-semilattice lemmas

theorem meet_le_left [Quantale α] (a b : α) : a ⊓ b ≤ a := by
  show (a ⊓ b) ⊓ a = a ⊓ b
  rw [meet_assoc, meet_comm b a, ← meet_assoc, meet_idem]

theorem meet_le_right [Quantale α] (a b : α) : a ⊓ b ≤ b := by
  rw [meet_comm]; exact meet_le_left b a

theorem le_meet [Quantale α] {a b c : α} (h1 : c ≤ a) (h2 : c ≤ b) : c ≤ a ⊓ b := by
  show c ⊓ (a ⊓ b) = c
  rw [← meet_assoc, show c ⊓ a = c from h1, show c ⊓ b = c from h2]

theorem le_antisymm' [Quantale α] {a b : α} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  have h1' : a ⊓ b = a := h1
  have h2' : b ⊓ a = b := h2
  rw [meet_comm] at h2'
  exact h1'.symm.trans h2'

theorem le_top [Quantale α] (a : α) : a ≤ ⊤ := by
  show a ⊓ ⊤ = a; exact meet_top a

-- Fold lemmas

theorem fold_le_of_mem [Quantale α] [DecidableEq α] (s : Finset α) {x : α} (hx : x ∈ s) :
    s.fold Min.min ⊤ id ≤ x := by
  induction s using Finset.induction_on with
  | empty => simp at hx
  | insert _ _ hna ih =>
    rw [Finset.fold_insert hna]; simp only [id]
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact meet_le_left _ _
    · exact Preorder.le_trans _ _ _ (meet_le_right _ _) (ih hx')

theorem le_fold [Quantale α] [DecidableEq α] (s : Finset α) {y : α} (hy : ∀ x ∈ s, y ≤ x) :
    y ≤ s.fold Min.min ⊤ id := by
  induction s using Finset.induction_on with
  | empty => exact le_top y
  | insert _ _ hna ih =>
    rw [Finset.fold_insert hna]; simp only [id]
    exact le_meet
      (hy _ (Finset.mem_insert_self _ _))
      (ih (fun x hx => hy x (Finset.mem_insert_of_mem hx)))

-- Instances

instance [Fintype α] [Quantale α] : Bot α where
  bot := Finset.univ.fold (· ⊓ ·) ⊤ id

instance [Fintype α] [Quantale α] [DecidableEq α] : Max α where
  max a b := (Finset.univ.filter fun x => a ≤ x ∧ b ≤ x).fold (· ⊓ ·) ⊤ id

-- Helper: ⊥ ≤ a for all a
theorem bot_le [Fintype α] [Quantale α] [DecidableEq α] (a : α) : ⊥ ≤ a :=
  fold_le_of_mem Finset.univ (Finset.mem_univ a)

-- Helper: a ≤ a ⊔ b
theorem le_join_left [Fintype α] [Quantale α] [DecidableEq α] (a b : α) : a ≤ a ⊔ b := by
  apply le_fold
  intro x hx
  exact (Finset.mem_filter.mp hx).2.1

theorem le_join_right [Fintype α] [Quantale α] [DecidableEq α] (a b : α) : b ≤ a ⊔ b := by
  apply le_fold
  intro x hx
  exact (Finset.mem_filter.mp hx).2.2

-- Helper: if a ≤ c and b ≤ c then a ⊔ b ≤ c
theorem join_le [Fintype α] [Quantale α] [DecidableEq α] {a b c : α}
    (h1 : a ≤ c) (h2 : b ≤ c) : a ⊔ b ≤ c := by
  apply fold_le_of_mem
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩

instance [Fintype α] [Quantale α] [DecidableEq α] : CompleteQuantale α where
  join_assoc := by
    intro a b c
    apply le_antisymm'
    · -- (a ⊔ b) ⊔ c ≤ a ⊔ (b ⊔ c)
      apply join_le
      · apply join_le
        · exact le_join_left a (b ⊔ c)
        · exact Preorder.le_trans _ _ _ (le_join_left b c) (le_join_right a (b ⊔ c))
      · exact Preorder.le_trans _ _ _ (le_join_right b c) (le_join_right a (b ⊔ c))
    · -- a ⊔ (b ⊔ c) ≤ (a ⊔ b) ⊔ c
      apply join_le
      · exact Preorder.le_trans _ _ _ (le_join_left a b) (le_join_left (a ⊔ b) c)
      · apply join_le
        · exact Preorder.le_trans _ _ _ (le_join_right a b) (le_join_left (a ⊔ b) c)
        · exact le_join_right (a ⊔ b) c
  join_comm  := by simp [max, And.comm]
  join_idem  := by
    intro a
    apply le_antisymm'
    · exact join_le (Preorder.le_refl a) (Preorder.le_refl a)
    · exact le_join_left a a
  join_bot   := by
    intro a
    apply le_antisymm'
    · exact join_le (Preorder.le_refl a) (bot_le a)
    · exact le_join_left a ⊥
  bot_join   := by
    intro a
    apply le_antisymm'
    · exact join_le (bot_le a) (Preorder.le_refl a)
    · exact le_join_right ⊥ a

instance [Fintype α] [DecidableEq α] [Mode α] : CompleteMode α where
  div a b := (Finset.univ.filter fun x => scale b x ≤ a).fold (· ⊔ ·) ⊥ id

  scale_div := by sorry

-- Modalities

inductive Id where | default

instance [Mode α] : Modality Id α where
  box a _ := a

  zero_box := by simp
  top_box := by simp
  meet_box := by simp
  seq_box := by simp

instance [Mode α] : Comonadic Id α where
  box_dec := by simp [box]
  box_idem := by simp [box]

instance [Mode α] : Monadic Id α where
  box_inc := by simp [box]
  box_idem := by simp [box]

inductive Comp (α1 α2 : Type*)
| comp : α1 → α2 → Comp α1 α2

instance [Mode β] [Modality α1 β] [Modality α2 β] : Modality (Comp α1 α2) β where
  box := λ b (.comp a1 a2) => box (box b a1) a2

  top_box := by simp [top_box]
  zero_box := by simp [zero_box]
  meet_box := by simp [meet_box]
  seq_box := by simp [seq_box]

end Base
