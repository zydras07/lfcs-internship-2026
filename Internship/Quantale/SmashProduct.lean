import Internship.Quantale.Base
open Base

namespace SmashProduct

class SmashableQuantale (α : Type*) extends Quantale α where
  zero_deconstruct_add : ∀ {a b : α}, a ≠ 0 → b ≠ 0 → a + b ≠ 0
  top_deconstruct_add : ∀ {a b : α}, a ≠ ⊤ → b ≠ ⊤ → a + b ≠ ⊤
  zero_deconstruct_meet : ∀ {a b : α}, a ≠ 0 → b ≠ 0 → a ⊓ b ≠ 0
  top_deconstruct_meet : ∀ {a b : α}, a ≠ ⊤ → b ≠ ⊤ → a ⊓ b ≠ ⊤

@[grind cases]
inductive QuantaleSmash α β [SmashableQuantale α] [SmashableQuantale β] where
  | top 
  | zero
  | pair : (a : α) → (a ≠ Top.top ∧ a ≠ Zero.zero)
         → (b : β) → (b ≠ Top.top ∧ b ≠ Zero.zero) 
         → QuantaleSmash α β

@[grind]
def meet [SmashableQuantale α] [SmashableQuantale β] : QuantaleSmash α β → QuantaleSmash α β → QuantaleSmash α β 
  | .top, n => n
  | n, .top => n
  | .zero, n => n
  | n, .zero => n
  | .pair x1 px1 y1 py1, .pair x2 px2 y2 py2 => 
    .pair (x1 ⊓ x2) (And.intro (SmashableQuantale.top_deconstruct_meet px1.left px2.left) 
                               (SmashableQuantale.zero_deconstruct_meet px1.right px2.right)) 
          (y1 ⊓ y2) (And.intro (SmashableQuantale.top_deconstruct_meet py1.left py2.left)
                               (SmashableQuantale.zero_deconstruct_meet py1.right py2.right))

@[grind]
def seq [SmashableQuantale α] [SmashableQuantale β] : QuantaleSmash α β → QuantaleSmash α β → QuantaleSmash α β 
  | .top, _ => .top
  | _, .top => .top
  | .zero, n => n
  | n, .zero => n
  | .pair x1 px1 y1 py1, .pair x2 px2 y2 py2 => 
    .pair (x1 + x2) (And.intro (SmashableQuantale.top_deconstruct_add px1.left px2.left) 
                               (SmashableQuantale.zero_deconstruct_add px1.right px2.right)) 
          (y1 + y2) (And.intro (SmashableQuantale.top_deconstruct_add py1.left py2.left)
                               (SmashableQuantale.zero_deconstruct_add py1.right py2.right))

instance [SmashableQuantale α] [SmashableQuantale β] : Top (QuantaleSmash α β) where
  top := .top

@[simp, grind =] theorem QuantaleSmash.top_eq [SmashableQuantale α] [SmashableQuantale β] :
    (⊤ : QuantaleSmash α β) = .top := rfl

instance [SmashableQuantale α] [SmashableQuantale β] : Zero (QuantaleSmash α β) where
  zero := .zero

@[simp, grind =] theorem QuantaleSmash.zero_eq [SmashableQuantale α] [SmashableQuantale β] :
    (0 : QuantaleSmash α β) = .zero := rfl


instance [SmashableQuantale α] [SmashableQuantale β] : Min (QuantaleSmash α β) where
  min := meet

@[simp, grind =] theorem QuantaleSmash.hmin_eq [SmashableQuantale α] [SmashableQuantale β] (a b : QuantaleSmash α β) :
    a ⊓ b = meet a b := rfl

instance [SmashableQuantale α] [SmashableQuantale β] : Add (QuantaleSmash α β) where
  add := seq

@[simp, grind =] theorem QuantaleSmash.hadd_eq [SmashableQuantale α] [SmashableQuantale β] (a b : QuantaleSmash α β) :
    a + b = seq a b := rfl

instance [SmashableQuantale α] [SmashableQuantale β] : Quantale (QuantaleSmash α β) where
  meet_assoc := by grind
  meet_comm := by grind
  meet_idem := by grind [Quantale.meet_idem]
  meet_top := by grind
  top_meet := by grind

  seq_assoc := by grind
  zero_seq := by grind
  seq_zero := by grind
  top_seq := by grind
  seq_top := by grind

  seq_meet := by grind [Quantale.seq_meet]
  meet_seq := by grind [Quantale.meet_seq]
