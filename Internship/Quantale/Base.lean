import Mathlib

namespace Base

class Quantale (α : Type*)
    extends Bot α, Zero α, Min α, Add α where

  inf_assoc : ∀ a b c : α, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)
  inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a
  inf_idem : ∀ a : α, a ⊓ a = a
  inf_zero : ∀ a : α, a ⊓ ⊥ = ⊥
  zero_inf : ∀ a : α, ⊥ ⊓ a = ⊥

  seq_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  zero_seq : ∀ a : α, 0 + a = a
  seq_zero : ∀ a : α, a + 0 = a
  bot_seq : ∀ a : α, ⊥ + a = ⊥
  seq_bot : ∀ a : α, a + ⊥ = ⊥

  seq_inf : ∀ a b c : α,
    a + (b ⊓ c) = (a + b) ⊓ (a + c)

  inf_seq : ∀ a b c : α,
    (a ⊓ b) + c = (a + c) ⊓ (b + c)

class ModeTheory (α : Type*) (β : Type*)
    extends Monoid α, Quantale β where

  ε : β
  act : α → β → β

  act_mul : ∀ (a b : α) (c : β), act a (act b c) = act (a * b) c
  act_one : ∀ b : β, act 1 b = b

  bot_act : ∀ a : α, act a ⊥ = ⊥
  zero_act : ∀ a : α, act a 0 = 0

  act_inf : ∀ (a : α) (b c : β),
    act a (b ⊓ c) = act a b ⊓ act a c
  act_seq_monotone : ∀ (a : α) (b c : β),
    act a (b + c) ⊓ (act a b) + (act a c) = (act a b) + (act a c)
