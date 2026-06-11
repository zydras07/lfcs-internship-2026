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


class Action (α : Type*)
    extends Quantale α, One α where

  act : α → α → α

  act_one : ∀ a : α, act 1 a = a
  one_act : ∀ a : α, act a 1 = a

  act_inf : ∀ (a : α) (b c : α),
    act a (b ⊓ c) = act a b ⊓ act a c

  inf_act : ∀ (a b : α) (c : α),
    act (a ⊓ b) c = act a c ⊓ act b c

  act_seq_monotone : ∀ (a : α) (b c : α),
    act a (b + c) ⊓ (act a b) + (act a c) = (act a b) + (act a c)
