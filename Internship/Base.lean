import Mathlib

namespace Base

class OrderedSemiring (α : Type*)
    extends Zero α, One α, Add α, Mul α, Min α where

  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a : α, a + 0 = a
  zero_add : ∀ a : α, 0 + a = a

  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
  zero_mul : ∀ a : α, 0 * a = 0
  mul_zero : ∀ a : α, a * 0 = 0

  inf_assoc : ∀ a b c : α, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)
  inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a
  inf_idem : ∀ a : α, a ⊓ a = a

  mul_add : ∀ a b c : α,
    a * (b + c) = a * b + a * c

  add_mul : ∀ a b c : α,
    (a + b) * c = a * c + b * c

  mul_inf : ∀ a b c : α,
    a * (b ⊓ c) = a * b ⊓ a * c

  inf_mul : ∀ a b c : α,
    (a ⊓ b) * c = a * c ⊓ b * c

  add_inf : ∀ a b c : α,
    a + (b ⊓ c) = (a + b) ⊓ (a + c)

  inf_add : ∀ a b c : α,
    (a ⊓ b) + c = (a + c) ⊓ (b + c)

instance [OrderedSemiring α] : LE α where
  le a b := a ⊓ b = a
