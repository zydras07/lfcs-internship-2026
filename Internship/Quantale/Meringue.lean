-- A quantale for baking a lemon meringue pie
--   https://math.ucr.edu/home/baez/act_course/lecture_25.html
--
-- The meringue theory contains a quantale that defines
-- which ingredients combine into which other ones.
-- We have .stuff i1 >= .stuff i2 if there is some way
-- to combine the ingredients in i1 to get the ingredients in i2.
-- The theory is first-order and has no sensible multiplication.
--
-- To obtain a higher-order theory, we include affine functions.
-- An affine function may contain ingredients, while a regular function may not.
--
-- This is an example of a theory where 1*s = s, but s*1 /= s.
-- We have 1 = affine, and let s,s1,s2 be some ingredients.
-- Assume that s + s = s*1 + s*1 <= s * (1 + 1) = s * many
-- We can not choose s * many = s + s, as many = 1 + 1 + 1.
-- This restricts us to s = 0 or s = top;
-- and both choices break other parts of the theory.
--
--
-- Other papers:
--  https://math.ucr.edu/home/baez/act_course/lecture_18.html
--  https://dl.acm.org/doi/pdf/10.1145/3326938.3326940
--  https://arxiv.org/pdf/1803.05316 (Chapter 2)
--  https://arxiv.org/pdf/1504.03661
--  https://arxiv.org/pdf/1409.5531

import Internship.Quantale.Base
open Base

namespace Meringue

@[grind cases]
inductive Ingredients where
  | crust
  | lemon
  | butter
  | sugar
  | egg
  | yolk
  | white
  | filling
  | meringue
  | lemonPie
  | meringuePie
  deriving DecidableEq, Repr, Fintype

-- [yolk]+[white]≤[egg]
-- [lemon filling]≤[lemon]+[butter]+[sugar]+[yolk]
-- [lemon pie]≤[crust]+[filling]
-- [meringue]≤[white]+[sugar]
-- [meringue pie]≤[lemon pie]+[meringue]

@[grind, simp]
def mix : Multiset Ingredients → Multiset Ingredients :=
  fun s => s

@[grind cases]
inductive MeringueSemiring where
  |       top
  |       zero
  |           stuff : (i : Multiset Ingredients) -> (pi : ∃ a,  a ∈ i) -> MeringueSemiring
  |  one
  |  many
  |       bot
  deriving DecidableEq

@[grind, simp]
def meet : MeringueSemiring → MeringueSemiring → MeringueSemiring
  | .top, n    => n
  | n, .top    => n
  | .zero, n   => n
  | n, .zero   => n
  | .bot, _    => .bot
  | _, .bot    => .bot
  | .one, .one => .one
  | .one, .many => .many
  | .many, .one => .many
  | .many, .many => .many
  | .stuff s1 p1, .stuff s2 p2 => .stuff (mix (s1 ∪ s2))
      (by cases p1 with | intro a h => exists a; simp [mix,h])
  | .stuff _ _, .one => .bot
  | .one, .stuff _ _ => .bot
  | .stuff _ _, .many => .bot
  | .many, .stuff _ _ => .bot

@[grind, simp]
def seq : MeringueSemiring → MeringueSemiring → MeringueSemiring
  | .top, _    => .top
  | _, .top    => .top
  | .zero, n   => n
  | n, .zero   => n
  | .bot, _    => .bot
  | _, .bot    => .bot
  | .one, .one => .many
  | .one, .many => .many
  | .many, .one => .many
  | .many, .many => .many
  | .stuff s1 p1, .stuff s2 p2 => .stuff (mix (s1 + s2))
      (by cases p1 with | intro a h => exists a; simp [mix,h])
  | .stuff s1 _, _ => .bot
  | _, .stuff s2 _ => .bot

@[grind, simp]
def scale : MeringueSemiring → MeringueSemiring → MeringueSemiring
  | .top, _    => .top
  | _, .top    => .top
  | .zero, _   => .zero
  | _, .zero   => .zero
  | .bot, _    => .bot
  | _, .bot    => .bot
  | .one, n    => n
  | .many, .one  => .many
  | .many, .many => .many
  | .many, .stuff _ _ => .bot
  | .stuff _ _, _ => .bot

instance : Top MeringueSemiring where
  top := .top

@[grind =, simp] theorem MeringueSemiring.top_eq :
    (⊤ : MeringueSemiring) = .top := rfl

instance : Zero MeringueSemiring where
  zero := .zero

@[grind =, simp] theorem MeringueSemiring.zero_eq :
    (0 : MeringueSemiring) = .zero := rfl

instance : One MeringueSemiring where
  one := .one

@[grind =, simp] theorem MeringueSemiring.one_eq :
    (1 : MeringueSemiring) = .one := rfl

instance : Add MeringueSemiring where
  add := seq

@[grind =, simp] theorem MeringueSemiring.hadd_eq (a b : MeringueSemiring) :
    a + b = seq a b := rfl

@[simp]
instance : Min MeringueSemiring where
  min := meet

@[grind =,simp] theorem MeringueSemiring.hmin_eq (a b : MeringueSemiring) :
    a ⊓ b = meet a b := rfl

lemma multiset_union_assoc {α} [DecidableEq α] : ∀ (s1 s2 s3 : Multiset α),
    s1 ∪ (s2 ∪ s3) = (s1 ∪ s2) ∪ s3 := sorry -- somehow this is not in mathlib?

instance : Quantale MeringueSemiring where
  meet_assoc := by
    intros a b c; cases a <;> cases b <;> cases c <;> simp [multiset_union_assoc]
  meet_comm := by
    intros a b; cases a <;> cases b <;> simp [Multiset.union_comm]
  meet_idem := by
    intros a; cases a <;> simp [Multiset.eq_union_left]
  meet_top := by intro a; cases a <;> simp
  top_meet := by simp

  seq_assoc := by
    intros a b c; cases a <;> cases b <;> cases c <;> simp [Multiset.add_assoc]
  zero_seq := by intro a; cases a <;> simp
  seq_zero := by intro a; cases a <;> simp
  top_seq := by simp
  seq_top := by intro a; cases a <;> simp

  seq_meet := by
    intros a b c; cases a <;> cases b <;> cases c <;> try simp
    simp [Multiset.eq_union_left]
    simp [Multiset.eq_union_right]
    simp [Multiset.eq_union_left]
    simp [Multiset.add_union_distrib]
  meet_seq := by
    intros a b c; cases a <;> cases b <;> cases c <;> try simp
    simp [Multiset.eq_union_right]
    simp [Multiset.eq_union_right]
    simp [Multiset.eq_union_left]
    simp [Multiset.union_add_distrib]

instance : Mode MeringueSemiring where
  scale := scale

  scale_assoc := by
    intros a b c; cases a <;> cases b <;> cases c <;> simp
  scale_top := by intro a; cases a <;> simp
  top_scale := by simp
  scale_zero := by intro a; cases a <;> simp
  zero_scale := by intro a; cases a <;> simp
  scale_one := by sorry -- not possible to prove, see above
  one_scale := by intro a; cases a <;> simp

  scale_meet := by
    intros a b c; cases a <;> cases b <;> cases c <;> simp
  meet_scale := by
    intros a b c; cases a <;> cases b <;> cases c <;> simp [Multiset.eq_union_left]
  scale_seq := by
    intros a b c; cases a <;> cases b <;> cases c <;> try simp
  seq_scale := by
    intros a b c; cases a <;> cases b <;> cases c <;> try simp
    simp [LE.le]
