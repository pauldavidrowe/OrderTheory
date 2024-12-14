/-
Copyright (c) 2024 Paul D. Rowe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul D. Rowe
-/
import OrderTheory.Exercises01
import Mathlib.Order.Sublattice
import Mathlib.Order.Ideal
import Mathlib.Data.Set.Card
import Mathlib.Order.Height
import Mathlib.Order.RelClasses
import Mathlib.Data.Finset.Lattice.Fold

open scoped Classical

variable {P Q ι X L K : Type}
/-!
  # Chapter 2: Lattices and Complete Lattices

  We continue with notes on the text and the translation of the various concepts
  into Lean.
-/

/-!
  # Lattices as ordered sets

  This section is all about lattices which are essentially partial orders with
  some additional structure related to the existence of upper and lower bounds.
-/

/-!
  ## 2.1 Defintions

  Let `P` be a partial order and let `S ⊆ P` be a subset of `P`. An element
  `x ∈ P` is an upper bound of `S` if and only if for all `s ∈ S`, `s ≤ x`. A
  lower bound is natrually defined dually.

  I can't find a separate predicate in Mathlib to say `x` is an upper bound
  of a set `S`. But it does contain notation for the set of all upper (and lower)
  bounds of a set. These are denoted `upperBounds` and `lowerBounds` respectively.
  They each consume a set `S` and give back the set `{x | ∀ s ∈ S, s ≤ x}` (or dually
  for lower bounds). The text denotes these by `Sᵘ` and `Sˡ` respectively. I will
  introduce that notation for Lean, just to keep consistent.
-/

postfix:max "ᵘ" => upperBounds
postfix:max "ˡ" => lowerBounds

/-!
  Since `≤` is transitive, `Sᵘ` is always an upper set, and `Sˡ` always a lower set.
-/

theorem isUpperSet_upperBounds [PartialOrder P] (S : Set P) : IsUpperSet Sᵘ :=
  λ _ _ le mem _ smem ↦ (mem smem).trans le

theorem isLowerSet_lowerBounds [PartialOrder P] (S : Set P) : IsLowerSet Sˡ :=
  λ _ _ le mem _ smem ↦ le.trans (mem smem)

/-!
  If `Sᵘ` has a least element `x`, it is called the least upper bound of S. Mathlib
  expresses this as `IsLUB S x`. In fact, `IsLUB` is defined just as in the text, namely
  as the least element of `upperBounds`. The following formulation is equivalent:

  (i) `x` is an upper bound of `S` and

  (ii) for all upper bounds `y` of `S`, `x ≤ y`
-/

/-- This seems to be true essentially by definition in Mathlib -/
theorem IsLUB_iff [PartialOrder P] (S : Set P) {x : P} :
    IsLUB S x ↔ x ∈ Sᵘ ∧ ∀ {y}, y ∈ Sᵘ → x ≤ y := Eq.to_iff rfl

theorem IsGLB_iff [PartialOrder P] (S : Set P) {x : P} :
    IsGLB S x ↔ x ∈ Sˡ ∧ ∀ {y}, y ∈ Sˡ → y ≤ x := Eq.to_iff rfl

/-!
  The least upper bound of `S` exists if and only if there exists `x : P` such that
  `∀ y : P, ((∀ s ∈ S, s ≤ y) ↔ x ≤ y)`
-/

theorem exists_LUB_iff [PartialOrder P] (S : Set P) :
    (∃ x, IsLUB S x) ↔ ∃ x, ∀ y : P, ((∀ s ∈ S, s ≤ y) ↔ x ≤ y) := by
  constructor
  · intro ⟨x, lub⟩
    use x
    intro y
    constructor
    · exact λ h ↦ lub.2 h
    · exact λ le _ mem ↦ (lub.1 mem).trans le
  · intro ⟨x, h⟩
    use x
    constructor
    · intro s mem
      specialize h x
      simp only [le_refl, iff_true] at h
      exact h s mem
    · exact λ y mem ↦ (h y).mp mem

/-!
  Of course the greatest lower bound works dually. It is denoted `IsGLB S x` in Mathlib.

  The text uses the notation `⋁S` for the least upper bound of a set (\bigvee) and
  `⋀S` (\bigwedge) for the greatest lower bound when these exist. Mathlib uses `sSup` and
  `sInf` (set supremum and infimum) for these.
-/

/-!
  ## 2.2 Top and bottom

  It is easily seen that if `P` has a top element, then `Pᵘ = {⊤}` in which case
  `sSup P = ⊤`. When `P` has no top element `Pᵘ = ∅` so `sSup P` does not exist.
-/

lemma example_2_2a [PartialOrder P] [OrderTop P] :
    (Set.univ : Set P)ᵘ = {⊤} := by simp

lemma example_2_2b [SemilatticeSup P] [OrderTop P] :
    IsLUB (Set.univ : Set P) ⊤ := by exact ⟨by simp, by simp⟩

lemma example_2_2c [PartialOrder P] :
    (∅ : Set P)ᵘ = Set.univ := by simp

lemma example_2_2d [PartialOrder P] : (∃ x, IsLUB (∅ : Set P) x) ↔ ∃ b : P, ∀ p, b ≤ p := by
  constructor
  · intro ⟨b, hb⟩
    use b
    intro p
    exact hb.2 (by simp)
  · intro ⟨b, hb⟩
    use b
    constructor
    · simp
    · intro p _
      exact hb p

/-!
  ## 2.3 Notation

  For Mathlib, we can write `x ⊔ y` for the least upper bound of `x` and `y`
  as long as we have an instance `[SemilatticSup P]`. (We can actually write it
  as long as we have `[Sup P]` but that type class is for notation only and does
  not enforce the properties of least upper bounds.) Similarly, `x ⊓ y` is the
  greatest lower bound, or infimum of `x` and `y` as long as we have `[SemilatticInf P]`.

  As above, we must write `sSup S` and `sInf S` for the supremum and infimum of
  a set `S`. But again, we need an instance of `[SupSet P]` or `[InfSet P]` for those
  to even make sense. And if we want them to have the properties of supremum and
  infimum, we must have an instance `[CompleteSemilatticeSup P]` or
  `[CompleteSemilatticInf P]`.

  Finally, if we have an indexed family of elements of p, `{pᵢ : P | i ∈ ι}`,
  then this manifests in Mathlib as follows. The existence of this family is denoted
  `p : ι → P`, and we denote the supremum of the family by `⨆ i, p i`. As in all the
  cases above, this notation is unlocked by a typeclass, in this case `[SupSet P]`,
  and it only has the properties we want when we have an instance
  `[CompleteSemilatticeSup P]`. The corresponding dual notation is `⨅ i, p i` with
  all the expected caveats about type classes.

  Essentially, we can only really access the notations for sups and infs of pairs
  or sets if we have notation instances that tell us how such functions are defined. And they
  only have the meaning we want when we have instances of the relevant type classes.
  To put it another way, unless sup and inf are defined for all pairs (respectively
  all sets) then we should not be using the notation. This differs somewhat from the
  text which does use the notation `x ⊔ y` even if it only exists for that one pair.
-/

/-!
  ## 2.4 Definitions

  When both `x ⊔ y` and `x ⊓ y` exists for all pairs `x` and `y` in an partial order `P`
  then we call `P` a lattice. This is a type class in Mathlib: `[Lattice P]`. The text doesn't
  mention at this point structures for which only one or the other of `⊔` or `⊓` is defined
  for all pairs, but Mathlib has this built in. If `⊔` is defined for all pairs then
  we have an instance `[SemilatticeSup P]`. If it's `⊓` that is defined for all pairs
  then we use `[SemilatticeInf P]`.

  If the supremum and infimum exist for all subsets `S : P`, (i.e. `sSup S` and `sInf S`
  exist and have the properties of supremum and infimum) then `P` is called a complete
  lattice. This is written `[CompleteLattice P]` in Mathlib. The one-sided versions in which
  only sups or infs of all sets are defined are written `[CompleteSemilatticeSup P]` and
  `[CompleteSemilatticeInf P]`. The Mathlib definitions for these one-sided version state
  that they are rarely used because any one-sided version is actually a complete lattice.
  I expect this will be discussed in the text.
-/

/-!
  ## 2.5 Remarks on ⊔ and ⊓

  (1) If `(x : P) ≤ y` then `{x, y}ᵘ = ↑ᵖy` and `{x, y}ˡ = ↓ᵖx`. It follows that
      `x ⊔ y = y` and `x ⊓ y = x`. Setting `x = y` we see that `x ⊔ x = x` and
      `x ⊓ x = x`.
-/

lemma example_2_5_1a [PartialOrder P] {x y : P} (h : x ≤ y) : {x, y}ᵘ = ↑ᵖy ∧ {x, y}ˡ = ↓ᵖx := by
  constructor
  · ext p
    constructor <;> intro mem
    · simp_all
    · simp_all; exact h.trans mem
  · ext p
    constructor <;> intro mem
    · simp_all
    · simp_all; exact mem.trans h

lemma example_2_5_1b [Lattice P] {x y : P} (h : x ≤ y) : x ⊔ y = y ∧ x ⊓ y = x := by
  -- constructor
  -- · exact sup_of_le_right h
  -- · exact inf_of_le_left h
  simp_all only [ge_iff_le, sup_of_le_right, inf_of_le_left, and_self]

/-!
  (2) Nothing to formalize here. It's just noting that the `x ⊔ y` can fail to
      exist either because `{x, y}ᵘ` is empty or because it has no least element.

  (3) Nothing to formalize here either.

  (4) If `P` is a lattice, then for all `a`, `b`, `c`, `d`,

  (i) `a ≤ b` implies `a ⊔ c ≤ b ⊔ c` and `a ⊓ c ≤ b ⊓ c`

  (ii) `a ≤ b` and `c ≤ d` imply `a ⊔ c ≤ b ⊔ d` and `a ⊓ c ≤ b ⊓ d`.

  These must already be in Mathlib.
-/

lemma example_2_5_4i [Lattice P] {a b : P} (c : P) (hab : a ≤ b) :
    a ⊔ c ≤ b ⊔ c ∧ a ⊓ c ≤ b ⊓ c := by
  constructor
  · --exact sup_le_sup_right hab c
    have lea : a ≤ b ⊔ c := hab.trans le_sup_left
    have lec : c ≤ b ⊔ c := le_sup_right
    apply sup_le lea lec
  · --exact inf_le_inf_right c hab
    have lea : a ⊓ c ≤ b := inf_le_left.trans hab
    have lec : a ⊓ c ≤ c := inf_le_right
    apply le_inf lea lec

lemma example_2_5_4ii [Lattice P] {a b c d : P} (hab : a ≤ b) (hcd : c ≤ d) :
    a ⊔ c ≤ b ⊔ d ∧ a ⊓ c ≤ b ⊓ d := by
  constructor
  · --exact sup_le_sup hab hcd
    have lea : a ≤ b ⊔ d := hab.trans le_sup_left
    have lec : c ≤ b ⊔ d := hcd.trans le_sup_right
    exact sup_le lea lec
  · --exact inf_le_inf hab hcd
    exact le_inf (inf_le_left.trans hab) (inf_le_right.trans hcd)

lemma example_2_5_5 [Lattice P] {a b c : P} (hba : b ≤ a) (habc : a ≤ b ⊔ c) :
    a ⊔ c = b ⊔ c := by -- Follow proof in text
  have hbcc : c ⊔ (b ⊔ c) = b ⊔ c := by apply (example_2_5_1b (by simp)).1
  have h2 : b ⊔ c ≤ a ⊔ c := by apply (example_2_5_4i c hba).1
  have h3 : a ⊔ c ≤ c ⊔ (b ⊔ c) := by simp_all
  rw [hbcc] at h3
  exact le_le_iff_eq.mp ⟨h3, h2⟩

/-!
  ## 2.6 Examples

  (1) Every chain is a lattice. This is known to Mathlib as LinearOrder.toLattice.
      This has a bunch of observations about ℝ, ℚ, ℤ, ℕ that follow quite naturally
      and are quite intuitive.

  (2) For any type `X` the type of subsets of `X`, `Set X` is complete lattice under
      set inclusion. Mathlib seems to know this but I can't find where it is defined.

-/

lemma example_2_6_2a {A : ι → Set X} : ⨆ i, A i = ⋃ i, A i := rfl

lemma example_2_6_2b {A : ι → Set X} : ⨅ i, A i = ⋂ i, A i := rfl

/-!
  (3) If `𝔏 : Set (Set X)`, then `𝔏` is called a lattice of sets if it is
      closed under finite unions and intersections, and complete lattice if
      it is closed under arbitrary unions and intersections.
-/

def example_2_6_3a {X : Type} (𝔏 : Set (Set X))
    (hUnion : ∀ S T, S ∈ 𝔏 → T ∈ 𝔏 → S ∪ T ∈ 𝔏)
    (hInter : ∀ S T, S ∈ 𝔏 → T ∈ 𝔏 → S ∩ T ∈ 𝔏) :
    Lattice { S : Set X | S ∈ 𝔏} :=
  {
    sup := λ S T ↦ ⟨S ∪ T, hUnion S.val T.val S.property T.property⟩
    le_sup_left := by simp
    le_sup_right := by simp
    sup_le := by simp_all
    inf := λ S T ↦ ⟨S ∩ T, hInter S.val T.val S.property T.property⟩
    inf_le_left := by simp
    inf_le_right := by simp
    le_inf := by simp_all
  }

local instance example_2_6_3bSupSet (𝔏 : Set (Set X))
    (hUnion : ∀ (I : Set (Set X)), I ⊆ 𝔏 → ⋃ i : I, i ∈ 𝔏) :
    SupSet { S // S ∈ 𝔏} := ⟨λ I ↦ ⟨⋃ i : I, i, by specialize hUnion I; simp_all⟩⟩

local instance example_2_6_3bSup (𝔏 : Set (Set X))
    [SupSet { S : Set X // S ∈ 𝔏}] :
  Max { S : Set X // S ∈ 𝔏} := ⟨λ S T ↦ sSup {S, T}⟩

local instance example_2_6_3InfSet {X : Type} (𝔏 : Set (Set X))
    (hInter : ∀ (I : Set (Set X)), I ⊆ 𝔏 → ⋂ i : I, i ∈ 𝔏) :
    InfSet { S : Set X // S ∈ 𝔏} := ⟨λ I ↦ ⟨⋂ i : I, i, by specialize hInter I; simp_all⟩⟩

local instance example_2_6_3bInf (𝔏 : Set (Set X))
    [InfSet { S : Set X // S ∈ 𝔏}] :
  Min { S : Set X // S ∈ 𝔏} := ⟨λ S T ↦ sInf {S, T}⟩



/-- We only need to prove it's a complete semilattice with sup -/
def example_2_6_3b {X : Type} (𝔏 : Set (Set X))
    (hUnion : ∀ (I : Set (Set X)), I ⊆ 𝔏 → ⋃ i : I, i ∈ 𝔏)
    (_ : ∀ (I : Set (Set X)), I ⊆ 𝔏 → ⋂ i : I, i ∈ 𝔏) :
    CompleteSemilatticeSup { S : Set X // S ∈ 𝔏} :=
  {
    sSup := λ I ↦ ⟨⋃ i : I, i, by specialize hUnion I; simp_all⟩
    le_sSup := by
      intro s a mema x memx
      simp_all
      use ↑a
      refine' ⟨_, memx⟩
      use a.property
    sSup_le := by
      intro s a b x memx
      simp_all
      obtain ⟨i, ⟨⟨x', memi⟩, memx'⟩⟩ := memx
      specialize b _ _ memi
      exact b memx'
  }

lemma example_2_6_3c [PartialOrder P]
    (A : ι → Set P) (h : ∀ i, IsLowerSet (A i)) :
    IsLowerSet (⋃ i, A i) ∧ IsLowerSet (⋂ i, A i) := by
  constructor
  · intro a b le mem
    obtain ⟨Ai, hAi1, hAi2⟩ := mem
    use Ai, hAi1
    obtain ⟨i, hi⟩ := hAi1
    subst Ai
    exact h i le hAi2
  · intro a b le mem Ai hAi
    specialize mem Ai hAi
    obtain ⟨i, hi⟩ := hAi
    subst Ai
    exact h i le mem

@[simp]
local instance instOrderTop {n : ℕ} : OrderTop (WithTop (WithBot (Fin' n))) :=
  {
    top := ⊤
    le_top := by simp
  }

@[simp]
local instance instOrderBot {n : ℕ} : OrderBot (WithTop (WithBot (Fin' n))) :=
  {
    bot := ↑⊥
    bot_le := by
      intro a
      cases a with
      | top => simp
      | coe a => exact bot_le
  }

@[simp]
noncomputable
instance instrSup {n : ℕ} : Max (WithTop (WithBot (Fin' n))) :=
  {
    max := λ
      | ⊥, y => y
      | x, ⊥ => x
      | x, y => if x = y then x else ⊤
  }

@[simp]
noncomputable
local instance instInf {n : ℕ} : Min (WithTop (WithBot (Fin' n))) :=
  {
    min := λ
      | x, ⊤ => x
      | ⊤, y => y
      | x, y => if x = y then x else ⊥
  }

noncomputable
local instance instrSemilatticeSup {n : Nat} :
    SemilatticeSup (WithTop (WithBot (Fin' n))) :=
  {
    sup := instrSup.max
    le_sup_left := by
      intro x y
      cases_type* WithTop WithBot
      all_goals simp_all
      split_ifs <;> simp_all
    le_sup_right := by
      intro x y
      cases_type* WithTop WithBot
      all_goals simp_all
      split_ifs <;> simp_all
    sup_le := by
      intro x y z le1 le2
      cases_type* WithTop <;> simp_all [WithTop.none_eq_top, WithTop.some_eq_coe]
      cases_type* WithBot <;> simp_all [WithBot.none_eq_bot]
      · rw [WithTop.some_eq_coe]; simp
      · apply bot_le
      · rw [WithTop.some_eq_coe]; simp; assumption
      · rw [WithTop.some_eq_coe]; simp; assumption
      · split_ifs with h
        · rw [←h, WithTop.some_eq_coe, WithTop.coe_le_coe]
          simp [WithBot.some_eq_coe]; assumption
        · rw [Fin'.le_iff] at le1 le2
          rw [le1, le2] at h
          contradiction
  }

noncomputable
local instance instSemilatticeInf {n : Nat} : Lattice (WithTop (WithBot (Fin' n))) :=
  {
    inf := instInf.min
    inf_le_left := by
      intro x y
      cases_type* WithTop WithBot
      all_goals simp_all
      all_goals split_ifs <;> simp_all
    inf_le_right := by
      intro x y
      cases_type* WithTop WithBot
      all_goals simp_all
      all_goals split_ifs <;> simp_all
    le_inf := by
      intro x y z le1 le2
      cases_type* WithTop <;> simp_all [WithTop.none_eq_top, WithTop.some_eq_coe]
      cases_type* WithBot <;> simp_all [WithBot.none_eq_bot, WithBot.some_eq_coe]
      rw [Fin'.le_iff] at le1 le2
      split_ifs with h
      · rw [le1, h]
      · rw [←le1, le2] at h
        contradiction
  }

/-!
  ## 2.7 Lattices of subgroups

  If `G` is a group and ⟨SubG, ⊆⟩ is its ordered set of subgroups, then let
  `H`, `K` be subgroups of `G`. It's certainly true that `H ∩ K` is also a
  subgroup of `G`, so we can define `H ⊓ K` to be the intersection. But
  `H ∪ K` is not typically a subgroup. Nevertheless, the subgroup generated
  by `H ∪ K` *is* a subgroup and is actually `H ⊔ K`. Sadly there is no simple
  general formula for this as a set. Normal subgroups are better behaved. For
  normal subgroups, the set `HK = { h*k | h ∈ H ∧ k ∈ K }` is normal and
  serves as the supremum of `H` and `K` in the set of normal subgroups of `G`.

  Mathlib does not seem to have any declaration of the type of normal subgroups
  of a group `G`. After a little effort trying to make one, I realized it's
  not trivial. It could be a good exercise, but is not the point of the
  current project, so I will defer it until later or until somebody else
  can do it instead.
-/

/-!
  # Lattices as algebraic structures

  We begin to look at lattices as algebraic structures where the operators
  `⊔` and `⊓` are primary. We explore how these are connected with `≤`.
-/

/-!
  ## 2.8 The Connecting Lemma

  Let `L` be a lattice and let `a b : L`. Then the following are equivalent:

  (i) `a ≤ b`

  (ii) `a ⊔ b = b`

  (iii) `a ⊓ b = a`
-/

theorem example_2_8_sup_eq_iff_le [Lattice L] {a b : L} : a ⊔ b = b ↔ a ≤ b :=
  ⟨by rw [sup_eq_right]; tauto, λ le ↦ (example_2_5_1b le).1⟩

theorem example_2_8_inf_eq_iff_le [Lattice L] {a b : L} : a ⊓ b = a ↔ a ≤ b :=
  ⟨by rw [inf_eq_left]; tauto, λ le ↦ (example_2_5_1b le).2⟩

theorem example2_8_sup_eq_iff_inf_eq [Lattice L] {a b : L} : a ⊔ b = b ↔ a ⊓ b = a := by
  rw [example_2_8_inf_eq_iff_le, example_2_8_sup_eq_iff_le]

/-!
  ## 2.9 Theorem

  Let `L` be a lattice. Then for all `a b c : L`, `⊔` and `⊓` satisfy:

  (L1) `(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)` (sup is associative)
  (L1') `(a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)` (inf is associative)
  (L2) `a ⊔ b = b ⊔ a` (sup is commutative)
  (L2') `a ⊓ b = b ⊓ a` (inf is commutative)
  (L3) `a ⊔ a = a` (sup is idempotent)
  (L3') `a ⊓ a = a` (inf is idempotent)
  (L4) `a ⊔ (a ⊓ b) = a` (absorption for inf then sup)
  (L4') `a ⊓ (a ⊔ b) = a` (absorption for sup then inf)
-/

/-- This is known in Mathlib as `sup_assoc`. The Mathlib proof is recreated here. -/
theorem example_2_9_sup_assoc [Lattice L] {a b c : L} : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) :=
  eq_of_forall_ge_iff (λ x ↦ by simp only [sup_le_iff]; rw [and_assoc])

/-- This is known in Mathlib as `inf_assoc`. This is provable as the dual of the above. -/
theorem example_2_9_inf_assoc [Lattice L] {a b c : L} : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) :=
  @example_2_9_sup_assoc Lᵒᵈ _ _ _ _

/-- This is known in Mathlib as `sup_comm`. -/
theorem example_2_9_sup_comm [Lattice L] {a b : L} : a ⊔ b = b ⊔ a :=
  eq_of_forall_ge_iff (λ x ↦ by simp only [sup_le_iff]; rw [and_comm])

/-- This is known in Mathlib as `inf_comm`. -/
theorem example_2_9_inf_comm [Lattice L] {a b : L} : a ⊓ b = b ⊓ a :=
  eq_of_forall_le_iff (λ x ↦ by simp only [le_inf_iff]; rw [and_comm])

/-- This is known in Mathlib as `sup_idem` and proved by simp. -/
theorem example_2_9_sup_idem [Lattice L] {a : L} : a ⊔ a = a := by simp

/-- This is known in Mathlib as `inf_idem` and proved by simp. -/
theorem example_2_9_inf_idem [Lattice L] {a : L} : a ⊓ a = a := by simp

/-- This is known in Mathlib as `sup_inf_self`. -/
theorem example_2_9_sup_inf_self [Lattice L] {a b : L} : a ⊔ (a ⊓ b) = a := by
  rw [sup_comm, example_2_8_sup_eq_iff_le]
  exact inf_le_left

/-- This is known in Mathlib as `inf_sup_self`. -/
theorem example_2_9_inf_sup_self [Lattice L] {a b : L} : a ⊓ (a ⊔ b) = a :=
  @example_2_9_sup_inf_self Lᵒᵈ _ _ _

/-!
  Let `L` be a set (type) equipped with two operations `⊔` and `⊓`
  that satisfy (L1)-(L4) and (L1')-(L4') above. Then

  (i) For all `a b : L`, we have `a ⊔ b = b` if and only if `a ⊓ b = a`

  (ii) Define `≤` on `L` by `a ≤ b` if and only if `a ⊔ b = b`. Then `L` is a
  partial order under `≤`.

  (iii) With `≤` as above, `L` is actually a lattice in which `⊔` is sup and
  `⊓` is inf.

  This is essentially `Lattice.mk'` which does not even use `L3` and `L3'`. I
  will try to get by without either of them.
-/

theorem example_2_10_i [Max L] [Min L]
    (L2 : ∀ {a b : L}, a ⊔ b = b ⊔ a)
    (L2': ∀ {a b : L}, a ⊓ b = b ⊓ a)
    (L4 : ∀ {a b : L}, a ⊔ (a ⊓ b) = a)
    (L4': ∀ {a b : L}, a ⊓ (a ⊔ b) = a) {a b : L} :
    a ⊔ b = b ↔ a ⊓ b = a := by
  constructor <;> intro h
  · rw [←h]; exact L4'
  · rw [←h, L2, L2']; exact L4

def LatPO [Max L] [Min L]
    (L1 : ∀ {a b c : L}, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (L1': ∀ {a b c : L}, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c))
    (L2 : ∀ {a b : L}, a ⊔ b = b ⊔ a)
    (L2': ∀ {a b : L}, a ⊓ b = b ⊓ a)
    (L4 : ∀ {a b : L}, a ⊔ (a ⊓ b) = a)
    (L4': ∀ {a b : L}, a ⊓ (a ⊔ b) = a) : Lattice L :=
  have L3 : ∀ (a : L), a ⊔ a = a := λ a ↦
    calc
      a ⊔ a = a ⊔ a ⊓ (a ⊔ a) := by rw [L4']
      _ = a := by rw [L4]
  {
    sup := Max.max
    inf := Min.min
    le := λ a b ↦ a ⊔ b = b
    le_refl := L3
    le_trans := by
      intro a b c le1 le2
      simp at le1 le2 ⊢
      rw [←le2, ←L1, le1]
    le_antisymm := by
      intro a b le1 le2
      simp at le1 le2
      rw [←le1]; nth_rewrite 1 [←le2]; rw [L2]
    le_sup_left := by
      intro a b; simp
      rw [←L1, L3]
    le_sup_right := by
      intro a b; simp
      rw [L2, L1, L3]
    sup_le := by
      intro a b c le1 le2
      simp at le1 le2 ⊢
      rw [L1, le2, le1]
    inf_le_left := by
      intro a b; simp
      rw [L2, L4]
    inf_le_right := by
      intro a b; simp
      rw [L2, L2', L4]
    le_inf := by
      intro a b c le1 le2
      simp at le1 le2 ⊢
      rw [example_2_10_i L2 L2' L4 L4'] at le1 le2 ⊢
      rw [←L1', le1, le2]
  }

/-!
  ## 2.11 Stocktaking

  So Lattices can be completely characterized by `⊔` and `⊓`. In all Lattices,
  the sup and inf are related to `≤` exactly as above. So, we can take the
  algebraic properties as simply given without having to think about LUBs and GLBs
  if that happens to be a more convenient way of proceeding.

  Observe that associativity of `⊔` means that `sSup {a₁, ..., aₙ} = a₁ ⊔ ... ⊔ aₙ` (by
  a simple inductive argument). As a consequence, suprema exist for any finite set of
  elements of a lattice. The inductive argument only applies to finite sets, and of
  course the suprema of infinite subsets of a lattice need not exist in general. So,
  in general, there need not be an instance of `SupSet L` if we have `Lattice L`.
-/

/-!
  ## 2.12 Definitions

  Let `L` be a lattice. It could happen that it has both a `⊤` and `⊥`. We want to
  explore how to think of these from the algebraic point of view instead of the
  order-theoretic point of view.

  `L` has a "one" if there is some element `1 : L` such that for all `a : L`,
  `a ⊓ 1 = a`. Similarly, `L` has a "zero" if there is some element `0 : L`
  such that `a ⊔ 0 = a` for all `a : L`. Then it follows that `L` has an
  algebraic `1` if and only if `L` has an order-theoretic `⊤`, and dually for
  `0` and `⊥`.

  A lattice with a `0` and `1` is called bounded. There does not seem to be a single class for
  bounded lattices in Mathlib. Rather, there is `BoundedOrder L` which is defined
  to be the conjunction of `OrderTop L` and `OrderBot L`. So, to say that `L` is
  a bounded lattice we would have to write `[BoundedOrder L] [Lattice L]`.

  Note that all finite lattices are automatically bounded with `sSup L = 1` and
  `sInf L = 0`. In fact, Mathlib does not seem to have an instance of `SupSet` for
  finite types with suprema. Can I just make one here? In the spirit of not
  worrying about finite sets in this pass, I will leave it alone.

  Recalling 2.6(5), note that `⟨ℕ, lcm, gcd⟩` is bounded with `1 = 0` and `0 = 1`.
-/

section

def LNat : Type := ℕ

@[simp]
instance LNat.instSuplocal : Max LNat := { max := Nat.lcm }

@[simp]
instance LNat.instInflocal : Min LNat := { min := Nat.gcd }

instance LNat.instCCMWZ : CancelCommMonoidWithZero LNat := Nat.instCancelCommMonoidWithZero
instance LNat.instNGCDM : NormalizedGCDMonoid LNat := by
  haveI I : NormalizedGCDMonoid Nat := by infer_instance
  exact I

lemma gcd_lcm_self (n m : LNat) : Nat.gcd n (Nat.lcm n m) = n := by
  exact Nat.gcd_eq_left (Nat.dvd_lcm_left n m)

lemma lcm_gcd_self (n m : LNat) : Nat.lcm n (Nat.gcd n m) = n  := by
  have h := Nat.gcd_dvd_left n m
  have : normalize n = n := by simp only [normalize, normUnit, Units.val_one, mul_one,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  exact (lcm_eq_left_iff n _ this).mpr h

instance example_2_12_L : Lattice LNat :=
  Lattice.mk' lcm_comm lcm_assoc gcd_comm gcd_assoc lcm_gcd_self gcd_lcm_self

def example_2_12_BO : BoundedOrder LNat :=
  {
    top := 0
    bot := 1
    le_top := λ a ↦ Nat.lcm_zero_right a
    bot_le := λ a ↦ by
      change 1 ⊔ a = a
      rw [example_2_10_i (by simp [Nat.lcm_comm]) (by simp [Nat.gcd_comm]) (by simp [lcm_gcd_self]) (by simp [gcd_lcm_self])]
      exact Nat.gcd_one_left a
  }

end section

/-!
  # Sublattices, products and homomorphisms

  We now show how to derive more lattices from existing lattices
-/

/-!
  ## 2.13 Sulattices

  Let `L` be a lattice and `∅ ≠ M ⊆ L`. Then `M` is a sublattice of `L`
  if and only if

  `a,b ∈ M` implies `a ⊔ b ∈ M` and `a ⊓ b ∈ M`.

  This manifests in Mathlib as `Sublattice (M : Set L)` that has the
  `carrier` set of elements of `M`, `supClosed'`, a proof that sups
  of elements of `M` are also in `M`, and its dual `infClosed'`.
-/

/-!
  ## 2.14 Examples

  (1) Any one-element subset of a lattice is a sublattice.
-/

def example_2_14a [Lattice L] (x : L) : Sublattice L :=
  {
    carrier := {x}
    supClosed' := by
      intro a mema b memb
      simp at mema memb
      subst a; subst b
      simp
    infClosed' := by
      intro a mema b memb
      simp at mema memb
      subst a; subst b
      simp
  }

/-!
  More generally, any non-empty chain in a lattice is a sublattice.
-/

def example_2_14b [Lattice L] {K : Set L} (h : IsChainLE K) :
    Sublattice L :=
  {
    carrier := K
    supClosed' := by
      intro a mema b memb
      by_cases eq : a = b
      · subst a; simp; exact memb
      · specialize h mema memb eq
        cases h with
        | inl h => simp_all
        | inr h => simp_all
    infClosed' := by
      intro a mema b memb
      by_cases eq : a = b
      · subst a; simp; exact memb
      · specialize h mema memb eq
        cases h with
        | inl h => simp_all
        | inr h => simp_all
  }

/-!
  (2) More diagram-based stuff

  (3) A subset `M` of a lattice `L` may be a lattice in its own right
  without being a sublattice of `L`. This is shown in one of the diagrams.
-/

/-!
  ## 2.15 Products

  Let `L` and `K` be lattices. Define `⊔` and `⊓` coordinate-wise on
  `L × K`, as follows:

    (l₁, k₁) ⊔ (l₂, k₂) = (l₁ ⊔ l₂, k₁ ⊔ k₂)

    (l₁, k₁) ⊓ (l₂, k₂) = (l₁ ⊓ l₂, k₁ ⊓ k₂)

  One can check that the algebraic properties of `⊔` and `⊓` are satisfied
  by these definitions, so the product also forms a lattice. This
  is the default lattice instance on `L × K` in Mathlib assuming `L` and `K`
  are both lattices.

  It is routine to show that `L × K` always contains sublattices isomorphic
  to `L` and to `K` (assuming they're nonempty), by taking `{l₀} × K` and
  `L × {k₀}` for any `l₀` and `k₀`. I'll only do one of these.
-/

def exercise_2_15_a [Lattice L] [Lattice K] (l₀  : L) :
    K ≃o ({ (l, _) | l = l₀ } : Set (L × K)) :=
  {
    toFun := λ k ↦ ⟨(l₀, k), by simp⟩
    invFun := λ lk ↦ lk.val.2
    left_inv := by intro k; simp
    right_inv := by
      intro ⟨(l, k), prf⟩; simp at prf ⊢
      symm; exact prf
    map_rel_iff' := by
      intro k1 k2
      constructor <;> intro le
      · exact le.2
      · exact ⟨by rfl, le⟩
  }

/-!
  ## 2.16 Homomorphisms

  Lattice homomorphisms are maps that preserve sups and infs. It will be
  important to understand how these maps relate to order preserving maps
  on the lattices viewed simply as partial orders. But first we have
  to get lattice homomorphisms defined.

  In Mathlib, a `SupHom α β` requires both `α` and `β` to have `⊔` defined.
  It then consists of a function `f : α → β` and a proof that it preserves sups,
  namely `f (a₁ ⊔ a₂) = f a₁ ⊔ f a₂`. Then a lattice homomorphism from
  `α` to `β` is a SupHom that also preserves inf. Thus `LatticeHom α β`
  comes equipped with a function, and two proofs that it preserves sups and
  infs. Those proofs are called `map_sup'` and `map_inf'`.

  The text defines a Lattice Isomorphism as a bijective Lattice Homomorphism.
  There is no `LatticeIso α β` defined in Mathlib, so it will probably turn
  out that an `OrderIso α β` between lattices `α` and `β` must be a bijective
  lattice homomorphism, but we'll see! Similarly, the text defines a
  lattice embedding to be a lattice hom that is injective. No such definition
  exists in Mathlib, so we'll have to see why.
-/

/-!
  ## 2.17 Remarks

  (1) It is easy to check that the inverse of a lattice isomorphism is a
  lattice hom, and hence also a lattice isomorphism.
-/

def example_2_17_1 [Lattice L] [Lattice K] (η : LatticeHom L K) (invFun : K → L)
    (leftInv : Function.LeftInverse invFun η.toFun)
    (rightInv : Function.RightInverse invFun η.toFun)
    : LatticeHom K L :=
  have h : Function.Bijective η.toFun := by
    apply Function.bijective_iff_has_inverse.mpr
    use invFun
  {
    toFun := invFun
    map_sup' := by
      intro a b
      obtain ⟨al, hal⟩ := h.2 a
      obtain ⟨bl, hbl⟩ := h.2 b
      subst a; subst b
      rw [←η.map_sup']
      rw [leftInv, leftInv, leftInv]
    map_inf' := by
      intro a b
      simp
      obtain ⟨al, hal⟩ := h.2 a
      obtain ⟨bl, hbl⟩ := h.2 b
      subst a; subst b
      rw [←η.map_inf']
      rw [leftInv, leftInv, leftInv]
  }

/-!
  (2) The text introduces notation for when `K` has a sublattice that is isomorphic
  to `L`. We will see below that when this happens, then there will be an
  OrderEmbedding.

  (3) Lattice homs need not preserve `⊤` and `⊥` if they exist, apparently.
  So it's natural to define a `BoundedLatticeHom` that is a `LatticeHom` that
  additionally preserves ⊤ and ⊥. The text calls these `{0, 1}-homomorphisms`.
  These apparently don't show up until chapters 5 and 11.
-/

/-!
  ## 2.18 Examples

  The text returns to various previous examples. The key takeaway is that
  not every `OrderHom` between lattices is also a `LatticeHom`. However, we
  will see below, that every `OrderIso` is a Lattice Isomorphism. This explains
  why we don't need a separate class for Lattice Isomorphisms.
-/

/-!
  ## 2.19 Proposition

  Let `L` and `K` be lattices and `f : L → K` a map.

  (i) The following are equivalent:

  (a) `f` is order-preserving

  (b) ∀ a b : L, f a ⊔ f b ≤ f (a ⊔ b)

  (c) ∀ a b : L, f (a ⊓ b) ≤ f a ⊓ f b

  In particular, if `f` is a lattice hom, it is order preserving.

  (ii) `f` is a lattice isomorphism if and only if it is an order isomorphism.
-/

lemma example_2_19_i_a_imp_b [Lattice L] [Lattice K] (f : L → K)
    (mono : Monotone f) : ∀ a b : L, f a ⊔ f b ≤ f (a ⊔ b) := by
  intro a b
  have ale : f a ≤ f (a ⊔ b) := mono (le_sup_left : a ≤ a ⊔ b)
  have ble : f b ≤ f (a ⊔ b) := mono (le_sup_right : b ≤ a ⊔ b)
  exact sup_le_iff.mpr ⟨ale, ble⟩

lemma example_2_19_i_a_imp_c [Lattice L] [Lattice K] (f : L → K)
    (mono : Monotone f) : ∀ a b : L, f (a ⊓ b) ≤ f a ⊓ f b := by
  intro a b
  have lea : f (a ⊓ b) ≤ f a := mono (inf_le_left : a ⊓ b ≤ a)
  have leb : f (a ⊓ b) ≤ f b := mono (inf_le_right : a ⊓ b ≤ b)
  exact le_inf_iff.mpr ⟨lea, leb⟩

lemma example_2_19_i_b_imp_a [Lattice L] [Lattice K] (f : L → K)
    (h : ∀ a b, f a ⊔ f b ≤ f (a ⊔ b)) : Monotone f := by
  intro a b le
  have bsup : a ⊔ b = b := sup_of_le_right le; rw[←bsup]
  have le' : f a ≤ f a ⊔ f b := le_sup_left
  exact le_trans le' (h a b)

lemma example_2_19_i_c_imp_a [Lattice L] [Lattice K] (f : L → K)
    (h : ∀ a b, f (a ⊓ b) ≤ f a ⊓ f b) : Monotone f := by
  intro a b le
  have ainf : a ⊓ b = a := inf_of_le_left le; rw [←ainf]
  have le' : f a ⊓ f b ≤ f b := inf_le_right
  exact le_trans (h a b) le'

lemma example_2_19_observation [Lattice L] [Lattice K] (f : LatticeHom L K) :
    Monotone f := by apply example_2_19_i_b_imp_a; simp

lemma example_2_19_ii [Nonempty L] [Lattice L] [Lattice K] (f : L → K) :
    (Function.Bijective f ∧ ∃ h₁ : LatticeHom L K, h₁.toFun = f) ↔
    ∃ h₂ : L ≃o K, h₂.toFun = f := by
  constructor
  · intro ⟨bij, ⟨h₁, lhom⟩⟩
    use {
      toFun := f
      invFun := Function.invFun f
      left_inv := Function.leftInverse_invFun bij.1
      right_inv := Function.rightInverse_invFun bij.2
      map_rel_iff' := by
        intro a b
        simp
        constructor <;> intro le
        · apply sup_of_le_right at le
          rw [←lhom, ←h₁.map_sup' a b] at le
          suffices a ⊔ b = b by rw [←this]; exact le_sup_left
          rw [lhom] at le
          exact bij.1 le
        · have mono := example_2_19_observation h₁
          rw [←lhom]
          exact mono le }
  · intro ⟨h₂, feq⟩
    constructor
    · rw [←feq]
      exact OrderIso.bijective h₂
    · use {
        toFun := f
        map_sup' := by
          intro a b
          subst f
          simp
        map_inf' := by
          intro a b
          subst f
          simp
      }

/-!
  # Ideals and filters

  This section introduces lattice ideals and filters. Ideals form a central
  concept in algebra, and filters have a variety of applications in logic
  and topology. Chapter 10 will focus on prime ideals, and this will form
  the basis for the contents of Chapter 11.
-/

/-!
  ## 2.20 Definitions

  Let `L` be a lattice. A non-empty subset `J` of `L` is called an "ideal" if
  and only if

  (i) `∀ a b : L, a ∈ J → b ∈ J → a ⊔ b ∈ J`

  (ii) `∀ a b : L, b ∈ J → a ≤ b → a ∈ J`

  The above definition resembles the definition of an ideal in a ring. We could
  state it more succinctly as a non-empty down-set `J` of a lattice that is closed
  under join.

  Mathlib has `Order.Ideal P` which is a structure that bundles a `LowerSet P`
  together with a proof that the set is "directed" (with respect to `≤`).
  This means that for any `a b ∈ J`, there is some `c ∈ J` such that `a ≤ c ∧ b ≤ c`.
  Being directed says nothing about closure under `⊔`, however, if `L` is a lattice
  and `J : Order.Ideal L`, then it follows that `J` is closed under `⊔`.
-/

/-- This is known in Mathlib as `Order.Ideal.sup_mem` -/
lemma example_2_20_lattice_ideal [Lattice L] (J : Order.Ideal L) :
    ∀ a ∈ J, ∀ b ∈ J, a ⊔ b ∈ J := by
  intro a amem b bmem
  obtain ⟨c, ⟨hc1, hc2, hc3⟩⟩ := J.directed' a amem b bmem
  have sle : a ⊔ b ≤ c := sup_le_iff.mpr ⟨hc2, hc3⟩
  exact J.lower sle hc1

/-!
  The text says that every ideal of a lattice is a sublattice.
-/

def example_2_20_ideal_toSublattice [Lattice L] (J : Order.Ideal L) : Sublattice L :=
  {
    carrier := J
    supClosed' := by
      intro a amem b bmem
      exact Order.Ideal.sup_mem amem bmem
    infClosed' := by
      intro a amem b _
      exact J.lower' (inf_le_left) amem
  }

/-!
   A dual ideal is called a "filter". More concretely, a non-empty subset `G`
   of a Lattice `L` is called a filter if and only if

   (i) `∀ a b : L, a ∈ G → b ∈ G → a ⊓ b ∈ G`

   (ii) `∀ a b : L, b ∈ G → b ≤ a → a ∈ G`

   In other words, a filter is a non-empty upper set, closed under `⊓`.

   Mathlib calls a filter an `Order.PFilter`, and it is literally defined by
   specifying an `Order.Ideal` on `Lᵒᵈ`.

   An ideal or filter is called "proper" if it is not equal to `L` itself.
   Mathlib has a type class for this called `Order.Ideal.IsProper J` which
   is a `Prop`. Oddly there is no corresponding definition for `Order.PFilter`.
   Perhaps we are typically meant to work with Ideals in partial orders, and
   when filters are used, we can just invoke the dual?

   It is easy to show that, if a lattice has a `⊤`, then an ideal `J` is proper
   if and only if `⊤ ∉ J`.
-/

lemma example_2_20_withTop_ideal [Lattice L] [OrderTop L] (J : Order.Ideal L) :
    Order.Ideal.IsProper J ↔ ⊤ ∉ J := by
  constructor <;> intro h
  · intro mem
    have allmem : ∀ x : L, x ∈ J := by
      intro x
      exact J.lower' (le_top (a := x)) mem
    apply h.ne_univ
    ext x
    constructor
    · simp
    · intro _
      exact allmem x
  · exact {
      ne_univ := by
        intro eq
        apply h
        have := Set.mem_univ (⊤ : L)
        rw [←eq] at this
        exact this }

/-!
  For each `a : L`, the set `↓ᵖa` is an ideal called the "principal ideal" generated
  by `a`. Dually `↑ᵖa` is a principal filter.
-/

def example_2_20_principal_ideal [Lattice L] (a : L) : Order.Ideal L :=
  {
    carrier := ↓ᵖa
    lower' := (↓ᵖa).lower'
    nonempty' := by use a; simp
    directed' := by
      intro x xmem y ymem
      use x ⊔ y
      constructorm* _ ∧ _
      · exact sup_le_iff.mpr ⟨xmem, ymem⟩
      · exact le_sup_left
      · exact le_sup_right
  }

/-!
  ## 2.21 Examples

  (1) In a finite lattice, every ideal or filter is principal. If `J` is an
  ideal, then `J = ↓ᵖ(sSup J)`.
-/

/-- What an absolute mess of a proof! -/
lemma example_2_21_1 [Fintype L] [Lattice L] (J : Order.Ideal L) (x : L) :
    ∃ s : L, x ∈ J ↔ x ∈ ↓ᵖs := by
  set J' := Set.toFinset J.carrier with hJ
  have mem_iff : ∀ x, x ∈ J ↔ x ∈ J' := by
    intro x
    change x ∈ J.carrier ↔ x ∈ J'
    rw [←Set.mem_toFinset, ←hJ]
  cases Finset.Nonempty.exists_eq_singleton_or_nontrivial (Set.toFinset_nonempty.mpr J.nonempty') with
  | inl h1 =>
    obtain ⟨a, ha⟩ := h1
    use a
    constructor
    · intro xmem
      rw [mem_iff] at xmem
      simp_all
    · intro xmem
      apply J.lower' at xmem
      have : a ∈ ↑J := by
        rw [mem_iff, hJ, ha]; simp
      exact xmem this
  | inr h1 =>
    obtain ⟨a, ha⟩ := J.nonempty'
    rw [←Set.mem_toFinset] at ha
    set K := J'.erase a with hK
    have add : J' = insert a K := by
      have := (Finset.insert_erase ha).symm
      rwa [hK]
    have ne : (J'.erase a).Nonempty := Finset.Nontrivial.erase_nonempty h1
    rw [←hK] at ne
    set b := Finset.sup' K ne id with hb
    use b ⊔ a
    constructor
    · intro xmem
      by_cases xK : x ∈ K
      · have xle : x ≤ b := by
          rw [hb]
          exact Finset.le_sup' id xK
        apply le_trans xle le_sup_left
      · rw [mem_iff x] at xmem
        rw [hK] at xK
        have xeq : x = a := by
          rw [add] at xmem
          rw [Finset.mem_insert_coe] at xmem
          apply Set.eq_or_mem_of_mem_insert at xmem
          cases xmem with
          | inl h => exact h
          | inr h => contradiction
        subst x
        exact le_sup_right
    · intro xmem
      rw [mem_iff]
      have mem : b ∈ J := by
        apply Finset.sup'_mem
        · intro y ymem z zmem
          exact Order.Ideal.sup_mem ymem zmem
        · intro i imem
          rw [hK] at imem
          change i ∈ J; rw [mem_iff]
          exact Finset.erase_subset a J' imem
      rw [Set.mem_toFinset] at ha
      change b ∈ J.carrier at mem
      have bamem := Order.Ideal.sup_mem mem ha
      apply J.lower xmem at bamem
      rw [←mem_iff]
      exact bamem

/-!
  (2) Let `L` and `K` be bounded lattices and `f : L → K` a bounded lattice hom.
  Then `f⁻¹(0)` is an ideal and `f⁻¹(1)` is a filter in `L`.
-/

lemma example_2_21_2a [Lattice L] [BoundedOrder L] [Lattice K] [BoundedOrder K]
    (f : BoundedLatticeHom L K) : Order.IsIdeal (f⁻¹' {⊥}) :=
  {
    IsLowerSet := by
      intro a b le amem
      simp_all
      have mono : Monotone f := (BoundedLatticeHom.toBoundedOrderHom f).monotone'
      apply_fun ⇑f at le using mono
      rw [amem] at le
      exact le_bot_iff.mp le
    Nonempty := by
      use ⊥
      rw [Set.mem_preimage]
      simp
    Directed := by
      intro a amem b bmem
      simp at amem bmem
      use a ⊔ b
      constructorm* _ ∧ _
      · simp; tauto
      · simp
      · simp
  }

/-!
  (3) The following are ideals in `Set X`:

  (a) all subsets not containing a fixed element of `X`

  (b) all finite subsets (this ideal is non-principal if `X` is infinite)
-/

lemma example_2_21_3a (x : X) : Order.IsIdeal { S : Set X | x ∉ S } :=
  {
    IsLowerSet := by
      intro a b le amem xmem
      exact amem (le xmem)
    Nonempty := by
      use ∅; simp
    Directed := by
      intro a amem b bmem
      use a ∪ b
      simp_all
  }

lemma example_2_21_3b : Order.IsIdeal { S : Set X | Set.Finite S } :=
  {
    IsLowerSet := by
      intro a b le amem
      exact Set.Finite.subset amem le
    Nonempty := by use ∅; simp
    Directed := by
      intro a amem b bmem
      use a ∪ b
      simp_all
  }

/-!
  (4) I won't formalize this one because it's about topological spaces
  and I don't really want to spend too much time learning the surrounding
  API, even if it might be pretty easy.
-/

/-!
  # Complete lattices and ⋂-structures

  It's time to come back to complete lattices for which the join and
  meet of arbitrary sets `S` exist. Recall that Mathlib denotes these
  as `sSup` and `sInf`, and this is defined via a type class instance
  of `SupSet` or `InfSet`.

  ## 2.22 Lemma

  Let `P` be an ordered set, let `S, T ⊆ P` and assume `sSup S`, `sSupT`,
  `sInf S`, and `sInf T` exist in `P`. (We will just assume `P` is a
  complete lattice instead, because it's a pain to make the right
  assumptions just for the given sets `S` and `T`, even though it's
  more general.)

  (i) `∀ s ∈ S, s ≤ sSup S ∧ sInf S ≤ s`.
-/

lemma example_2_22_i [CompleteLattice P] (S : Set P) (s : P) (smem : s ∈ S) :
    s ≤ sSup S ∧ sInf S ≤ s := ⟨le_sSup smem, sInf_le smem⟩

/-- Version that only assumes sup and inf for `S`. -/
lemma example_2_22_ia' [PartialOrder P] (S : Set P) (s : P) {ssup : P} (smem : s ∈ S)
    (supS : IsLUB S ssup) :
    s ≤ ssup := supS.1 smem

lemma example_2_22_ib' [PartialOrder P] (S : Set P) (s : P) {sinf : P} (smem : s ∈ S)
    (infS : IsGLB S sinf):
    sinf ≤ s := infS.1 smem

/-!
  (ii) Let `x : P`; then `x ≤ sInf S ↔ ∀ s ∈ S, x ≤ s`
-/

lemma example_2_22_ii [CompleteLattice P] (S : Set P) (x : P) :
    x ≤ sInf S ↔ ∀ s ∈ S, x ≤ s := by
  constructor
  · intro xle s smem
    exact le_trans xle (sInf_le smem)
  · intro h
    exact le_sInf h

lemma example_2_22_ii' [PartialOrder P] (S : Set P) (x : P) {sinf : P} (infS : IsGLB S sinf) :
    x ≤ sinf ↔ ∀ s ∈ S, x ≤ s := by
  constructor
  · intro xle s smem
    exact le_trans xle (infS.1 smem)
  · intro h
    exact infS.2 h


/-!
  (iii) Let `x : P`; then `sSup S ≤ x ↔ ∀ s ∈ S, s ≤ x`
-/

lemma example_2_22_iii [CompleteLattice P] (S : Set P) (x : P) :
    sSup S ≤ x ↔ ∀ s ∈ S, s ≤ x := by
  constructor
  · intro lex s smem
    exact le_trans (le_sSup smem) lex
  · intro h
    exact sSup_le h

lemma example_2_22_iii' [PartialOrder P] (S : Set P) (x : P) {ssup : P} (supS : IsLUB S ssup) :
    ssup ≤ x ↔ ∀ s ∈ S, s ≤ x := by
  constructor
  · intro lex s smem
    exact le_trans (supS.1 smem) lex
  · intro h
    exact supS.2 h

/-!
  (iv) `sSup S ≤ sInf T ↔ ∀ s ∈ S, ∀ t ∈ T, s ≤ t`
-/

lemma example_2_22_iv [CompleteLattice P] (S T : Set P) :
    sSup S ≤ sInf T ↔ ∀ s ∈ S, ∀ t ∈ T, s ≤ t := by
  constructor
  · intro le s smem t tmem
    apply le_trans _ (sInf_le tmem)
    exact le_trans (le_sSup smem) le
  · intro h
    rw [example_2_22_iii]
    intro s smem
    rw [example_2_22_ii]
    intro t tmem
    exact h s smem t tmem

lemma example_2_22_iv' [PartialOrder P] (S T : Set P) (ssup tinf : P)
    (supS : IsLUB S ssup) (infT : IsGLB T tinf) :
    ssup ≤ tinf ↔ ∀ s ∈ S, ∀ t ∈ T, s ≤ t := by
  constructor
  · intro le s smem t tmem
    apply le_trans _ (infT.1 tmem)
    exact le_trans (supS.1 smem) le
  · intro h
    rw [example_2_22_iii' S tinf supS]
    intro s smem
    rw [example_2_22_ii' T s infT]
    intro t tmem
    exact h s smem t tmem

/-!
  (v) If `S ⊆ T`, then `sSup S ≤ sSup T` and `sInf T ≤ sInf S`
-/

lemma example_2_22_v [CompleteLattice P] (S T : Set P) (sub : S ⊆ T) :
    sSup S ≤ sSup T ∧ sInf T ≤ sInf S := by
  constructor
  · rw [example_2_22_iii]
    intro s smem
    specialize sub smem
    exact (example_2_22_i T s sub).1
  · rw [example_2_22_ii]
    intro s smem
    specialize sub smem
    exact (example_2_22_i T s sub).2

lemma example_2_22_va' [PartialOrder P] (S T : Set P) (sub : S ⊆ T)
    {ssup tsup : P} (supS : IsLUB S ssup) (supT : IsLUB T tsup) :
    ssup ≤ tsup:= by
  rw [example_2_22_iii' S tsup supS]
  intro s smem
  specialize sub smem
  exact example_2_22_ia' T s sub supT

lemma example_2_22_vb' [PartialOrder P] (S T : Set P) (sub : S ⊆ T)
    {sinf tinf : P} (infS : IsGLB S sinf) (infT : IsGLB T tinf) :
    tinf ≤ sinf := by
  rw [example_2_22_ii' S tinf infS]
  intro s smem
  specialize sub smem
  exact example_2_22_ib' T s sub infT

/-!
  The join and meet behave well with respect to union.

  ## 2.23 Lemma

  Let `P` be a complete lattice and `S, T ⊆ P`. Then
  `sSup (S ∪ T) = (sSup S) ⊔ (sSup T)` and
  `sInf (S ∪ T) = (sInf S) ⊓ (sInf T)`
-/

lemma example_2_23a [CompleteLattice P] (S T : Set P) :
    sSup (S ∪ T) = (sSup S) ⊔ (sSup T) := by
  rw [←le_le_iff_eq]
  constructor
  · rw [example_2_22_iii]
    intro st stmem
    cases stmem with
    | inl smem => exact le_trans (le_sSup smem) le_sup_left
    | inr tmem => exact le_trans (le_sSup tmem) le_sup_right
  · apply sup_le
    · exact (example_2_22_v _ _ (Set.subset_union_left)).1
    · exact (example_2_22_v _ _ (Set.subset_union_right)).1

lemma example_2_23b [CompleteLattice P] (S T : Set P) :
    sInf (S ∪ T) = (sInf S) ⊓ (sInf T) := by
  rw [←le_le_iff_eq]
  constructor
  · apply le_inf
    · exact (example_2_22_v _ _ (Set.subset_union_left)).2
    · exact (example_2_22_v _ _ (Set.subset_union_right)).2
  · rw [example_2_22_ii]
    intro st stmem
    cases stmem with
    | inl smem => exact le_trans inf_le_left (sInf_le smem)
    | inr tmem => exact le_trans inf_le_right (sInf_le tmem)

/-!
  ## 2.24 Lemma

  Let `P` be a lattice. Then for every finite, nonempty set `F`,
  `sSup F` and `sInf F` are defined.

  Mathlib already has this in some form. Namely it has `Finset.sup'`
  and `Finset.inf'`. (The unprimed versions do not require `F` to be
  nonempty, but do require `[OrderBot P]` and `[OrderTop P]` respectively.)

  Oddly, while Mathlib has proofs for the component pieces to say that these
  are LUB and GLB, there is no result stating it explicitly. So I include it
  here.
-/

lemma Finset.sup_isLUB {α : Type} [SemilatticeSup α] [OrderBot α] (F : Finset α) :
    IsLUB F (sup F id) := ⟨λ x h => id_eq x ▸ le_sup h, λ _ h => Finset.sup_le h⟩

lemma Finset.sup'_isLUB {α : Type} [SemilatticeSup α] {F : Finset α} (ne : F.Nonempty) :
    IsLUB F (sup' F ne id) := ⟨λ x h => id_eq x ▸ le_sup' id h, λ _ h => Finset.sup'_le ne id h⟩

lemma Finset.inf_isGLB {α : Type} [SemilatticeInf α] [OrderTop α] (F : Finset α) :
    IsGLB F (inf F id) := ⟨λ x h => id_eq x ▸ inf_le h, λ _ h => Finset.le_inf h⟩

lemma Finset.inf'_isGLB {α : Type} [SemilatticeInf α] {F : Finset α} (ne : F.Nonempty) :
    IsGLB F (inf' F ne id) := ⟨λ x h => id_eq x ▸ inf'_le id h, λ _ h => Finset.le_inf' ne id h⟩

/-
class FinSupSet (α : Type*) where
  /-- Supremum of a finite set -/
  fSup : ∀ {F : Finset α}, F.Nonempty → α
open FinSupSet

class FinInfSet (α : Type*) where
  /-- Infimum of a finite set -/
  fInf : ∀ {F : Finset α}, F.Nonempty → α
open FinInfSet

instance FinSupSet.toDual {α : Type*} [FinInfSet α] : FinSupSet αᵒᵈ where
  fSup := λ neF ↦ OrderDual.toDual (fInf neF)

instance FinInfSet.toDual {α : Type*} [FinSupSet α] : FinInfSet αᵒᵈ where
  fInf := λ neF ↦ OrderDual.toDual (fSup neF)

instance FinSupSet.ofDual {α : Type*} [FinInfSet αᵒᵈ] : FinSupSet αᵒᵈ where
  fSup := λ neF ↦ OrderDual.ofDual (fSup neF)

instance FinInfSet.ofDual {α : Type*} [FinSupSet αᵒᵈ] : FinInfSet αᵒᵈ where
  fInf := λ neF ↦ OrderDual.ofDual (fInf neF)

lemma IsLUB.cons [SemilatticeSup P] (a : P) {b : P} {s : Finset P} (ha : a ∉ s) (hs : IsLUB s b) :
    IsLUB (Finset.cons a s ha) (a ⊔ b) := by
  rw [Finset.cons_eq_insert]
  push_cast
  exact IsLUB.insert a hs


lemma example_2_24a' [Lattice P] {F : Finset P} (ne : F.Nonempty) :
    ∃ p : P, IsLUB F p := by
  use F.sup' ne id
  exact ⟨λ x h => id_eq x ▸ Finset.le_sup' id h, λ _ h => Finset.sup'_le ne id h⟩

lemma example_2_24a [Lattice P] {F : Finset P} (ne : F.Nonempty) :
    ∃ p : P, IsLUB F p := by
  induction ne using Finset.Nonempty.cons_induction with
  | singleton a =>
      use a
      simp only [Finset.coe_singleton, IsLUB_iff, upperBounds_singleton,
        Set.mem_Ici, le_refl, imp_self, implies_true, and_self]
  | cons a s h hs ih =>
      obtain ⟨x, hx⟩ := ih
      use a ⊔ x
      exact IsLUB.cons a h hx

lemma example_2_24b [Lattice P] {F : Finset P} (ne : F.Nonempty) :
    ∃ p : P, IsGLB F p := by
  exact @example_2_24a Pᵒᵈ _ _ ne

/-- These typeclasses seem to be more trouble than they're worth.  -/
noncomputable
instance instLatticeFinSupSet [Lattice P] : FinSupSet P where
  fSup := λ ne ↦ (example_2_24a ne).choose


noncomputable
instance instLatticeFinInfSet [Lattice P] : FinInfSet P where
  fInf := λ ne ↦ (example_2_24b ne).choose

lemma fSup.sup [Lattice P] {F : Finset P} (neF : F.Nonempty) {p : P} :
    p ∈ F → p ≤ fSup neF := by
  intro pmem
  exact ((IsLUB_iff _).mp (example_2_24a neF).choose_spec).1 pmem

lemma fInf.inf [Lattice P] {F : Finset P} (neF : F.Nonempty) {p : P} :
    p ∈ F → fInf neF ≤ p := by
  intro pmem
  exact ((IsGLB_iff _).mp (example_2_24b neF).choose_spec).1 pmem

lemma fSup.isLUB [Lattice P] {F : Finset P} (neF : F.Nonempty) : IsLUB F (fSup neF) :=
  (example_2_24a neF).choose_spec

lemma fInf.isGLB [Lattice P] {F : Finset P} (neF : F.Nonempty) : IsGLB F (fInf neF) :=
  (example_2_24b neF).choose_spec

lemma fSup.isLUB_of_eq [Lattice P] {F : Finset P} (neF : F.Nonempty)
    {x : P} (eq : x = fSup neF) : IsLUB F x := by subst eq; exact fSup.isLUB neF

lemma fInf.isGLB_of_eq [Lattice P] {F : Finset P} (neF : F.Nonempty)
    {x : P} (eq : x = fInf neF) : IsGLB F x := by subst eq; exact fInf.isGLB neF
 -/
lemma IsLUB_uniq [PartialOrder P] {S : Set P} {a b : P} (h1 : IsLUB S a) (h2 : IsLUB S b) : a = b :=
  le_antisymm (h1.2 h2.1) (h2.2 h1.1)


/-
lemma fSup_singleton [Lattice P] {p : P} (ne : ({p} : Finset P).Nonempty) :
    fSup ne = p := by
  have pmem : p ∈ ({p} : Finset P) := Finset.mem_singleton.mpr rfl
  have lub := (example_2_24a ne).choose_spec; push_cast at lub
  have plub : IsLUB {p} p := isLUB_singleton
  have ple := fSup.sup ne pmem
  simp only [fSup, Finset.coe_singleton]
  exact IsLUB_uniq lub plub -/

/-!
  ## 2.25 Corollary

  Every finite lattice is complete.

  If I had the above formalizations, I could then upgrade them into
  an instance of a `CompleteLattice`.

  `TODO`: define an instance of `CompleteLattice P` from `[Lattice P]`
  and `[Fintype P]`. This might involve altering the above lemmas not
  to rely on `sSup` existing in general.
-/

instance example_2_25a' [Nonempty P] [SemilatticeInf P] [Fintype P] : OrderBot P where
  bot := Finset.inf' (Finset.univ : Finset P) Finset.univ_nonempty id
  bot_le := λ a => Finset.inf'_le id (Finset.mem_univ a)

instance example_2_25b' [Nonempty P] [SemilatticeSup P] [Fintype P] : OrderTop P where
  top := Finset.sup' (Finset.univ : Finset P) Finset.univ_nonempty id
  le_top := λ a => Finset.le_sup' id (Finset.mem_univ a)

noncomputable
instance example_2_25a [Nonempty P] [Lattice P] [Fintype P] : SupSet P where
  sSup := λ S ↦ if h : S.toFinset.Nonempty then fSup h else fInf Finset.univ_nonempty


lemma example_2_25b [Nonempty P] [Lattice P] [Fintype P] (S : Set P) :
    IsLUB S (sSup S) := by
  dsimp [sSup]
  split_ifs with h
  · have lub := fSup.isLUB h
    rw [Set.coe_toFinset] at lub
    exact lub
  · have e : S = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at h
      exact Set.toFinset_eq_empty.mp h
    subst e
    simp only [isLUB_empty_iff, IsBot]
    intro b
    exact fInf.inf _ (Finset.mem_univ b)

noncomputable
instance example_2_25c [Nonempty P] [Lattice P] [Fintype P] : CompleteSemilatticeSup P where
  le_sSup := λ S ↦ example_2_25b S|>.1
  sSup_le := λ S ↦ example_2_25b S|>.2

noncomputable
instance instNonemptyFintypeCompleteLattice [Nonempty P] [Lattice P] [Fintype P] : CompleteLattice P :=
  completeLatticeOfCompleteSemilatticeSup P

/- example [IsEmpty P] : CompleteSemilatticeSup P where
  sSup := λ S ↦ by
    have e : S = ∅ := Set.eq_empty_of_isEmpty S
 -/


/-!
  ## 2.26 Definition

  Let `P` and `Q` be partially ordered sets, and `φ : P → Q` a map.
  Then we say that `φ` "preserves existing joins" if whenever
  `sSup S` exists in `P`, then `sSup (φ S)` exists in `Q` and
  `φ (sSup S) = sSup (φ S)`. The dual definition is obvious.

  This is very similar to Mathlib's `sSupHom` that is a map `φ`together
  with a proof that `∀ (s : Set P), φ (sSup s) = sSup (φ '' s)`. (Here
  `φ ''` extends `φ : P → Q` to a map `Set P → Set Q`.) The difference
  is that in the text, `sSup` need not be defined on all sets.

  In general, instead of `sSup`, I should just assert `x : P` such that
  `IsLUB S x`, etc.

  `TODO`: Figure out if I can better formalize some of the material in
  Chapter 2 to avoid the use of type classes when they are not warranted.
-/


/-!
  ## 2.27 Lemma

  Let `P` and `Q` be ordered sets and `φ : P →o Q` be an order preserving
  map.

  (i) Assume that `S ⊆ P` is such that it has a LUB `pu` in `P` and
  `φ '' S` has a LUB `qu` in `Q`. Then `qu ≤ φ pu`. Dually,
  `φ pl ≤ ql` when the GLBs `pl` and `ql` exists for `S` and `φ '' S`
  respectively.
-/

lemma example_2_27_ia [PartialOrder P] [PartialOrder Q] (φ : P →o Q)
    (S : Set P) {pu : P} {qu : Q} (plub : IsLUB S pu) (qlub : IsLUB (φ '' S) qu) :
    qu ≤ φ pu := by
  rw [isLUB_le_iff qlub]
  intro x xmem
  obtain ⟨y, hy1, hy2⟩ := xmem
  subst x
  mono
  exact plub.1 hy1

/-- Upgrade the above to complete lattices. -/
lemma example_2_27_ia' [CompleteLattice P] [CompleteLattice Q] (φ : P →o Q)
    (S : Set P) : sSup (φ '' S) ≤ φ (sSup S) :=
  example_2_27_ia φ S (isLUB_sSup S) (isLUB_sSup (φ '' S))

lemma example_2_27_ib [PartialOrder P] [PartialOrder Q] (φ : P →o Q)
    (S : Set P) {pl : P} {ql : Q} (pglb : IsGLB S pl) (qglb : IsGLB (φ '' S) ql) :
    φ pl ≤ ql := by
  rw [le_isGLB_iff qglb]
  intro x xmem
  obtain ⟨y, hy1, hy2⟩ := xmem
  subst x
  mono
  exact pglb.1 hy1

lemma example_2_27_ib' [CompleteLattice P] [CompleteLattice Q] (φ : P →o Q)
    (S : Set P) : φ (sInf S) ≤ sInf (φ '' S) :=
  example_2_27_ib φ S (isGLB_sInf S) (isGLB_sInf (φ '' S))

/-!
  (ii) Assume now that `φ : P ≃o Q` is an order-isomorphism. Then `φ`
  preserves all existing joins and meets.
-/

lemma example_2_27_iia [PartialOrder P] [PartialOrder Q] (φ : P ≃o Q) :
    ∀ S pu, IsLUB S pu → IsLUB (φ '' S) (φ pu) := by
  intro S pu plub
  constructor
  · intro x xmem
    obtain ⟨y, hy1, hy2⟩ := xmem; subst x
    apply φ.map_rel_iff'.mpr
    exact plub.1 hy1
  · intro x xmem
    rw [←φ.right_inv x]
    apply φ.map_rel_iff'.mpr
    rw [isLUB_le_iff plub]
    intro y ymem
    apply φ.map_rel_iff'.mp
    simp
    have hy : φ y ∈ φ '' S := by simp_all
    exact xmem hy

lemma example_2_27_iia' [CompleteLattice P] [CompleteLattice Q] (φ : P ≃o Q) :
    ∀ S, φ (sSup S) = sSup (φ '' S) := by
  intro S
  have h := example_2_27_iia φ S (sSup S) (isLUB_sSup S)
  apply (isLUB_iff_sSup_eq.mp h).symm

lemma example_2_27_iib [PartialOrder P] [PartialOrder Q] (φ : P ≃o Q) :
    ∀ S pl, IsGLB S pl → IsGLB (φ '' S) (φ pl) := by
  intro S pl pglb
  constructor
  · intro x xmem
    obtain ⟨y, hy1, hy2⟩ := xmem; subst x
    apply φ.map_rel_iff'.mpr
    exact pglb.1 hy1
  · intro x xmem
    rw [←φ.right_inv x]
    apply φ.map_rel_iff'.mpr
    rw [le_isGLB_iff pglb]
    intro y ymem
    apply φ.map_rel_iff'.mp
    simp
    have hy : φ y ∈ φ '' S := by simp_all
    exact xmem hy

lemma example_2_27_iib' [CompleteLattice P] [CompleteLattice Q] (φ : P ≃o Q) :
    ∀ S, φ (sInf S) = sInf (φ '' S) := by
  intro S
  have h := example_2_27_iib φ S (sInf S) (isGLB_sInf S)
  apply (isGLB_iff_sInf_eq.mp h).symm

/-!
  ## 2.28 Lemma

  Let `Q` be a subset, with the induced order, of some ordered set `P`, and
  let `S ⊆ Q`. If `S` has a least upper bound `p` in `P`, then `p ∈ Q` and
  `p` is the least upper bound in `Q`.
-/

lemma example_2_28a [PartialOrder P] (Q : Set P) (S : Set Q)
    (p : P) (h : IsLUB (S : Set P) p) (mem : p ∈ Q) :
    IsLUB S (⟨p, mem⟩ : Q) := by
  constructor
  · intro s smem
    apply Subtype.mk_le_mk.mpr
    exact h.1 (Set.mem_image_of_mem _ smem)
  · intro q qmem
    apply Subtype.mk_le_mk.mpr
    apply h.2
    intro x hx
    rw [Set.mem_image] at hx
    obtain ⟨x', mem', hx'⟩ := hx
    subst x
    apply qmem mem'

lemma example_2_28b [PartialOrder P] (Q : Set P) (S : Set Q)
    (p : P) (h : IsGLB (S : Set P) p) (mem : p ∈ Q) :
    IsGLB S (⟨p, mem⟩ : Q) := @example_2_28a Pᵒᵈ _ _ _ _ (IsGLB.dual h) _

/-!
  ## 2.29 Corollary

  Let `𝔏` be a family of subsets of a set `X` and let `{A i | i : ι}` be
  a subset of `𝔏`.

  (i) If `⋃ (i : I), A i ∈ 𝔏`, then it is the least upper bound of the
  family of sets.
-/

lemma example_2_29_i (𝔏 : Set (Set X)) (A : ι → Set X)
    (sub : {A i | i : ι} ⊆ 𝔏) (union : ⋃ (i : ι), A i ∈ 𝔏) :
    @IsLUB 𝔏 _ { A i | i : ι } ⟨(⋃ (i : ι), A i), union⟩ := by
  apply example_2_28a
  constructor
  · intro S Smem y ymem
    simp at Smem
    obtain ⟨i, eq⟩ := Smem.1
    rw [Set.mem_iUnion]
    use i; subst S
    exact ymem
  · intro S Smem x xmem
    simp [upperBounds] at Smem
    rw [Set.mem_iUnion] at xmem
    obtain ⟨i, xmem⟩ := xmem
    apply Smem i _ xmem
    apply sub
    simp

/-!
  (ii) If `⋂ (i : ι), {A i | i : ι} ∈ 𝔏` then it is the greatest lower
  bound of the family of sets.
-/

lemma example_2_29_ii (𝔏 : Set (Set X)) (A : ι → Set X)
    (sub : {A i | i : ι} ⊆ 𝔏) (inter : ⋂ (i : ι), A i ∈ 𝔏) :
    @IsGLB 𝔏 _ { A i | i : ι } ⟨(⋂ (i : ι), A i), inter⟩ := by
  apply example_2_28b
  constructor
  · intro S Smem x xmem
    simp [upperBounds] at Smem
    rw [Set.mem_iInter] at xmem
    obtain ⟨i, eq⟩ := Smem.1; subst S
    exact xmem i
  · intro S Smem y ymem
    rw [Set.mem_iInter]
    intro i
    apply Smem _ ymem
    simp
    apply sub
    simp

/-!
  ## 2.30 Lemma

  Let `P` be an ordered set with `sInf` defined for every nonempty
  subset of `P`. (I.e., every nonempty subset has a GLB.) Then
  `sSup` is defined for every subset `S` of `P` that has an upper
  bound in `P`. (In fact, sSup S = sInf (Sᵘ))
-/

def example_2_30 [PartialOrder P]
    (infs : Π S : Set P, S.Nonempty → { x // IsGLB S x }) :
    Π (S : Set P), (Sᵘ).Nonempty → { y // IsLUB S y } := by
  intro S ne
  obtain ⟨x, hx1, hx2⟩ := infs Sᵘ ne
  use x
  constructor
  . intro p pmem
    exact hx2 (λ a a ↦ a pmem)
  · exact hx1

/-!
  ## 2.31 Theorem

  Let `P` be a non-empty ordered set. Then the following are equivalent.

  (i) `P` is a complete lattice

  (ii) `sInf` exists in `P` for every subset `S` of `P`

  (iii) `P` has a top element `⊤`, and `sInf` exists in `P` for
  every non-empty subset `S` of `P`.
-/

def example_2_31_i_ii [CompleteLattice P] :
    Π (S : Set P), { x // IsGLB S x } := λ S ↦ ⟨sInf S, isGLB_sInf S⟩

/- lemma example_2_31_i_ii (h : CompleteLattice P) : ∀ S : Set P,
    ∃ x, IsGLB S x := by
  intro S
  use (sInf S)
  exact isGLB_sInf S  -/

def example_2_31_ii_iiia [PartialOrder P]
    (h : Π (S : Set P), {x // IsGLB S x}) : OrderTop P :=
  {
    top := (h ∅).val
    le_top := by
      intro a
      have h2 := (h ∅).property
      simp at h2
      apply h2
  }

def example_2_31_ii_iiib [PartialOrder P]
    (h : Π (S : Set P), {x // IsGLB S x}) :
    Π (S : Set P), S.Nonempty → {x // IsGLB S x} := λ S _ ↦ h S

/- lemma example_2_31_ii_iii' [PartialOrder P] (h : ∀ S : Set P, ∃ x, IsGLB S x) :
    (∃ _ : OrderTop P, true) ∧ ∀ S : Set P, S.Nonempty → ∃ x, IsGLB S x := by
  constructor
  · obtain ⟨x, hx⟩ := h ∅
    use {
      top := x
      le_top := by
        intro a
        obtain ⟨_, hx2⟩ := hx
        simp at hx2
        apply hx2
        simp
    }
  · intro S _
    exact h S  -/

def example_2_31_ii_i [PartialOrder P]
    (h : Π S : Set P, {x // IsGLB S x}) : CompleteLattice P :=
  have h' := example_2_31_ii_iiib h
  haveI : OrderTop P := example_2_31_ii_iiia h
  have supne : ∀ S : Set P, (Sᵘ).Nonempty := by
    intro S
    use ⊤
    intro a _
    exact le_top
  {
    inf := λ a b ↦ h (Set.insert a {b})
    sup := λ a b ↦ example_2_30 h' ({a, b}) (supne {a, b})
    inf_le_left := by
      intro a b
      have h1 := (h (Set.insert a {b})).property
      apply h1.1
      exact Set.mem_insert a {b}
    inf_le_right := by
      intro a b
      have h1 := (h (Set.insert a {b})).property
      apply h1.1
      apply Set.mem_insert_of_mem
      simp
    le_sup_left := by
      intro a b
      have h1 := (example_2_30 h' (Set.insert a {b}) (supne {a, b})).property
      apply h1.1
      exact Set.mem_insert a {b}
    le_sup_right := by
      intro a b
      have h1 := (example_2_30 h' (Set.insert a {b}) (supne {a, b})).property
      apply h1.1
      apply Set.mem_insert_of_mem
      simp
    sup_le := by
      intro a b c ac bc
      have h1 := (example_2_30 h' (Set.insert a {b}) (supne {a, b})).property
      apply h1.2
      intro x hx
      cases hx <;> subst x <;> assumption
    le_inf := by
      intro c a b ca cb
      have h1 := (h (Set.insert a {b})).property
      apply h1.2
      intro x hx
      cases hx <;> subst x <;> assumption
    sInf := λ S ↦ h S
    sSup := λ S ↦ example_2_30 h' S (supne S)
    sInf_le := by
      intro S a amem
      have h1 := (h S).property
      simp
      exact h1.1 amem
    le_sInf := by
      intro S a ble
      have h1 := (h S).property
      simp
      apply h1.2
      exact ble
    le_sSup := by
      intro S a amem
      have h1 := (example_2_30 h' S (supne S)).property
      simp
      exact h1.1 amem
    sSup_le := by
      intro S a ble
      have h1 := (example_2_30 h' S (supne S)).property
      simp
      apply h1.2
      exact ble
    bot := example_2_30 h' ∅ (supne ∅)
    le_top := this.le_top
    bot_le := by
      intro x
      have h1 := (example_2_30 h' ∅ (supne ∅)).property
      simp
      apply h1.2
      simp
  }

noncomputable
def example_2_31_iii_ii [PartialOrder P] [ot : OrderTop P]
    (h : Π S : Set P, S.Nonempty → { x // IsGLB S x }) :
    Π S : Set P, { x // IsGLB S x } := λ S ↦ by
  by_cases ne : S.Nonempty
  · exact h S ne
  · rw [Set.nonempty_iff_ne_empty] at ne
    simp at ne
    subst S
    have : IsGLB (∅ : Set P) ⊤ := by simp
    exact ⟨⊤, this⟩

noncomputable
def example_2_31_iii_i [PartialOrder P] [ot : OrderTop P]
  (h : Π S : Set P, S.Nonempty → { x // IsGLB S x }) :
  CompleteLattice P := by
  have h' := example_2_31_iii_ii h
  exact example_2_31_ii_i h'

/-!
  ## 2.32 Corollary

  Let `X` be a set and let `𝔏` be a family of subsets ordered by inclusion
  such that

  (a) `∀ ι (A : ι → Set X), { A i | i : ι} ⊆ 𝔏 → ⋂ (i : ι), A i ∈ 𝔏`

  (b) `X ∈ 𝔏`.

  Then 𝔏 is a complete lattice in which `⨅ (i : ι), A i = ⋂ (i : ι), A i`
  and `⨆ (i : ι), A i = ⋃₀ { B ∈ 𝔏 | ⋃ (i : ι), A i ⊆ B}`
-/

noncomputable
def example_2_32 (𝔏 : Set (Set X)) (h1 : (Set.univ : Set X) ∈ 𝔏)
    (h2 : ∀ (ι : Type 0) [Inhabited ι] (A : ι → Set X), { A i | i : ι } ⊆ 𝔏 → ⋂ (i : ι), A i ∈ 𝔏) :
    CompleteLattice 𝔏 := by
  have ot : OrderTop 𝔏 :=
    {
      top := ⟨(Set.univ : Set X), h1⟩
      le_top := by
        intro a x _; simp
    }
  have h3 : Π S : Set 𝔏, S.Nonempty → { x // IsGLB S x } := by
    intro S nes
    set A : S → Set X := λ X ↦ X.val with hA
    have HA : ∀ S, A ↑S = ↑↑S := by
      intro S1
      rw [hA]
    have sub : { A i | i : S } ⊆ 𝔏 := by
      intro x ⟨i, hi⟩; subst x
      rw [hA]; simp
    have : Nonempty S := Set.Nonempty.to_subtype nes
    inhabit ↥S
    have g := h2 ↥S A sub
    refine' ⟨⟨⋂ (i : S), A i, g⟩, _⟩
    constructor
    · intro x xmem y ymem
      simp at ymem ⊢
      set x' : S := ⟨x, xmem⟩ with Hx'
      have hx' := HA x'
      specialize ymem ↑↑x' (Subtype.mem x) xmem
      rw [hx', Hx'] at ymem
      exact ymem
    · intro x xmem y ymem i imem
      obtain ⟨a, b, ha⟩ := imem
      beta_reduce
      have ha := Subtype.mem a
      specialize xmem ha
      specialize xmem ymem
      rw [HA a]
      exact xmem
  exact example_2_31_iii_i h3

/-!
  ## 2.33 Definitions

  If `𝔏` is a non-empty family of subsets of `X` which satisfies condition (a) of
  `example_2_32` (i.e., `h2` in the lemma statement), then `𝔏` is called an
  "intersection structure". If `𝔏` also satisfies (b) (i.e., `h1`) then it is
  called a "topped intersection structure".

  Mathlib does not seem to have classes for these concepts. It would be instructive
  to make some here, since the text is likely to return to them frequently enough.
  I will probably not build a robust API around them, however, unless that becomes
  more obviously helpful.
-/

class InterStructure (𝔏 : Set (Set X)) where
  ne : 𝔏.Nonempty
  inter : ∀ (ι : Type 0) [Inhabited ι] (A : ι → Set X), { A i | i : ι } ⊆ 𝔏 → ⋂ (i : ι), A i ∈ 𝔏

class ToppedInterStructure (𝔏 : Set (Set X)) extends InterStructure 𝔏 where
  univ_mem : (Set.univ : Set X) ∈ 𝔏

/-!
  Just to test that these classes are working ok, I will prove 2.32 again for
  `ToppedInterStructure`s.
-/

noncomputable
def example_2_33 {𝔏 : Set (Set X)} [Inst : ToppedInterStructure 𝔏] : CompleteLattice 𝔏 :=
  example_2_32 𝔏 Inst.univ_mem Inst.inter

/-!
  ## 2.34 Examples

  (1) Consider `X → Option Y` where we assume `X.Nonempty` and `Y.nonempty`. From observations
  in 1.10, the map `λ π ↦ graph π` is an order-embedding of `X → Option Y` into `Set (X × Y)`.
  Let `𝔏` be the family of subsets of `X × Y` which are graphs of partial maps. To prove that
  `𝔏` is cloased under intersections, use the characterization given in 1.10: if
  `S ⊆ X × Y`, then `S ∈ 𝔏` if and only if `(s, y) ∈ S` and `(s, y') ∈ S` imply `y = y'`.
  So we can make `𝔏` a (topless) InterStructure. If `∣Y∣ = 1` it is actually topped.
-/
@[simp]
def graph {Y : Type} (f : X → Option Y) : Set (X × Y) := { (x, y) | f x = some y }

def example_2_34_1b {Y : Type} : (X → Option Y) ↪o Set (X × Y) :=
  {
    toFun := λ π ↦ graph π
    inj' := by
      intro f g eq
      ext x y
      constructor <;> intro mem
      · have xymemf : (x, y) ∈ graph f := by simpa
        simp_all
      · have xymemf : (x, y) ∈ graph f := by simp_all
        simp at xymemf; assumption
    map_rel_iff' := by
      intro f g
      constructor <;> intro le
      · simp at le
        intro x eq
        rw [Option.isSome_iff_exists] at eq
        obtain ⟨y, hy⟩ := eq
        specialize le x y hy
        rw [hy, le]
      · intro xy xymem
        simp_all
        have is : Option.isSome (f xy.1) = true := by
          rw [Option.isSome_iff_exists]
          use xy.2
        specialize @le xy.1 is
        rw [← le]; assumption
  }

lemma example_2_34_1c {Y : Type} (S : Set (X × Y)) :
    (∀ x y y', (x, y) ∈ S → (x, y') ∈ S → y = y') ↔ ∃ π : X → Option Y, S = graph π := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x
      by_cases e : ∃ y, (x, y) ∈ S
      · let a := Exists.choose e
        exact some a
      · exact none
    · ext ⟨x, y⟩
      constructor
      · intro mem
        dsimp only [graph, Set.mem_setOf_eq]
        split_ifs with e
        · simp
          apply h x e.choose y e.choose_spec mem
        · apply e ⟨y, mem⟩
      · intro mem
        simp only [graph, Option.dite_none_right_eq_some, Option.some.injEq,
            Set.mem_setOf_eq] at mem
        obtain ⟨e, he⟩ := mem
        rw [←he]
        exact e.choose_spec
  · intro ⟨π, h⟩ x y y' mem1 mem2
    simp_all

def example_2_34_1 {Y : Type} [Inhabited X] [Inhabited Y]
    : InterStructure { graph π | π : X → Option Y } :=
  {
    ne := ⟨{}, λ _ ↦ none, by simp⟩
    inter := by
      simp only [Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff,
        Set.mem_setOf_eq]
      -- Let {Sᵢ} be a family of sets such that each one is the graph of some πᵢ
      intro ι inh S sub
      -- Show there is some partial function π whose graph is ⋂ i, Sᵢ
      refine ⟨?_, ?_⟩
      -- We define π as follows
      · intro x
        -- For any x, decide if there is a y so that all the Sᵢ have (x, y) as a member.
        by_cases e : ∃ y, (∀ i, (x, y) ∈ S i)
          -- If so, define π(x) to be such a y (using Exists.choose)
        · exact some e.choose
          -- Otherwise, π(x) is undefined
        · exact none
      -- We now prove that graph π = ⋂ i, Sᵢ
      · ext ⟨x, y⟩
        constructor
        -- Assume (x, y) ∈ graph π
        · intro eq
          -- Let Sᵢ be any set of the family. We must show (x, y) ∈ Sᵢ
          intro Si imem
          obtain ⟨i, hi⟩ := imem
          rw[←hi]; dsimp only
          -- Since (x, y) ∈ graph π, the choice function gives a y', s.t. (x, y') is in each Sᵢ
          -- and y' = y
          simp only [graph, Option.dite_none_right_eq_some, Option.some.injEq,
              Set.mem_setOf_eq] at eq
          obtain ⟨e, he⟩ := eq
          have hec := e.choose_spec i
          -- Since (x, y') ∈ Sᵢ and y' = y, (x, y) ∈ Sᵢ
          rwa [he] at hec
        -- Conversely, assume (x, y) ∈ ⋂ i, Sᵢ
        · intro con; simp only [Set.mem_iInter] at con
          -- To show that (x, y) ∈ graph π, we must show that there is a y' s.t.
          -- (x, y') is in each Sᵢ and that y' = y.
          simp only [graph, Option.dite_none_right_eq_some, Option.some.injEq, Set.mem_setOf_eq]
          refine ⟨?_, ?_⟩
          -- We first show there is a y' s.t. (x, y') in in each Sᵢ, with y as witness
          · use y
          -- We now show that the choice function is unique, i.e. we get the y we need
          · let e : ∃ y, ∀ i, (x, y) ∈ S i := ⟨y, con⟩
            -- Since ι is inhabited, we know the choice function gives us y' s.t.
            -- (x, y') ∈ Sᵢ for some default i
            obtain h :=  e.choose_spec default
            -- And we know (x, y) ∈ Sᵢ as well, by assumption
            specialize con default
            -- But since Sᵢ is the graph of some πᵢ, (x, y) and (x, y') are in the same graph
            obtain ⟨p, hp⟩ := sub default
            unfold graph at hp
            rw [←hp] at h con
            -- So y' = y
            simp [Set.mem_setOf_eq] at h con
            rw [h] at con
            rwa [Option.some.injEq] at con
  }

/-!
  (2) We decline to formalize this list as it involves other mathematical structures
  beyond the scope of the current project.

  (3) Same here.

  (4) Same here.

  Given a `PartialOrder P` and a map `F : P → P` an element `x ∈ P` is called a
  "fixpoint" of `F` if and only if `F x = x`. Fixpoints are treated in detail in
  Chapter 8. For now we state and prove the following famous theorem.
-/

/-!
  ## 2.35 The Knaster-Tarski Fixpoint Theorem

  Let `L` be a complete lattice and `F : L → L` an order preserving map. Then
  `α := sSup { x : L | x ≤ F x }` is a fixpoint of `F`. Further, `α` is the
  greatest fixpoint of `F`. Dually, `F` has a least fixpoint given by
  `β := sInf { x : L | F x ≤ x }`.
-/

theorem knasterTarskiFixpoint_a [CompleteLattice L] (F : L →o L) :
    F (sSup { x | x ≤ F x }) = sSup { x | x ≤ F x } := by
  let H := { x | x ≤ F x }
  let A := sSup H
  have h : ∀ x ∈ H, x ≤ A ∧ x ≤ F x ∧ F x ≤ F A :=
    λ x mem ↦ ⟨le_sSup mem, mem, F.monotone (le_sSup mem)⟩
  have A_le : A ≤ F A := sSup_le λ x mem ↦ (h x mem).2.1.trans (h x mem).2.2
  have FA_le : F A ≤ A := le_sSup (F.monotone A_le)
  exact le_le_iff_eq.mp ⟨FA_le, A_le⟩

theorem knasterTarskiFixpoint_b [CompleteLattice L] (F : L →o L) :
    ∀ x, (F x = x) → x ≤ sSup { x | x ≤ F x } := by
  intro x fp
  symm at fp
  apply le_of_eq at fp
  exact le_sSup fp

theorem knasterTarskiFixpoint_dual_a [CompleteLattice L] (F : L →o L) :
    F (sInf { x | F x ≤ x }) = sInf { x | F x ≤ x } := by
  exact @knasterTarskiFixpoint_a Lᵒᵈ _ (OrderHom.dual F)

theorem knasterTarskiFixpoint_dual_b [CompleteLattice L] (F : L →o L) :
    ∀ x, (F x = x) → sInf { x | F x ≤ x } ≤ x := by
  exact @knasterTarskiFixpoint_b Lᵒᵈ _ (OrderHom.dual F)

/-!
  These are indeed in Mathlib, albeit in a slightly different form. Mathlib has
  `OrderHom.gfp F` that is an OrderHom from monotone maps on `L` to `L`. It
  maps `F` to `sSup { x | x ≤ F x }`. Similarly, it has `OrderHom.lfp F` that
  takes `F` to its least fixed point. To show this is a fixed point,
  it has `OrderHom.isFixedPt_lfp`. It also has the fact it is the least fixed
  point by `OrderHom.isLeast_lfp` and also `OrderHom.lfp_le_fixed`. Oddly,
  there is no equivalent `OrderHom.fixed_le_gfp` although it does have
  `OrderHom.isGreatest_gfp`.
-/

/-!
  # Chain conditions and completeness

  I skipped the proof that every finite lattice is complete. However, there are
  weaker finiteness conditions that already guarantee a lattice is complete. This
  section introduces those.
-/

/-!
  ## 2.37 Definitions

  Let `P` be an ordered set.

  (i) If `C = {c₀, c₁, cₙ}` is a finite chain in `P` with `∣C∣ = n + 1` then we
  say that the "length" of `C` is `n`. (I.e., it's the number of uses of `⋖`.)

  (ii) `P` is said to have "length" `n`, written `ℓ(P) = n`, if the length of
  the longest chain in `P` is `n`.

  (iii) `P` is of "finite length" if it has length `n` for some `n : ℕ`.

  (iv) `P` has "no infinite chains" if every chain in `P` is finite.

  (v) `P` satisfies the "ascending chain condition", (ACC), if and only if
  given any sequence `x₁ ≤ x₂ ≤ ... ≤ xₙ ≤ ...` of elements of `P`, there
  exists `k : ℕ` such that `xₖ = xₖ₊₁ = ...`. The dual of the ascending
  chain condition is the descending chain condition (DCC).

  Mathlib has `Set.chainHeight : Set P → ℕ∞` which is supremum over
  all finite chains `l`, of the length of `l`. This is essentially (ii)
  above (except it works on `Set P`, so we have to feed it `Set.univ`).
  We can use this to define a predicate saying `P` is of finite length,
  giving us (iii). An infinite chain in `P` is essentially (the image of)
  an order embedding of ℕ into `P`. We can thus express (iv) by saying that
  there does not exist an OrderEmbedding of ℕ into `P`.
  The ACC or DCC does not seem to be defined
  explicitly in Mathlib, however, there is `WellFounded.monotone_chain_condition`
  which says that `(⬝ > ⬝)` is well founded if and only if
  `∀ (a : ℕ →o P), ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → a n = a m`. That means that
  we can usually just substitute `WellFounded (· > ·)` for ACC. But for
  this study, we will express it explicitly, and use the above to prove the
  equivalence. We also explicitly spell out the DCC in the definition
  and show that it is the same (by `rfl`) as the ACC in the dual order.
-/

noncomputable def Order.length (P : Type) [PartialOrder P] : ℕ∞ :=
  Set.chainHeight (Set.univ : Set P)

def Order.FiniteLength (P : Type) [PartialOrder P] : Prop :=
  Order.length P ≠ ⊤

@[reducible]
def Order.NoInfiniteChains' (P : Type) [PartialOrder P] : Prop :=
  ¬∃ _ : ℕ ↪o P, true

@[reducible]
def Order.NoInfiniteChains (P : Type) [PartialOrder P] : Prop :=
  ∀ Q : Set P, IsChainLE ↑Q → Finite Q

@[reducible]
def Order.ACC (P : Type) [PartialOrder P] : Prop :=
  ∀ (f : ℕ →o P), ∃ n : ℕ, ∀ (m : ℕ), n ≤ m → f n = f m

@[reducible]
def Order.DCC (P : Type) [PartialOrder P] : Prop :=
  ∀ (f : ℕ →o Pᵒᵈ), ∃ n : ℕ, ∀ (m : ℕ), n ≤ m → f n = f m

lemma Order.ACC_dual_iff (P : Type) [PartialOrder P] :
    Order.ACC Pᵒᵈ ↔ Order.DCC P := by rfl

lemma Order.DCC_dual_iff (P : Type) [PartialOrder P] :
    Order.DCC Pᵒᵈ ↔ Order.ACC P := by rfl

lemma WellFoundedGT_iff_ACC [PartialOrder P] :
    WellFounded ((· > ·) : P → P → Prop) ↔ Order.ACC P :=
  WellFounded.monotone_chain_condition

lemma WellFoundedLT_iff_DCC [PartialOrder P] :
    WellFounded ((· < ·) : P → P → Prop) ↔ Order.DCC P :=
  @WellFounded.monotone_chain_condition Pᵒᵈ _

lemma Order.NoInfiniteChains.Dual {P : Type} [PartialOrder P] :
    Order.NoInfiniteChains P → Order.NoInfiniteChains Pᵒᵈ := by
  simp [NoInfiniteChains]
  intro h Q ch
  set Q' := { OrderDual.ofDual q | q ∈ Q } with hQ
  have : Q ≃ Q' := by
    refine Set.BijOn.equiv ?f ?h
    · intro pd; exact OrderDual.ofDual pd
    · constructor
      · intro p
        simp [Q']
      · constructor
        · intro a amem b bmem
          simp
        · intro a amem
          simp [Q'] at amem ⊢
          assumption
  have ch' : IsChainLE Q' := by
    simp [IsChainLE, IsChain] at ch ⊢
    intro a amem b bmem ne
    have amem' : OrderDual.toDual a ∈ Q := by simp [Q'] at amem; assumption
    have bmem' : OrderDual.toDual b ∈ Q := by simp [Q'] at bmem; assumption
    specialize ch amem' bmem' ne
    exact id (Or.symm ch)
  specialize h { OrderDual.ofDual q | q ∈ Q } ch'
  rw [←hQ] at h
  exact (Equiv.finite_iff (id this.symm)).mp h

lemma Order.NoInfiniteChains.Dual_iff {P : Type} [PartialOrder P] :
    Order.NoInfiniteChains P ↔ Order.NoInfiniteChains Pᵒᵈ :=
  ⟨Order.NoInfiniteChains.Dual, Order.NoInfiniteChains.Dual⟩

lemma Order.no_strict_inc_of_ACC [PartialOrder P] (acc : Order.ACC P) (f : P → P) (p : P) :
    ¬∀ p, p < f p := by
  by_contra h
  let g : ℕ → P := Nat.rec p fun _ ↦ f
  have hg : ∀ n, g n < g (n + 1) := by intro n; exact h (g n)
  let G : ℕ →o P := ⟨g, StrictMono.monotone <| strictMono_nat_of_lt_succ hg⟩
  obtain ⟨n, hn⟩ := acc G
  specialize hn (n + 1) (by simp)
  specialize hg n
  have : ∀ n, G n = g n := by intro n; rfl
  rw [this n, this (n + 1)] at hn
  rw [hn] at hg
  exact (lt_self_iff_false (g (n + 1))).mp hg

lemma Order.no_strict_dec_of_DCC [PartialOrder P] (dcc : Order.DCC P) (f : P → P) (p : P) :
    ¬∀ p, f p < p := Order.no_strict_inc_of_ACC dcc f p

lemma Order.no_strict_inc_on_of_ACC [PartialOrder P] (acc : Order.ACC P) (A : Set P) (f : A → A) (p : A) :
    ¬∀ p, p < f p := by
  by_contra h
  let g : ℕ → A := Nat.rec p fun _ ↦ f
  have hg : ∀ n, g n < g (n + 1) := by intro n; exact h (g n)
  let G : ℕ →o P := ⟨λ a ↦ (g a).val, StrictMono.monotone <| strictMono_nat_of_lt_succ hg⟩
  obtain ⟨n, hn⟩ := acc G
  specialize hn (n + 1) (by simp)
  specialize hg n
  have hg' : (g n).val < (g (n + 1)).val := by exact h (g n)
  have : ∀ n, G n = (g n).val := by intro n; rfl
  rw [this n, this (n + 1)] at hn
  rw [hn] at hg'
  apply (lt_self_iff_false (g (n + 1))).mp hg'

lemma Order.no_strict_dec_on_of_DCC [PartialOrder P] (dcc : Order.DCC P) (A : Set P) (f : A → A) (p : A) :
    ¬∀ p, f p < p := Order.no_strict_inc_on_of_ACC dcc A f p



/-!
  ## 2.38 Examples

  (1) A lattice of finite length has no infinite chains, and so satisfies both ACC
  and DCC. (This is one of those deceptively hard things to work with.)
-/

lemma example_2_38_1a [Finite P] [PartialOrder P] : Order.ACC P := by
  rw [←WellFoundedGT_iff_ACC, ←isWellFounded_iff]
  exact @Finite.to_wellFoundedGT P _ _

lemma example_2_38_1b [Finite P] [PartialOrder P] : Order.DCC P :=
  @example_2_38_1a Pᵒᵈ _ _

/-!
  (2) The lattice of ℕ under the divides relation satisfies DCC but not ACC.

  I forget where this lattice instance is defined. So I skip it for now.

  TODO: Define a type synonym for ℕ that has the lattice structure
  for divides on it.

  (3) ℕ under the normal order satisfies DCC but not ACC. Dually, ℕᵒᵈ satisfies
  ACC but not DCC.
-/

lemma example_2_38_3a : Order.DCC ℕ := by
  rw [←WellFoundedLT_iff_DCC]
  exact wellFounded_lt

lemma example_2_38_3b : ¬ Order.ACC ℕ := by
  simp [Order.ACC]
  use ⟨λ n ↦ 2^n, by apply pow_right_mono₀; simp⟩
  intro n
  use n + 1, by simp, by simp

lemma example_2_38a_dual : Order.ACC ℕᵒᵈ := example_2_38_3a

lemma example_2_38b_dual : ¬Order.DCC ℕᵒᵈ := example_2_38_3b

/-!
  (4) This is about dimensions of vector spaces which I will skip for now.
-/

/-!
  ## 2.39 Lemma

  A partial order `P` satisfies ACC if and only if every non-empty
  subset `A` of `P` has a maximal element.

  The text defers a formal proof until chapter 10, but I tackle it here.
  They note that the proof requires the axiom of choice.
-/

lemma example_2_39 [PartialOrder P] : Order.ACC P ↔
    ∀ A : Set P, A.Nonempty → ∃ a, Maximal (· ∈ A) a := by
  constructor
  · contrapose
    -- Assume there is a nonempty set A with no maximal element, and that ACC holds.
    intro nmax acc
    push_neg at nmax
    simp only [Order.ACC] at acc
    obtain ⟨A, ne, h⟩ := nmax
    -- Since A is nonempty, it has some element p.
    obtain ⟨p, hp⟩ := ne
    simp only [Maximal, not_and, not_forall, Classical.not_imp] at h
    -- We mimic the Mathlib proof for orders with no maximal elements.
    -- This is given by the typeclass NoMaxOrder, which A satisfies.
    have nmo : NoMaxOrder A := by
      constructor
      intro a
      obtain ⟨b, hb1, hb2, hb3⟩ := h a <| Subtype.coe_prop a
      exact ⟨⟨b, hb1⟩, lt_of_le_not_le hb2 hb3⟩
    -- Using the axiom of choice, we can construct a strictly increasing function g: A → A
    choose g hg using fun x : A => exists_gt x
    -- From g, we construct f: ℕ → A by f 0 = p, f (n + 1) = f (g n).
    let f : ℕ → A := Nat.rec ⟨p, hp⟩ fun _ ↦ g
    -- Since g is strictly monotone, so is f,
    have smf : StrictMono f := strictMono_nat_of_lt_succ fun n ↦ hg _
    -- and so it must also be (weekly) monotone.
    have mf : Monotone f := by exact StrictMono.monotone smf
    -- Thus we can promote f to the order homomorphism needed by ACC.
    let h : ℕ →o P :=
    {
      toFun := λ n => (f n).1
      monotone' := by
        intro a b le
        apply mf le
    }
    -- From ACC we obtain an n : ℕ, after which h becomes constant
    obtain ⟨n, hn⟩ := acc h
    -- Since h is strictly monotone, this will be a contradiction.
    -- In particular, consider n and n + 1. By ACC h n = h (n + 1).
    specialize hn (n + 1) (by simp)
    -- But by monotonicity of h, h n < h (n + 1)
    have hn' : h n < h (n + 1) := smf (by simp : n < n + 1)
    -- This contradicts irreflexivity of <.
    rw [hn] at hn'
    exact lt_irrefl _ hn'
  · contrapose
    -- Assume ACC doesn't hold, and prove there is a set without a maximal element.
    intro acc; push_neg
    simp only [Order.ACC, not_forall, not_exists, Classical.not_imp] at acc
    -- Since ACC doesn't hold, there is a monotone f that doesn't stabilze.
    obtain ⟨f, hf⟩ := acc
    -- We take the range of f to be the set without a maximal element.
    use (Set.range f), ⟨f 0, by simp⟩
    -- To show there's no maximal element, consider any element a, and assume it's maximal.
    intro a ⟨⟨N, hN⟩, h2⟩
    -- Using the property of f, we get M > N (where f N = a) and f N ≠ f M
    obtain ⟨M, hM, eq⟩ := hf N
    -- Since f is monotone, we know f N ≤ f M.
    have le := f.monotone' hM
    -- But since, a = f N is assumed maximal, this implies f M ≤ f N
    specialize h2 (by simp : f M ∈ Set.range f)
    rw [←hN] at h2
    specialize h2 le
    -- But this means, f M = f N, contradicting the definition of M witnessing instability of f.
    exact eq <| eq_of_le_of_le le h2

/-- This alternative proof uses the built-in `WellFounded.wellFounded_iff_has_min`
    together with the proof above that `ACC` and `WellFounded` are equivalent. The API for
    `WellFounded` is quite robust, so it is advantageous to convert to `WellFounded` whenever
    possible. -/
lemma example_2_39' [PartialOrder P] : Order.ACC P ↔
    ∀ A : Set P, A.Nonempty → ∃ a, Maximal (· ∈ A) a := by
  rw [←WellFoundedGT_iff_ACC]
  constructor
  · intro wf
    rw [WellFounded.wellFounded_iff_has_min] at wf
    intro A ne
    obtain ⟨m, mem, hm⟩ := wf A ne
    use m
    use mem
    intro y hy le
    specialize hm y hy
    apply le_of_eq
    exact eq_iff_le_not_lt.mpr ⟨le, hm⟩|>.symm
  · rw [WellFounded.wellFounded_iff_has_min]
    intro max A ne
    obtain ⟨m, mem, hm⟩ := max A ne
    use m, mem
    intro a amem gt
    specialize hm amem (le_of_lt gt)
    rw [gt_iff_lt] at gt
    exact not_lt_of_le hm <| gt

/-- Here is an alternate proof of the forward direction that leverages the
    result above saying that ACC is incompatible with any function
    `f : A → A` such that `A ⊆ P` and `∀ a ∈ A, a < f a`. -/
lemma example_2_39a [PartialOrder P] : Order.ACC P →
    ∀ A : Set P, A.Nonempty → ∃ a, Maximal (· ∈ A) a := by
  contrapose
  intro nmax acc
  push_neg at nmax
  obtain ⟨A, ⟨p, hp⟩, h⟩ := nmax
  simp only [Maximal, not_and, not_forall, Classical.not_imp] at h
  choose g hg using h
  let f : A → A := λ a ↦ ⟨g a.1 a.2, (hg a.1 a.2).choose⟩
  apply Order.no_strict_inc_on_of_ACC acc A f ⟨p, hp⟩
  intro ⟨q, hq⟩
  simp only [f]
  obtain ⟨mem, ⟨le, nle⟩⟩ := hg q hq
  exact lt_of_le_not_le le nle

/-!
  ## 2.40 Theorem

  A partial order `P` has no infinite chains, if and only if it satisfies
  both ACC and DCC.
-/

theorem example_2_40mp [PartialOrder P] :
    Order.NoInfiniteChains P → Order.ACC P ∧ Order.DCC P := by
  intro h
  constructor
  · intro f
    by_contra h1
    push_neg at h1
    let h2 : ∀ p : Set.range f, ∃ q, p < q := by
      intro ⟨p, ⟨n, hn⟩⟩
      obtain ⟨m, hm1, hm2⟩ := h1 n
      use ⟨f m, by simp⟩
      simp; rw [←hn]
      have lt := f.monotone' hm1
      exact lt_of_le_of_ne lt hm2
    choose g hg using h2
    let g' : ℕ → Set.range f := Nat.rec ⟨(f 0), by simp⟩ fun _ ↦ g
    simp [Order.NoInfiniteChains] at h
    specialize h (Set.range f)
    have finf : IsChainLE (Set.range f) := by
      simp [IsChainLE, IsChain, Pairwise]
      intro x ⟨n, xmem⟩ y ⟨m, ymem⟩ ne
      cases Nat.lt_trichotomy n m with
      | inl h =>
        apply le_of_lt at h
        apply f.monotone' at h
        rw [←xmem, ←ymem]
        left; assumption
      | inr h => cases h with
      | inl h => subst h; rw [xmem] at ymem; contradiction
      | inr h =>
        apply le_of_lt at h
        apply f.monotone' at h
        rw [←xmem, ←ymem]
        right; assumption
    apply h at finf
    have noMax : NoMaxOrder (Set.range f) := by
      constructor
      intro a
      use ⟨g a, by simp⟩, hg a
    have inff : Infinite (Set.range f) := NoMaxOrder.infinite
    exact not_finite ↑(Set.range ⇑f)
  · intro f
    by_contra h1
    push_neg at h1
    let h2 : ∀ p : Set.range f, ∃ q, p < q := by
      intro ⟨p, ⟨n, hn⟩⟩
      obtain ⟨m, hm1, hm2⟩ := h1 n
      use ⟨f m, by simp⟩
      simp; rw [←hn]
      have lt := f.monotone' hm1
      exact lt_of_le_of_ne lt hm2
    choose g hg using h2
    let g' : ℕ → Set.range f := Nat.rec ⟨(f 0), by simp⟩ fun _ ↦ g
    apply Order.NoInfiniteChains.Dual at h
    simp [Order.NoInfiniteChains] at h
    specialize h (Set.range f)
    have finf : IsChainLE (Set.range f) := by
      simp [IsChainLE, IsChain, Pairwise]
      intro x ⟨n, xmem⟩ y ⟨m, ymem⟩ ne
      cases Nat.lt_trichotomy n m with
      | inl h =>
        apply le_of_lt at h
        apply f.monotone' at h
        rw [←xmem, ←ymem]
        left; assumption
      | inr h => cases h with
      | inl h => subst h; rw [xmem] at ymem; contradiction
      | inr h =>
        apply le_of_lt at h
        apply f.monotone' at h
        rw [←xmem, ←ymem]
        right; assumption
    apply h at finf
    have noMax : NoMaxOrder (Set.range f) := by
      constructor
      intro a
      use ⟨g a, by simp⟩, hg a
    have inff : Infinite (Set.range f) := NoMaxOrder.infinite
    exact not_finite ↑(Set.range ⇑f)


/-- What a beast to prove! I have a feeling there is a 2-3 liner available if I use
    use stuff from Mathlib. There may even be a way to shorten this argument. But
    this is the general structure of the proof in the book. -/
theorem example_2_40mpr [PartialOrder P] :
    Order.ACC P ∧ Order.DCC P → Order.NoInfiniteChains P := by
  intro ⟨acc, dcc⟩
  intro Q hQ
  by_contra infQ; simp [Finite] at infQ
  have neQ : Q.Nonempty := Set.Nonempty.of_subtype

  -- We proceed by finding a max x₀ of Q, then a max x₁ of Q \ {x}, etc.
  -- The idea is that { q ∈ Q | xᵢ ≤ q } will be finite for each of these xᵢ.
  -- Since { q ∈ Q | q < xᵢ } is the rest of Q, that will be infinite, allowing
  -- us to use choice to build a decreasing function on Q.

  -- First we show that for any x, Q = { q ∈ Q | q < x ∨ x ≤ q }. Why is this so long?
  have hAll : ∀ x : Q, Q = { q ∈ Q | q < x } ∪ { q ∈ Q | x ≤ q } := by
    intro x
    ext z
    constructor
    · intro zmem
      simp [IsChainLE, IsChain] at hQ
      specialize hQ x.2 zmem
      by_cases eq : x = z
      · subst eq; simp
      · specialize hQ eq
        cases hQ with
        | inl hq => simp; right; use zmem, hq
        | inr hq =>
            simp; left; use zmem; obtain ⟨x, hx⟩ := x; simp at eq ⊢; exact lt_of_le_of_ne hq fun a => eq (id (Eq.symm a))
    · intro zmem
      cases zmem with
      | inl zmem => exact zmem.1
      | inr zmem => exact zmem.1

  -- This is where we argue that if the upper set of the split is finite, the lower one must be infinite
  have key : ∀ x : { q ∈ Q | Finite { q' ∈ Q | q ≤ q' } }, Infinite { q ∈ Q | q < x } := by
    intro ⟨x, xmem, finX⟩
    rw [Set.infinite_coe_iff] at infQ ⊢
    rw [Set.finite_coe_iff] at finX
    by_contra finY
    rw [Set.not_infinite] at finY
    specialize hAll ⟨x, xmem⟩
    have finQ : ({ q ∈ Q | q < x} ∪ { q' ∈ Q | x ≤ q'}).Finite := Set.Finite.union finY finX
    rw [←hAll] at finQ
    exact infQ finQ

  -- This is the heart of the proof. By showing that there is always a smaller element of Q, we can
  -- later use choice to build the decreasing function.
  have next : ∀ x : { q ∈ Q | Finite { q' ∈ Q | q ≤ q' } }, ∃ y, y < x := by
    intro x
    -- We want to take y to be the maximum of Iio x guranteed by 2_39. This step secretly uses
    -- Infinitude of { q ∈ Q | q < x } to infer it's nonempty. That is, it uses key.
    obtain ⟨y, ⟨⟨ymem, lt⟩, ymax⟩⟩ := example_2_39.1 acc { q ∈ Q | q < x } Set.Nonempty.of_subtype
    -- This is the y we want. We are given y ∈ Q, and y < x. So it only remains to show that
    -- { q ∈ Q | y ≤ q } is finite.
    refine ⟨⟨y, ymem, ?_⟩, lt⟩
    -- Since y was maximal below x, the elements above y are either y or also above x.
    have seq : { q ∈ Q | y ≤ q } = Set.insert y { q ∈ Q | x ≤ q } := by
      ext p
      constructor
      · intro pmem
        obtain ⟨pmem, lt'⟩ := pmem
        simp [le_iff_lt_or_eq] at lt'
        cases lt' with
        | inl lt' =>
            simp [Set.insert]
            right
            simp [IsChainLE, IsChain] at hQ
            use pmem
            specialize hQ x.2.1 pmem
            by_cases eq : ↑x = p
            · exact le_of_eq eq
            · specialize hQ eq
              cases hQ with
              | inl hQ => exact hQ
              | inr hQ =>
                  have ltpx : p < x := by exact lt_of_le_of_ne hQ fun a => eq (id (Eq.symm a))
                  specialize ymax ⟨pmem, ltpx⟩ (le_of_lt lt')
                  exfalso
                  simp at lt' ymax
                  exact not_lt_of_le ymax lt'
        | inr eq => simp [Set.insert]; left; exact eq.symm
      · intro pmem
        simp [IsChainLE, IsChain] at hQ ⊢
        cases pmem with
        | inl eq => subst eq; use ymem
        | inr pmem =>
            use pmem.1
            exact (le_of_lt lt).trans pmem.2
    rw [seq]
    -- Since the set of elements above x is finite,
    have finX := x.2.2
    -- So is the set of elements above x together with y.
    apply Finite.Set.finite_insert
  -- We can thus build a decreasing function
  choose g hg using next
  -- To use the fact that decreasing functions are incompatible with DCC, we need an element
  -- of the set, which we can get by taking the max according to 2_39.
  have x := example_2_39.1 acc Q neQ
  obtain ⟨x, ⟨xmem, hx⟩⟩ := x
  -- To prove x is in the set, we need to show the set of elements above it is finite.
  have finX : Finite { q ∈ Q | x ≤ q } := by
    have sing : { q ∈ Q | x ≤ q } = {x} := by
      ext a
      constructor
      · intro ⟨amem, lt⟩
        specialize hx amem lt
        apply eq_of_le_of_le hx at lt
        simpa
      · intro amem
        simp at amem ⊢
        subst amem
        use xmem
    rw [sing]
    exact Finite.of_subsingleton
  -- We thus get our contradiction
  apply Order.no_strict_dec_on_of_DCC dcc { q ∈ Q | Finite { q' ∈ Q | q ≤ q' } } g ⟨x, ⟨xmem, finX⟩⟩ hg

/-!
  ## 2.41 Theorem

  Let `P` be a lattice.

  (i) If `P` satisfies ACC, then for every non-empty subset `A ⊆ P` there
      exists a finite subset `F ⊆ A` such that `sSup A = sSup F`.

  (ii) If `P` has a bottom element and satisfies ACC, then `P` is complete.

  (iii) If `P` has no infinite chains, then `P` is complete.
-/

theorem example_2_41_i [Lattice P] (acc : Order.ACC P) (A : Set P) (neA : A.Nonempty) :
    ∃ F : Finset P, ∃ neF : F.Nonempty, ↑F ⊆ A ∧ IsLUB A (fSup neF) := by
  let B := { x | ∃ F : Finset P, ∃ neF : F.Nonempty, ↑F ⊆ A ∧ x = fSup neF}
  have neB : B.Nonempty := by
    obtain ⟨a, amem⟩ := neA
    use a
    simp only [exists_and_left, Set.mem_setOf_eq, B]
    use {a}
    push_cast
    use (Set.singleton_subset_iff.mpr amem), Finset.singleton_nonempty a
    exact Eq.symm (fSup_singleton (Finset.singleton_nonempty a))
  obtain ⟨m, ⟨⟨F, neF, hF1, hF2⟩, hm2⟩⟩ := example_2_39a acc B neB
  use F, neF, hF1
  rw [IsLUB_iff]
  constructor
  · intro a amem
    let Fa := F ∪ {a}
    have FaSub : ↑Fa ⊆ A := by
      intro x xmem
      simp only [Finset.coe_union, Finset.coe_singleton, Set.union_singleton, Set.mem_insert_iff,
        Finset.mem_coe, Fa] at xmem
      cases xmem with
      | inl eq => subst eq; exact amem
      | inr xmem => exact hF1 xmem
    have FaNe : Fa.Nonempty := ⟨a, by simp [Fa]⟩
    have FsubFa : F ⊆ Fa := Finset.subset_union_left
    set x := fSup FaNe with hx
    have xmem : x ∈ B := by
      simp only [exists_and_left, Set.mem_setOf_eq, B]
      exact ⟨Fa, ⟨FaSub, ⟨FaNe, by simp⟩⟩⟩
    have le : m ≤ x := by
      simp only [fSup] at hF2 hx
      exact example_2_22_va' F Fa.toSet FsubFa (fSup.isLUB_of_eq neF hF2)
          (fSup.isLUB_of_eq FaNe hx)
    have meqx : m = x := eq_of_le_of_le le (hm2 xmem le)
    have alem : a ≤ m := by
      rw [meqx]
      apply fSup.sup FaNe
      simp [Fa]
    exact hF2 ▸ alem
  · intro x xmem
    have xlubF : x ∈ Fᵘ := by exact fun ⦃a⦄ a_1 => xmem (hF1 a_1)
    have mlub : IsLUB F m := by exact fSup.isLUB_of_eq neF hF2
    simp [IsLUB, IsLeast] at mlub
    exact hF2 ▸ mlub.2 xlubF

lemma example_2_41_ii [Lattice P] [OrderBot P] (acc : Order.ACC P) :
    Nonempty (CompleteLattice P) :=
  ⟨example_2_31_iii_i (P := Pᵒᵈ)
    (λ S ne ↦
      let neF := example_2_41_i acc S ne|>.choose_spec|>.choose
      let ⟨_, hF2⟩ := example_2_41_i acc S ne|>.choose_spec|>.choose_spec
      ⟨fSup neF, hF2⟩)⟩

/-!
    To show part (iii), the text claims that if `P` has no infinite chains
    then it has a bottom element.
 -/

noncomputable
instance Order.NoInfiniteChains.OrderBot [Lattice P] (ne : Nonempty (Set.univ : Set P)) (h : Order.NoInfiniteChains P) :
    OrderBot P where
  bot := by
    obtain wf := WellFoundedLT_iff_DCC.mpr  <| (example_2_40mp h).2
    exact WellFounded.min wf _ (Set.nonempty_coe_sort.1 ne)
  bot_le := by
    obtain wf := WellFoundedLT_iff_DCC.mpr  <| (example_2_40mp h).2
    intro a
    simp only [WellFounded.min, Set.mem_univ, forall_const, true_and]
    let exmin := wf.has_min _ (Set.nonempty_coe_sort.1 ne)
    obtain ⟨h1, h2⟩ := (exmin).choose_spec
    let x := exmin.choose ⊓ a
    have lem : x ≤ exmin.choose := inf_le_left
    have lea : x ≤ a := inf_le_right
    specialize h2 x trivial
    have eq : x = exmin.choose := eq_of_le_of_not_lt lem h2
    rw [eq] at lea
    simp only [Set.mem_univ, forall_const, true_and] at lea
    exact lea

lemma example_2_41_iii [Lattice P] (ne : Nonempty (Set.univ : Set P)) (h : Order.NoInfiniteChains P) :
    Nonempty (CompleteLattice P) :=
  haveI : OrderBot P := Order.NoInfiniteChains.OrderBot ne h
  example_2_41_ii (example_2_40mp h).1

/-!
  # Join-irreducible elements

  We look at join-irreducible elements in analogy with primes which are
  product-irreducible elements.

  ## 2.42 Definitions

  Let `L` be a lattice, an element `x ∈ L` is "join-irreducible" if

  (i) `x ≠ 0` (in case `L` has a zero)

  (ii) `∀ a b, x = a ⊔ b → x = a ∨ x = b`

  Condition (ii) is equivalent to the more pictorial

  (ii') `∀ a b, a < x → b < x → a ⊔ b < x`
-/

@[simp]
def Order.IsSupIrreducible [Lattice P] (x : P) : Prop :=
  (¬IsBot x) ∧
  (∀ a b, x = a ⊔ b → x = a ∨ x = b)

@[simp]
def Order.IsSupIrreducible' [Lattice P] (x : P) : Prop :=
  (¬IsBot x) ∧
  (∀ a b, a < x → b < x → a ⊔ b < x)

lemma Order.IsSupIrreducible_equiv [Lattice P] (x : P) :
    Order.IsSupIrreducible x ↔ Order.IsSupIrreducible' x := by
  constructor
  · intro ⟨h1, h2⟩
    use h1
    intro a b lta ltb
    specialize h2 a b
    cases eq_or_lt_of_le <| sup_le (le_of_lt lta) (le_of_lt ltb) with
    | inl eq =>
        specialize h2 eq.symm
        cases h2 with
        | inl ha => subst ha; exfalso; exact (lt_self_iff_false x).mp lta
        | inr hb => subst hb; exfalso; exact (lt_self_iff_false x).mp ltb
    | inr eq => exact eq
  · intro ⟨h1, h2⟩
    use h1
    intro a b eq
    subst eq
    specialize h2 a b
    have h3 : a ≤ a ⊔ b := le_sup_left
    apply eq_or_lt_of_le at h3
    cases h3 with
    | inl eq => left; exact eq.symm
    | inr lt =>
      specialize h2 lt
      have h4 : b ≤ a ⊔ b := le_sup_right
      apply eq_or_lt_of_le at h4
      cases h4 with
      | inl eq => right; exact eq.symm
      | inr lt => specialize h2 lt; exfalso; exact (lt_self_iff_false (a ⊔ b)).mp h2

/-!
  The meet-irreducible elements are defined dually. I will defer that work
  until I learn that I'll need it.

  For now, we continue to define the set of all join-irreducible elements
-/
def Order.𝒥 (P : Type) [Lattice P] : Set P := { x : P | Order.IsSupIrreducible x }

def Order.SupDense [Lattice P] (Q : Set P) : Prop :=
    ∀ a : P, ∃ A ⊆ Q, IsLUB A a

/-!
  ## 2.43 Examples of join-irreducible elements

  (1) Every non-zero element of a chain (linear order) is join-irreducible. Consequently,
      if `L` is an `n`-element chain, then `Order.𝒥 P` is an `(n - 1)`-element chain.
-/

lemma example_2_43_1a [LinearOrder L] (x : L) (nz : ¬IsBot x) :
    Order.IsSupIrreducible x := by
  use nz
  intro a b eq
  rw [eq]
  cases lt_trichotomy a b with
  | inl lt => right; exact sup_eq_right.2 (le_of_lt lt)
  | inr h => cases h with
    | inl eq => subst eq; left; exact max_self a
    | inr lt => left; exact sup_eq_left.2 (le_of_lt lt)

def example_2_43_1b {n : ℕ} : LinearOrder (Order.𝒥 (Fin n)) := by
  infer_instance

instance instFinOrderBot {n : ℕ} : OrderBot (Fin (n + 1)) where
  bot := ⟨0, by simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]⟩
  bot_le := by
    intro ⟨k, hk⟩
    simp only [Fin.mk_le_mk, zero_le]

lemma example_2_43_1c {n : ℕ} {x : Fin (n +1)} :
    x ∈ Order.𝒥 (Fin (n + 1)) ↔ x ≠ ⟨0, by simp only [lt_add_iff_pos_left, add_pos_iff,
      zero_lt_one, or_true]⟩ := by
  constructor
  · intro ⟨h1, h2⟩
    intro eq
    rw [eq] at h1
    apply h1
    intro ⟨k, hk⟩
    simp only [Fin.zero_eta, Fin.zero_le]
  · intro ne
    have nbot : ¬IsBot x := by
      intro bt
      specialize bt ⟨0, by simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]⟩
      simp at bt ne
      exact ne bt
    constructor
    · exact nbot
    · exact (example_2_43_1a x nbot).2

lemma example_2_43_2 [Nonempty L] [Lattice L] [Fintype L] {x : L} :
    Order.IsSupIrreducible x ↔ ∃! m, m ⋖ x := by
  constructor
  · intro ⟨nbot, h⟩
    simp [IsBot] at nbot
    obtain ⟨b, hb⟩ := nbot
    have nebot : ⊥ ≠ x := by
      intro eq
      subst eq
      exact hb bot_le
    have botle : ⊥ ≤ x := bot_le
    obtain botlt := lt_of_le_of_ne botle nebot
    obtain ⟨m, hm⟩ := Fintype.exists_covBy_of_lt' botlt
    use m, hm
    intro y cb


    sorry
  · intro ⟨m, hm1, hm2⟩
    constructor
    · intro bt
      specialize bt m
      simp only at hm1 hm2
      exact not_lt_of_le bt (CovBy.lt hm1)
    · intro a b eq
      by_cases h : a = b
      · subst h
        simp at eq
        tauto
      · have ale : a ≤ a ⊔ b := le_sup_left
        have ble : b ≤ a ⊔ b := le_sup_right
        rw [←eq] at ale ble
        sorry
