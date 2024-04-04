import OrderTheory.Exercises01

open scoped Classical 

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
  # 2.1 Defintions
  
  Let `P` be a partial order and let `S ⊆ P` be a subset of `P`. An element 
  `x ∈ P` is an upper bound of `S` if and only if for all `s ∈ S`, `s ≤ x`. A 
  lower bound is natrually defined dually. 
  
  I can't find a separate predicate in Mathlib to say `x` is an upper bound
  of a set `S`. But it does contain notation for the set of all upper (and lower)
  bounds of a set. These are denoted `upperBounds` and `lowerBound` respectively. 
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
  as the least element of upperBounds. The following formulation is equivalent:
  
  (i) `x` is an upper bound of `S` and 
  (ii) for all upper bounds `y` of `S`, `x ≤ y` 
-/

/-- This seems to be true essentially by definition in Mathlib -/
theorem IsLUB_iff [PartialOrder P] (S : Set P) {x : P} : 
    IsLUB S x ↔ x ∈ Sᵘ ∧ ∀ y ∈ Sᵘ, x ≤ y := by exact Eq.to_iff rfl

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
    · intro h 
      exact lub.2 h 
    · intro le s mem
      exact (lub.1 mem).trans le 
  · intro ⟨x, h⟩
    use x 
    constructor
    · intro s mem
      specialize h x 
      simp at h 
      exact h s mem
    · intro y mem
      specialize h y 
      exact h.mp mem 

/-!
  Of course the greatest lower bound works dually. It is denoted `IsGLB S x` in Mathlib.
  
  The text uses the notation `⋁S` for the least upper bound of a set (\bigvee) and
  `⋀S` (\bigwedge) for the greatest lower bound when these exist. Mathlib uses `sSup` and 
  `sInf` (set supremum and infimum) for these. 
-/

/-!
  # 2.2 Top and bottom
  
  
-/
