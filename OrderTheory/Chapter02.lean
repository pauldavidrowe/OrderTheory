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
  # 2.3 Notation
  
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
  # 2.4 Definitions 
  
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
  # 2.5 Remarks on ⊔ and ⊓
  
  (1) If `(x :P) ≤ y` then `{x, y}ᵘ = ↑ᵖy` and `{x, y}ˡ = ↓ᵖx`. It follows that 
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
  # 2.6 Examples 
  
  (1) Every chain is a lattice. This is known to Mathlib as LinearOrder.toLattice. 
      This has a bunch of observations about ℝ, ℚ, ℤ, ℕ that follow quite naturally
      and are quite intuitive. 
      
  (2) For any type `X` the type of subsets of `X`, `Set X` is complete lattice under
      set inclusion. Mathlib seems to know this by I can't find where it is defined. 
      
-/

lemma example_2_6_2a {A : ι → Set X} : ⨆ i, A i = ⋃ i, A i := rfl 

lemma example_2_6_2b {A : ι → Set X} : ⨅ i, A i = ⋂ i, A i := rfl 

/-!
  (3) If `𝔏 : Set (Set X)`, then `𝔏` is called a lattice of sets if it is
      closed under finite unions and intersections, and complete lattice if 
      it is closed under arbitrary unions and intersections. 
-/

lemma example_2_6_3a {X : Type} (𝔏 : Set (Set X)) 
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
  Sup { S : Set X // S ∈ 𝔏} := ⟨λ S T ↦ sSup {S, T}⟩

local instance example_2_6_3InfSet {X : Type} (𝔏 : Set (Set X)) 
    (hInter : ∀ (I : Set (Set X)), I ⊆ 𝔏 → ⋂ i : I, i ∈ 𝔏) :
    InfSet { S : Set X // S ∈ 𝔏} := ⟨λ I ↦ ⟨⋂ i : I, i, by specialize hInter I; simp_all⟩⟩

local instance example_2_6_3bInf (𝔏 : Set (Set X)) 
    [InfSet { S : Set X // S ∈ 𝔏}] :
  Inf { S : Set X // S ∈ 𝔏} := ⟨λ S T ↦ sInf {S, T}⟩


    
/-- We only need to prove it's a complete semilattice with sup -/
lemma example_2_6_3b {X : Type} (𝔏 : Set (Set X)) 
    (hUnion : ∀ (I : Set (Set X)), I ⊆ 𝔏 → ⋃ i : I, i ∈ 𝔏)
    (hInter : ∀ (I : Set (Set X)), I ⊆ 𝔏 → ⋂ i : I, i ∈ 𝔏) :
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
local instance instOrderTop : OrderTop (WithTop (WithBot (Fin' n))) := 
  {
    top := none 
    le_top := by simp
  }
  
@[simp]
local instance instOrderBot : OrderBot (WithTop (WithBot (Fin' n))) := 
  { 
    bot := some none 
    bot_le := by
      intro a 
      cases a with 
      | none => simp 
      | some a => simp 
  }
    
@[simp]
noncomputable
instance instrSup : Sup (WithTop (WithBot (Fin' n))) := 
  {
    sup := λ 
      | ⊥, y => y 
      | x, ⊥ => x 
      | x, y => if x = y then x else ⊤ 
  }

@[simp]
noncomputable
local instance instInf : Inf (WithTop (WithBot (Fin' n))) :=
  {
    inf := λ
      | x, ⊤ => x
      | ⊤, y => y 
      | x, y => if x = y then x else ⊥
  }

noncomputable 
local instance instrSemilatticeSup {n : Nat} : SemilatticeSup (WithTop (WithBot (Fin' n))) := 
  {
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
      cases_type* WithTop WithBot <;> simp_all [LE.le]
  }

noncomputable 
local instance instSemilatticeInf {n : Nat} : Lattice (WithTop (WithBot (Fin' n))) :=
  {
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
      cases_type* WithTop WithBot 
      all_goals try rw [WithTop.none_eq_top] at *
      all_goals try simp_all
      all_goals try rw [WithTop.none_eq_top] at *
      all_goals try simp_all
      all_goals split_ifs
      all_goals try simp_all
      case neg x y z h
      · rw [Fin'.le_iff] at le1 le2 
        subst y; subst z
        contradiction
  }
    
