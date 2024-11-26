/-
Copyright (c) 2024 Paul D. Rowe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul D. Rowe
-/
import OrderTheory.Mathlib.lib
import Mathlib.Tactic

open scoped Classical
/-!
  # Chapter 1

  In this file, we focus on the core definitions found in Chapter 1
  of Introduction to Lattices and Order by B.A. Davey and H.A. Priestley.

  Throughout these comments, we talk frequently of definitions or theorems that
  exist in Lean. Technially, most of these exist not in the core of Lean, but in
  Mathlib, the monolithic library of mathematical definitions and results maintained
  by the Lean community. We typically gloss over the distinction between Lean and
  Mathlib since we are focused on the mathematics.

  The first chapter introduces many of the basic definitions, and presents
  numerous examples. We follow the structure of the chapter, providing pointers
  to the corresponding definitions and facts in Mathlib where they exist. In some
  cases, the textbook mentions a fact outside the context of an official lemma
  or theorem. We may choose to represent it or not according to how useful
  or relevant it seems to be.

  In the first pass, we omit many of the examples as it can be more challenging to
  represent particular examples instead of general results.
-/

/-!
  # Ordered sets
-/

/-!
  ## 1.1 Order

  This section of the text simply introduces a few intuitive examples.
  There is nothing worth formalizing in this section.
-/

/-!
  ## 1.2 Partial Orders, PreOrders, and Linear Orders

  A traditional treatment of Order Theory considers ordered sets. The formalization
  here, of course, starts from a treatment of ordered *types*, and ordered sets arise
  as a byproduct of considering subc-collections of elements of an order.

  The core notion of an ordered set P is represented in Lean as `[PartialOrder P]`.
  Whenever we talk about an order P, or an ordered set P, we implicitly mean a partial order.
  We also have the weaker notion of a quasi-ordered set or a preordered set P which
  is `[Preorder P]`. There is also the stronger notion of a total order which is
  written `[LinearOrder P]` in Lean.

  The primary thing to specify for a Partial Order is the `≤` relation. Lean automatically
  infers the strict order `<` according the usual rule: `x < y ↔ x ≤ y ∧ x ≠ y`.
-/
variable {P Q R S α X Y P₁ P₂ : Type}
universe u v

/-!
  ## 1.3 Chains and Antichains

  A chain is another name for a total or linear order. We can naturally express finite
  total orders of n elements with the type `Fin n`. These types naturally inherit a
  total order, so `≤` may be used on them as expected. Lean also has a predicate
  `IsChain : (α → α → Prop) → Set α → Prop` that works on sets instead of types. This
  takes any relation. For convenience we define it for `≤` and call it `IsChain_le`.
-/

def IsChain_le [LE P] (s : Set P) : Prop := IsChain LE.le s

/-!
  An antichain is an order in which `x ≤ y` if and only if `x = y`. To define a type
  as an antichain, one only has to define `≤` using `=`. There is also a predicate
  `IsAntichain : (α → α → Prop) → Set α → Prop` that works on sets. We also define
  this specifically for `≤` as `IsAntichain_le`.
-/

def IsAntichain_le [LE P] (s : Set P) : Prop := IsAntichain LE.le s

/-!
  The fact that a subset of a chain is also a chain is written using `IsChain.mono`. The
  corresponding fact about antichains is written as `IsAntichain.subset`.

  We can define `Fin' n` to be the type of finite antichains. That is, the type
  has n elements, and they are only related to each other via `=`.
-/

def Fin' (n : ℕ) := Fin n

instance Fin'.instPartialOrder {n : Nat} : PartialOrder (Fin' n) :=
  {
    le := (· = ·)
    le_refl := Eq.refl
    le_trans := λ a b c ↦ Eq.trans
    le_antisymm := λ a b h1 _ ↦ h1
  }

theorem Fin'.IsAntichain {n : Nat} : IsAntichain (· ≤ ·) (Set.univ : Set (Fin' n)) := by
  intro x _ y _ neq le
  apply neq
  simp [LE.le] at le
  assumption

theorem Fin'.le_iff {n : Nat} {x y : Fin' n} : x ≤ y ↔ x = y := by rfl

/-!
  ## 1.4 Order Isomorphisms

  The definition used in the text book is importantly different from the one used
  in Lean. The textbook definition of an isomorphism between Partial Orders P and Q
  is a function `φ : P → Q` such that

    * (i) `φ` is surjective and

    * (ii) `x ≤ y` if and only if `φ x ≤ φ y`.

  We include a formalization of this definition in case it makes sense to use it
  when proving two orders are isomorphic.
-/

class OrderIso' (P Q : Type*) [PartialOrder P] [PartialOrder Q] where
  toFun : P → Q
  surj' : Function.Surjective toFun
  map_rel_iff' : ∀ {a b}, toFun a ≤ toFun b ↔ a ≤ b

/-- We use `P ≃o' Q` to denote the type of `OrderIso'` between `P` and `Q`.-/
infix:100 " ≃o' " => OrderIso'

/-!
  Lean's definition of `OrderIso` requires an explicit inverse `invFun : Q → P` to be
  provided along with proofs that `invFun` forms both a left and right inverse of `toFun`.
  This style is inherently more constructive than the textbook version which is why
  it is preferred in Lean. The Lean definition is also more general in the sense that
  it does not assume P and Q are partial orders, only that they have `≤` defined.

  If we have an `OrderIso'`, we can create an `OrderIso`, but that translation is not
  computable, because the inverse of an arbitrary `OrderIso'` is obtained by instantiating
  an existential. Nonetheless, we can do it. The next two lemmas are useful for this purpose
  but are not in Mathlib.
-/

/-- In a partial order, the converse of anti-symmetry also holds. -/
lemma le_le_iff_eq [PartialOrder P] {a b : P} : a ≤ b ∧ b ≤ a ↔ a = b := by
  constructor
  · rintro ⟨h1, h2⟩
    exact PartialOrder.le_antisymm a b h1 h2
  · intro eq
    apply And.intro (le_of_eq eq)
    exact le_of_eq eq.symm

/--
  If a function preserves and reflects the order relation on two partial orders,
  then the function must be injective. In fact, the conclusion holds if we
  only assume the forward direction of `h2`. That result is called
  `injective_of_le_imp_le`, and takes the function as an explicit argument.
-/
lemma injective_of_le_iff_le [PartialOrder P] [PartialOrder Q]
    {f : P → Q} (h2 : ∀ {a b}, f a ≤ f b ↔ a ≤ b) : Function.Injective f := by
  intro a b eq
  rw [←le_le_iff_eq] at eq
  rw [@h2 a b, @h2 b a] at eq
  exact le_le_iff_eq.1 eq


/--
  Given an OrderIso', we can define (though not compute) an OrderIso.
-/
noncomputable def OrderIsoOfOrderIso' [PartialOrder P] [PartialOrder Q]
    (φ : OrderIso' P Q) : OrderIso P Q := by
  have h : Function.Bijective φ.toFun :=
        ⟨injective_of_le_imp_le φ.toFun φ.map_rel_iff'.mp, φ.surj'⟩
  rw [Function.bijective_iff_has_inverse] at h
  exact {
    toFun := φ.toFun
    invFun := h.choose
    left_inv := h.choose_spec.left
    right_inv := h.choose_spec.right
    map_rel_iff' := φ.map_rel_iff'
  }

/-!
  For the most part we will work with Lean's `OrderIso`, but we may prefer `OrderIso'`
  in cases where we want to mimic a proof found in the textbook.

  The inverse of an `OrderIso`, `φ`, is denoted `φ.symm`. This is a full `OrderIso`
  structure that comes equipped with all the necessary proofs that it is also
  an order isomorphism.
-/

/-!
  ## 1.5 Number systems

  The number systems ℝ, ℚ, and ℕ all form total orders. Lean has already defined
  default instances of these `LinearOrder`s. One detail to watch out for is that
  the textbook defines ℕ as excluding 0 and writes ℕ₀ to denote the natural numbers
  with 0. In Lean, ℕ includes 0, so we will do the same.

  We can define a different partial order on ℕ as `m ≤ n` if and only if `m` divides `n`,
  (written `m ∣ n`). Since this is not the default order on ℕ in Lean, we show how to
  define it here.
-/

def instNatDivPartialOrder : PartialOrder ℕ :=
  {
    le := λ m n ↦ m ∣ n
    lt := λ m n ↦ m ∣ n ∧ ¬ n ∣ m
    le_refl := Nat.dvd_refl
    le_trans := λ a b c ↦ Nat.dvd_trans
    le_antisymm := λ a b ↦ Nat.dvd_antisymm
  }

/-!
  ## 1.6 Families of sets

  The type of (sub)sets of a type P is denoted `Set P`. The set of subsets of a
  type P forms a partial order where `≤` is interpreted as `⊆`. Lean already has
  a `PartialOrder` instance for `Set P`. Beyond considering all subsets of P, we
  often consider a restricted class of subsets of P. A particularly important
  class in order theory is the down-sets of P. The textbook denotes this as `𝒪(P)`.
  We will see in 1.27 below how they are represented in Lean.

  The textbook talks about the predicates p on a type P: `p : P → Prop`. There is
  a natural correspondence between such predicates p and subsets `S : Set P`. In
  fact, in Lean, subsets of P are actually implemented as predicates under the hood.
-/

/-!
  # Examples from social science and computer science
-/

/-!
  ## 1.7 Ordered sets in the humanities and social sciences

  We will not dwell to much on these examples here. But we do point out some
  relevant definitions in Lean.

  Intervals form a strict partial order according the rule `[a, b] < [c, d]` if
  and only if `b < c` in the usual sence. Lean has defined `Interval X` to be
  the type of (closed) intervals of `X` (assuming `≤` is defined on `X`). It then also
  has a default instance showing that `Interval X` forms a partial order.

  The book mentions concept analysis as a use case for partial orders. We delay
  the introduction of Formal Concepts until Chapter 3, noting for now simply
  that Lean has...

  TODO: Check what the order is on `Interval X`
-/

/-!
  ## 1.8 Programs

  There are no details in the textbook that naturally point us to any particular
  definitions for this section. Examples of datatypes and programs come in the
  next few subsections.
-/

/-!
  ## 1.9 Binary Strings

  Binary strings are finite lists of 0s and 1s. We can represent the type of finite
  binary strings in Lean as `List (Fin 2)`. Here, `List α` is the type of (finite)
  lists of some type α. We take lists over `Fin 2` which is the finite type of naturals
  less than 2, (i.e., 0 and 1). We can generalize over arbitrary types, α, not just
  `Fin 2`, of course. Finite lists form a partial order according to
  `x ≤ y` if and only if `x` is a prefix of `y`. The prefix relation is denoted
  `x <+: y`. This does not appear to be a default instance in Lean, so we define
  it here. It seems that Lean already knows the prefix relation is transitive, so
  we start by showing it is reflexive and antisymmetric.
-/

theorem List.IsPrefix.refl (a : List α) : a <+: a := by use []; simp

theorem List.IsPrefix.antisymm {a b : List α}: a <+: b → b <+: a → a = b := by
  intro h1 h2
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨b1, h2⟩ := h2
  subst b;
  rw [append_assoc] at h2
  nth_rewrite 2 [←append_nil a] at h2
  rw [append_cancel_left_eq, append_eq_nil] at h2
  rw [h2.left]; simp

instance List.instListPartialOrder {α : Type} : PartialOrder (List α) :=
  {
    le := λ x y ↦ x <+: y
    le_refl := IsPrefix.refl
    le_trans := λ a b c ↦ IsPrefix.trans
    le_antisymm := λ a b ↦ IsPrefix.antisymm
  }

/-!
  Dealing with possibly infinite lists is somewhat more complicated. One way of
  representing a possibly infinite list is as a `Stream`. Definitely infinite
  lists are somewhat easier as we can represent them as functions `l : ℕ → α`.
  This is the underlying implementation in Lean of `Stream'`. However, possibly
  infinite lists are an important type for order theory because they are often
  used to represent the output of computations, some of which terminate (finite
  lists), and some of which do not (infinite lists).

  TODO: Figure out how to work with streams and define a `PartialOrder` instance
  on streams.
-/

/-!
  ## 1.10 Partial maps

  A partial map `f : X → Y` is a map that may not be defined on all terms in X.
  In Lean, this is naturally represented by the type `X → Option Y`. For two such
  functions `f` and `g`, we define `f ≤ g` if and only if

  (i) `g x` is defined whenever `f x` is, and

  (ii) `g x = f x` whenever `f x` is defined.

  We start by formalizing `≤`, then showing it is reflexive, transitive, and
  antisymmetric.
-/

instance Function.Option.instLE {X : Type u} {Y : Type v} : LE (X → Option Y) :=
  {
    le := λ f g ↦ ∀ {x}, (f x).isSome → (f x) = (g x)
  }

theorem Function.Option.le_refl (a : X → Option Y) : a ≤ a := by simp [LE.le]

theorem Function.Option.le_trans {a b c : X → Option Y} (h1 : a ≤ b) (h2 : b ≤ c) :
    a ≤ c := by
  intro x eq
  specialize @h1 x eq; rw [h1] at eq
  specialize @h2 x eq; rw [h1, h2]

theorem Function.Option.le_antisymm {a b : X → Option Y} (h1 : a ≤ b) (h2 : b ≤ a) :
    a = b := by
  simp [LE.le] at h1 h2
  ext x y; simp
  specialize @h1 x
  specialize @h2 x
  by_cases h : (a x).isSome
  · specialize h1 h; rw [h1]
  · by_cases h' : (b x).isSome
    · specialize h2 h'; rw [h2]
    · rw [Option.isSome_iff_exists] at h h'
      push_neg at h h'
      specialize h y
      specialize h' y
      tauto

instance Function.Option.instPartialOrder :
    PartialOrder (X → Option Y) :=
  {
    le := LE.le
    le_refl := le_refl
    le_trans := λ a b c ↦ le_trans
    le_antisymm := λ a b ↦ le_antisymm
  }

/-!
  ## 1.11 Intervals in ℝ and exact real arithmetic

  We can approximate real numbers by specifying closed interval in which it lives.
  Such intervals are naturally ordered by inclusion. Notice that this order conflicts
  with the Interval order described in 1.7. If the one in 1.7 is preferred, it must
  be declared as a local instance, possibly with a higher priority.

  A related topic is more general intervals viewed as sets of elements between the top
  and bottom of the interval. The top and bottom can each be (independently) closed, open, or
  infinite (unbounded). Such sets are denoted in Lean by the types
  `Set.Icc` `Set.Ico` `Set.Ici` `Set.Ioc` `Set.Ioo` `Set.Ioi` `Set.Iic` `Set.Iio`.
  (We don't use `Set.Iii` because that's just `Set.univ`, the set of all values of a type.)
-/

/-!
  ## 1.12 Information orderings

  The previous three sections considered orderings in which greater elements are
  "more informative" than lesser ones. Maximal elements are in a sense "totally
  defined" whereas all other elements are only partially defined. We will introduce
  notions of maximal and minimal as they are developed in the text. The total objects
  can also be viewed as limits of partial objects. We will introduce the notion
  of limits also as it arises in the text.
-/

/-!
  ## 1.13 Semantics and semantic domains

  There is not much to add for a formalization from this section. Rather there are
  several forward references to Domains and Domain Theory and the theory of Fixpoints.
-/

/-!
  # Diagrams: The art of drawing ordered sets

  This section is dedicated to the visualization of ordered sets. We generally
  will not concern ourselves with diagrams in this treatment because visualizations
  are largely to help intuition. Formalization is not well suited to visual
  intuitions.
-/

/-!
  ## 1.14 The covering relation

  An element y "covers" an element x (denoted in Lean as `x ⋖ y`) if and only if
  `x < y` and for any z such that `x ≤ z < y` we have `x = z`. That is, there are
  no elements between x and y (which are strictly ordered). The text uses the notation
  `-<` for the covers relation, but we stick to Lean's notation here.

  The text offers that in `Set X`, `A ⋖ B` if and only if `B = A ∪ {b}` for some
  `b ∉ A`. This fact is already in Lean as `Set.covby_iff_exists_insert`.

  The text also mentions in passing that, for finite orders, `x < y` if and only if
  there is a finite sequence of covering relations `x = x₀ ⋖ x₁ ⋖ ... ⋖ xₙ = y`.
  While this observation may seem obvious, it is somewhat difficult to formally prove.
  Dealing with finite sets is surprisingly hard in Lean! Since it's used later, it's
  worth stating it here and leaving it unsolved.

  TODO: Prove the finite chain condition.
-/

/-- Predicate that is true iff there are xᵢ such that x = x₀ ⋖ x₁ ⋖ ... ⋖ xₙ = y -/
def CovChain [LT P] (x y : P) : ℕ → Prop
  | 0  => x = y
  | .succ n =>  ∃ w, x ⋖ w ∧ CovChain w y n

lemma covChain_of_fintype [PartialOrder P] [Fintype P] {x y : P} :
    x < y ↔ ∃ n, CovChain x y n := sorry

/-!
  ## 1.15 Diagrams

  In this formalization we won't concern ourselves with Hasse diagrams. Their
  primary benefit is for intuitive and visual understanding. While it's possible
  to formalize them and several results about them, those results are not all
  that illuminating in themselves, so we omit them. Nevertheless, we formalize
  and prove below (relative to the unproven observation above) the key lemma in
  the proof that diagrams are legitimate. Since we don't formalize diagrams,
  we omit the final proof.

  TODO:(?) Formalize diagrmas, and prove they are legitimate (1.18)
-/

/-!
  ## 1.16 Examples

  This section is all about examples of diagrams. There is not much to formalize.
-/

/-!
  ## 1.17 Lemma

  Let P and Q be finite ordered sets and let f : P → Q be a bijective map.
  The following are equivalent:
  (i) `f` satisfies the conditions of an order isomorphism
  (ii) `∀ x y, f x < f y ↔ x < y`
  (iii) `∀ x y, f x ⋖ f y ↔ x ⋖ y`
-/

lemma orderIso_iff_image_lt_lt [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]
    [DecidableEq Q] (f : P → Q) (hf : f.Bijective) :
    (∃ φ : P ≃o Q, φ = f) ↔ (∀ x y, f x < f y ↔ x < y) := by
  constructor
  · rintro ⟨φ, eq⟩ x y; rw [←eq]; simp
  · intro h
    use
    {
      toFun := f
      invFun := Fintype.bijInv hf
      left_inv := Fintype.leftInverse_bijInv hf
      right_inv := Fintype.rightInverse_bijInv hf
      map_rel_iff' := by
        simp
        intro a b
        specialize h a b
        rw [le_iff_lt_or_eq, le_iff_lt_or_eq, h,
            Function.Injective.eq_iff hf.1]
    }
    simp

lemma image_covby_covby_of_image_lt_lt [Fintype P] [Fintype Q] [PartialOrder P]
    [PartialOrder Q] [DecidableEq Q] (f : P → Q) (hf : f.Bijective) :
    (∀ x y, f x < f y ↔ x < y) → (∀ x y, f x ⋖ f y ↔ x ⋖ y) := by
  intro h x y
  constructor
  · intro ⟨lt, nlt⟩
    constructor
    · exact (h x y).1 lt
    · by_contra h1; push_neg at h1
      obtain ⟨w, hw⟩ := h1
      apply @nlt (f w) ((h x w).2 hw.left)
      exact (h w y).2 hw.right
  · intro ⟨lt, nlt⟩
    constructor
    · exact (h x y).2 lt
    · by_contra h1; push_neg at h1
      obtain ⟨w, hw⟩ := h1
      obtain ⟨u, hu⟩ := hf.2 w
      rw [←hu] at hw
      apply @nlt u ((h x u).1 hw.left)
      exact (h u y).1 hw.right

lemma image_lt_lt_of_image_covby_covby [Fintype P] [Fintype Q] [PartialOrder P]
    [PartialOrder Q] [DecidableEq Q] (f : P → Q) (hf : f.Bijective) :
    (∀ x y, f x ⋖ f y ↔ x ⋖ y) → (∀ x y, f x < f y ↔ x < y) := by
  intro h x y
  rw [covChain_of_fintype, covChain_of_fintype]
  constructor <;> intro ⟨n, hn⟩ <;> use n <;> revert x y
  · induction n with
    | zero => intro x y hn; exact hf.1 hn
    | succ k ih =>
      intro x y ⟨w, hw, covc⟩
      use (Fintype.bijInv hf w)
      have winv : w = f (Fintype.bijInv hf w) := by
        symm; apply Fintype.rightInverse_bijInv hf
      constructor
      · rw [winv] at hw
        exact (h x _).mp hw
      · apply ih (Fintype.bijInv hf w) y
        rwa [← winv]
  · induction n with
    | zero => intro x y hn; congr
    | succ k ih =>
      intro x y ⟨w, hw, covc⟩
      exact ⟨f w, ⟨(h x w).2 hw, by apply ih w y covc⟩⟩

lemma image_lt_lt_iff_image_covby_covby [Fintype P] [Fintype Q] [PartialOrder P]
    [PartialOrder Q] [DecidableEq Q] (f : P → Q) (hf : f.Bijective) :
    (∀ x y, f x < f y ↔ x < y) ↔ (∀ x y, f x ⋖ f y ↔ x ⋖ y) :=
  ⟨image_covby_covby_of_image_lt_lt f hf, image_lt_lt_of_image_covby_covby f hf⟩

lemma orderIso_iff_image_covby_covby [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]
    [DecidableEq Q] (f : P → Q) (hf : f.Bijective) :
    (∃ φ : P ≃o Q, φ = f) ↔ (∀ x y, f x ⋖ f y ↔ x ⋖ y) := by
  rw [orderIso_iff_image_lt_lt, image_lt_lt_iff_image_covby_covby] <;> exact hf

/-!
  ## 1.18 Proposition

  Two ordered sets P and Q are order isomorphic if and only if they can be
  represented by the same diagram.

  Formalized statement and proof omitted.
-/

/-!
  # Constructing and de-constructing ordered sets
-/

/-!
  ## 1.19 The dual of an ordered set

  The dual of an ordered set consists of "reversing" the ≤ relation. In Lean,
  if P is partial order, we can represent its (order dual) as `Pᵒᵈ`. Notice how
  `P` and `Pᵒᵈ` are related:
-/

lemma example_1_19a [PartialOrder P] (x y : P) :
    OrderDual.toDual x ≤ OrderDual.toDual y ↔ y ≤ x := by simp

/-!
  In the current formalization, given `x : P` we will use `xᵈ` to represent
  `x` viewed as an element of the dual order. Note that `x : Pᵒᵈ` does not perform the
  same task because there is no coersion from `P` to `pᵒᵈ`. I suspect there is good
  reason not want to a coersion, but I wonder...

  In any case, we can thus rewrite the above example more compactly.
-/

postfix:100 "ᵈ" => OrderDual.toDual

lemma example_1_19b [PartialOrder P] (x y : P) :
    xᵈ ≤ yᵈ ↔ y ≤ x := by simp

/-!
  The importance of duals lies in the duality principle. For any statement Φ, we can
  define a dual statement Φᵒᵈ that replaces every occurrence of ≤ with ≥. Then for
  any statement Φ, if it's true in all ordered sets, then so is its dual statement
  Φᵒᵈ. This is surprisingly hard to formalize in a useful way here, because suddenly the
  statements are not just the language we use to express properties, but they become
  objects of study themselves. That is, we would need to define a type of statements.
  Furthermore, formalizing the statements wouldn't be useful in generating a dual lemma
  because the statement used in the Lean formalization would be distinct from the
  formalization of the statement itself. The best approach is simply to realize that
  whenever we prove a statement about all partial orders, we should also manually
  write the dual statement and prove it accordingly.

  TODO: Is it possible to reuse the first proof without rewriting it by first
  transferring to the dual, then applying the original theorem? Is this even a good
  thing to do from a computational point of view?
-/

/-!
  ## 1.20 Bottom and Top

  Lean has several type classes related to orders containing a bottom or top
  element. The most basic are `[Bot P]` and `[Top P]`. These are simply
  "notation type classes" that ensure we can use the notations `⊥` and `⊤`
  to represent particular elements of the type. To express that an order
  has a minimum or maximum, we use the type clasess `[OrderBot]` or
  `[OrderTop]`. Those type classes come equiped with proofs that `⊥` is
  the miminum and `⊤` is the maximum.

  For the partial order of subsets of X, the bottom element is `∅` and
  the top element is all of X. If X is a type, we denote its underlying
  set by `Set.univ : Set X`.
-/

lemma example_1_20a {X : Type u} : (⊥ : Set X) = ∅ := Set.bot_eq_empty

lemma example_1_20b {X : Type u} : (⊤ : Set X) = Set.univ := Set.top_eq_univ

/-!
  ℕ has a bottom element, namely 0, but it has no top element. ℤ has no
  bottom or top element.
-/

lemma example_1_20c : ⊥ = 0 := bot_eq_zero

/-!
  The order of finite lists has a bottom element, namely the empty list.
  The bottom element of partially defined functions is the constant function
  that always ouputs none. These are not in Lean, so we define them here.
-/

instance List.instOrderBot : OrderBot (List α) :=
  {
    bot := []
    bot_le := λ a ↦ by use a; simp only [nil_append]
  }

instance Function.Option.instOrderBot : OrderBot (X → Option Y) :=
  {
    bot := λ _ ↦ none
    bot_le := λ f ↦ by simp [LE.le]
  }

/-!
  ## 1.22 Lifting

  For any ordered set P, we can easily add a bottom element that is less than
  all other elements while leaving the remaining elements ordered as before.
  Specifically, in the new order, `x ≤ y` if and only if either `x = ⊥` or
  `x = some x'` and `y = some y'` and `x' ≤ y'` in `P`. In Lean we can transform
  any order P into one with such a bottom element with `WithBot P`. The result
  is a new type that has a bottom element. Similarly, we can write `WithTop P`
  to add a top element.

  These are both implemented as `Option P`, with `⊥ = none` in the former case
  and `⊤ = none` in the latter.
-/

/-!
  ## 1.23 Maximal and minimal elements

  An element x of an order P is maximal if and only if `∀ a : P, x ≤ a → x = a`.
  In fact, Lean uses the equivalent definition `∀ a : P, x ≤ a → a ≤ x`. This
  easily implies the first definition by antisymmetry. We write `IsMax x` to
  state that x is a maximal element of P.

  The text talks of maximal elements of `Q : Set P`, and uses the notation MaxQ
  to denote the set of maximal elements of Q. In Lean this is denote by
  `maximals (· ≤ ·) Q`. The use of `(· ≤ ·)` is required because `maximals` is
  well-defined for arbitrary binary relations.

  Of course the dual concepts are written `IsMin x` and `minimals`. -/

  def maximals_le [LE α] : Set α → Set α := maximals (· ≤ ·)

  def minimals_le [LE α] : Set α → Set α := minimals (· ≤ ·)

/-
  For any nonempty finite subset Q of an order Q both `maximals_le Q` and
  `minimals_le Q` are nonempty. Similarly, for any `x ∈ Q`, there is some
  `y ∈ maximals_le Q` such that `x ≤ y`. As with many facts about finite sets,
  these are surprisingly hard to prove.

  TODO: Prove these facts about finite sets.

  Any total function `f : X → Y` is maximal among partial functions
  `X → Option Y`.
-/

theorem Function.Option.isMax_isSome {f : X → Option Y} (hf : ∀ x, (f x).isSome) :
    IsMax f := by
  intro g le x _
  exact (le (hf x)).symm

/-!
  ## 1.24 Sums of ordered sets

  There are two primary ways of defining a partial order on the union (or sum) of
  two partial orders. The first is to take the disjoint union of P and Q
  and define `x ≤ y` if and only if either `x : P` and `y : P` and `x ≤ y`
  or `x : Q` and `y : Q` and `x ≤ y`.

  This disjoint union is denoted `P ⊕ Q` in Lean, and there is a default
  instance of `PartialOrder` defined as above.

  The other way is called a "linear sum" or "lexicographic sum" of
  P and Q. In this order, `x ≤ y` if and only if any of the following holds:

  (i) `x : P` and `y : P` and `x ≤ y`

  (ii) `x : Q` and `y : Q` and `x ≤ y`

  (iii) `x : P` and `y : Q`

  That is, the orders of both P and Q are preserved, and everything in P
  is `≤` everything in Q.

  To access this instance of the order on the sum of P and Q we can write
  `P ⊕ₗ Q` with a subscript `l` on the `⊕`. There is a translation between
  `P ⊕ Q` and `P ⊕ₗ Q` given by `toLex` (behind the scenes, Lean calls `P ⊕ₗ Q`
  `Lex (P ⊕ Q)`). The backwards translation is called `ofLex`.

  The text talks of the lifting of `P` to `WithBot P` as an instance of
  a linear sum. In fact `WithBot P ≃o PUnit ⊕ₗ P` and
  `WithTop P ≃o P ⊕ₗ PUnit`. These facts are defined in Lean as
  `WithBot.orderIsoPUnitSumLex` and `WithTop.orderIsoSumLexPUnit`.

  TODO: Why is the naming convention different? The placement of `Sum`
  in the names is not consistent.

  Both versions of sums are associative (which Lean knows), so we
  don't have to fully specify parentheses. But by default, they associate
  to the right so that `P ⊕ Q ⊕ R` is defined as `P ⊕ (Q ⊕ R)`.
-/

/-!
  ## 1.25 Products

  Given two partial orders P and Q, there are also two ways to define an
  order on the product `P × Q`. The first is the standard way and is called
  the "coordinate-wise order". In this way we define `x ≤ y` if and only if
  `x.1 ≤ y.1` and `x.2 ≤ y.2`. This is the default order put on the product
  in Lean.

  We can also define the "lexicographic order" on `P × Q` in which `x ≤ y`
  if and only if either

  (i) `x.1 < y.1` or

  (ii) `x.1 = y.1` and `x.2 ≤ y.2`

  Just as with `P ⊕ₗ Q`, Lean defines a type synonym `P ×ₗ Q` that is called
  `Lex (P × Q)` behind the scenes.
-/

/-!
  ## 1.26 Proposition

  Let X = {1, 2, ..., n} and define φ : Set X → (Fin 2)ⁿ by
  φ(A) = (ε₁, ..., εₙ) where εᵢ = if i ∈ A then 1 else 0. Then φ is an
  order-isomorphism.

  It is not clear how to denote `Pⁿ`, the n-fold product of `P`, in Lean.

  TODO: Ask on Zulip how to express the n-fold product of a type (especially
  in the context of orders.) In the meantime, the below represents
  `(Fin 2)ⁿ` as `Fin n → Prop` implicitly relying on an order-isomorphism
  between `Fin 2` and `Prop` that maps `0 ↦ False` and `1 ↦ True`.
-/

section Ch_1_26

variable {n : ℕ}

/-- Definition of forward function defining the `OrderIso` for 1.26 -/
def f {n : ℕ} (A : Set (Fin n)) : Fin n → Prop := λ i ↦ i ∈ A

/--
  Proof that φ' is an `OrderIso`. The proof of `map_rel_iff'` is
  essentially what is in the textbook, but `OrderIso` requires us to
  explicitly define the inverse, while `OrderIso'` only requires us
  to demonstrate that the function is surjective.
-/
def φ : OrderIso (Set (Fin n)) (Fin n → Prop) := {
  toFun := f
  invFun := λ s ι ↦ s ι
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_rel_iff' := by
    simp; intro A B
    rw [Set.subset_def]
    unfold f
    simp [LE.le]
}


/--
  An alternative approach that shows φ is a `OrderIso'`
-/
def φ' : OrderIso' (Set (Fin n)) (Fin n → Prop) := {
  toFun := f
  map_rel_iff' := φ.map_rel_iff'
  surj' := by
    intro s
    use { ι | s ι }
    unfold f; simp
}

end Ch_1_26

/-!
  # Down-sets and up-sets
-/

/-!
  ## 1.27 Definitions and remarks

  A down-set `Q : Set P` of a partial order P is defined by the property that
  if `x ∈ Q` and `(y : P) ≤ x`, then `y ∈ Q`. An up-set of P is defined dually.
  This is sometime called a "decreasing set" or an "order ideal". The text denotes
  the down-sets of P by 𝒪(P). Lean represents this with a type called `LowerSet P`
  which has a carrier set of type `Set P` and a proof that the down-set property
  holds. The dula notion of an up-set is called `UpperSet P` in lean. It is also
  sometimes called an "increasing set" or an "order filter". The text does provide
  a notation for `UpperSet P`. We teach Lean the 𝒪(P) notation here. So we will
  prefer the notation from the book in these notes. We also introduce the notation
  𝒪ᵈ(P) for `UpperSet P`.
-/

notation:max "𝒪("arg:25")" => LowerSet arg
notation:max "𝒪ᵈ("arg:25")" => UpperSet arg

/-
  Given `Q : Set P` we can define `{ x | ∃ y ∈ Q, x ≤ Q }` to be the downward
  closure of Q. The text denotes this as `↓Q`. In Lean this is called
  `lowerClosure Q` (dually `upperClosure Q`). We introduce `↓ˢQ` and `↑ˢQ`
  as Lean notation for `lowerClosure` and `upperClosure` respectively, where
  the superscript `s` indicates that it takes a set as an argument.
-/

prefix:100 "↓ˢ" => lowerClosure
prefix:100 "↑ˢ" => upperClosure

/- The down-set `↓ˢQ` has type `𝒪(P)`, and `↑ˢQ` has type `𝒪ᵈ(P)`.

  A "principal down-set" or "principal ideal" is the downward closure of a singleton
  set `{x}`. The text uses `↓x` to represent the principle down-set of x. The set
  `Set.Iic x` happens to be a `LowerSet`. Lean has `LowerSet.Iic x`
  that bundles `Set.Iic x` together with a proof that is a `LowerSet`.
  We introduce the notations `↓ᵖx` and `↑ᵖx` to denote the principle down- and
  up-sets `LowerSet.Iic x` and `UpperSet.Ici x` respectively.
-/

prefix:100 "↓ᵖ" => LowerSet.Iic
prefix:100 "↑ᵖ" => UpperSet.Ici

/-
  There is an equivalence between `↓ˢ{x}` and `↓ᵖx`.
-/

lemma example_1_27 [PartialOrder P] (x : P) : ↓ˢ{x} = ↓ᵖx :=
  lowerClosure_singleton x

/-!
  The text says it is easy to see that `↓ˢQ` is the smallest LowerSet
  containing Q, and that Q is a LowerSet if and only if `↓ˢQ = Q`.
  We show these (and their duals) below.
-/

theorem lowerClosure_smallest [PartialOrder P] (Q : Set P) (R : 𝒪(P)) (sub : Q ⊆ R) :
    ↓ˢQ ⊆ R := by
  intro x ⟨a, ha1, ha2⟩
  apply R.lower' ha2 (sub ha1)

theorem upperClosure_smallest [PartialOrder P] (Q : Set P) (R : 𝒪ᵈ(P)) (le : Q ⊆ R) :
    ↑ˢQ ⊆ R := by
  intro x ⟨a, ha1, ha2⟩
  apply R.upper' ha2 (le ha1)

theorem lowerClosure_eq_self_iff [PartialOrder P] (Q : Set P) :
    ↓ˢQ = Q ↔ IsLowerSet Q := by
  constructor <;> intro h
  · rw [←h]; exact (lowerClosure Q).lower'
  · exact IsLowerSet.lowerClosure h

theorem upperClosure_eq_self_iff [PartialOrder P] (Q : Set P) :
    ↑ˢQ = Q ↔ IsUpperSet Q := by
  constructor <;> intro h
  · rw [←h]; exact (upperClosure Q).upper'
  · exact IsUpperSet.upperClosure h

/-!
  # 1.28 The ordered set 𝒪(P) of down-sets

  As mentioned above, certain restricted families of `Set P` can be given
  an order structure. One important such family is 𝒪(P), the set of down-sets
  of P. It has a default instance of `PartialOrder` on it.

  When P is finite, every nonempty down-set is expressible as a finite
  union of principal down-sets. As with other facts about finite sets,
  we omit the proof of this fact (which not given in the text either).
-/

/-!
  # 1.29 Examples

  Several of the examples would not be illuminated by formalization.
  However, the text notes that if `Q ⊆ P` is an antichain, then the down-sets of
  Q are all subsets of Q. This is written `𝒪(Q) ≃o Set Q` where
  we don't use equality, but rather demonstrate an order-isomorphism.
-/

theorem LowerSet.IsAntichain [PartialOrder P] {Q : Set P} (h : IsAntichain (· ≤ ·) Q) :
    𝒪(Q) ≃o Set Q :=
  {
    toFun := LowerSet.carrier -- The coersion from LowerSet Q to Set Q
    invFun := λ s ↦
      ⟨s, by -- Must prove s is a lower set
        intro a b le mem
        rw [le_iff_lt_or_eq] at le
        cases le with
        | inl lt =>
          exfalso
          apply IsAntichain.not_lt h (by simp) (by simp) lt
        | inr eq => rw [eq]; exact mem⟩
    left_inv := λ a ↦ by simp; rfl
    right_inv := λ a ↦ by simp
    map_rel_iff' := by simp
  }

/-!
  If we consider the n-element chain `Fin n`, then 𝒪(P) consists of all principal
  lower sets ↓x together with ∅.

  This is surprisingly hard to prove. It requires more API around embedding
  `Fin n` into `Fin (n + 1)`. Currently there are order embeddings, but there is
  no API around what it does to `LowerSets`

  TODO: Add more API around LowerSets in the embedding of `Fin n` into `Fin (n + 1)`
-/

/- def LowerSet.Fin_succ_orderIso : Fin (n + 1) ≃o LowerSet (Fin n) :=
  {
    toFun := λ
      | ⟨0, _⟩ => ∅
      | ⟨k + 1, hl⟩ => Iic ⟨k, by linarith⟩
    invFun := λ ls ↦ if h : ls = ∅ then 0 else by sorry
    left_inv := sorry
    right_inv := sorry
  }

theorem LowerSet.Fin_orderIso (ls : Set (Fin n)) :
    IsLowerSet ls ↔ (ls = ∅ ∨ ∃ x, ls = (Iic x).carrier) := by
  constructor <;> intro h
  · induction n with
    | zero => left; exact Set.eq_empty_of_isEmpty ls
    | succ k ih => sorry
  · cases' h with h h
    · rw [h]; exact isLowerSet_empty
    · obtain ⟨x, hx⟩ := h; rw [hx]; exact (Iic x).lower' -/

/-!
  # 1.30 Lemma

  Let `P` be an ordered set and `x, y ∈ P`. Then the following are equivalent
  (i) `x ≤ y`
  (ii) `↓x ⊆ ↓y`
  (iii) `∀ Q : LowerSet P, y ∈ Q → x ∈ Q`
-/

theorem LowerSet.Iic_sub_iff_le [PartialOrder P] {x y : P} :
    ↓ᵖx ⊆ ↓ᵖy ↔ x ≤ y := by
  constructor <;> intro h
  · specialize @h x (Iic_mem_self x)
    exact LowerSet.mem_Iic_iff.mp h
  · intro a mem
    exact mem.trans h

theorem LowerSet.mem_of_mem_iff_Iic_sub [PartialOrder P] {x y : P} :
    (∀ Q : 𝒪(P), y ∈ Q → x ∈ Q) ↔ ↓ᵖx ⊆ ↓ᵖy := by
  constructor <;> intro h
  · intro a mem
    simp at mem
    specialize h (Iic y) (Iic_mem_self y)
    simp at h ⊢
    exact mem.trans h
  · intro Q mem
    specialize @h x (Iic_mem_self x)
    exact Q.lower' h mem

theorem LowerSet.mem_of_mem_iff_le [PartialOrder P] {x y : P} :
    (∀ Q : 𝒪(P), y ∈ Q → x ∈ Q) ↔ x ≤ y := by
  rw [mem_of_mem_iff_Iic_sub, Iic_sub_iff_le]

/-!
  # 1.31 𝒪(P) and duality

  Down-sets and up-sets are not only related by duality, but also by
  complementation. `Q` is a lower set of `P` if and only if `Qᶜ` is
  an upper set of `P` (or a lower set of `Pᵒᵈ`). This result exists in Lean
  already.
-/

lemma example_1_31a [PartialOrder P] (Q : LowerSet P) : 𝒪ᵈ(P) := LowerSet.compl Q
lemma example_1_31b [PartialOrder P] (Q : UpperSet P) : 𝒪(P) := UpperSet.compl Q

/-!
  We have `A ⊆ B` if and only if `Bᶜ ⊆ Aᶜ`.
-/

lemma example_1_31c [PartialOrder P] (A B : Set P) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  simp only [Set.compl_subset_compl]

/-!
  It follows that 𝒪(P)ᵒᵈ ≃o 𝒪(Pᵒᵈ).
-/

theorem LowerSet.dual_orderIso [PartialOrder P] :
    𝒪(P)ᵒᵈ ≃o 𝒪(Pᵒᵈ) :=
  {
    toFun := λ s ↦
      ⟨s.carrierᶜ, λ a b le memac memb ↦ memac (s.lower' le memb)⟩
    invFun := λ s ↦
      ⟨s.carrierᶜ, λ a b le memac memb ↦ memac (s.lower' le memb)⟩
    left_inv := λ s ↦ by simp only [carrier_eq_coe, _root_.compl_compl]; rfl
    right_inv := λ s ↦ by simp only [carrier_eq_coe, _root_.compl_compl]; rfl
    map_rel_iff' := by
      intro ⟨s', _⟩ ⟨t', _⟩
      constructor <;> intro h
      · intro _ mem
        change s'ᶜ ⊆ t'ᶜ at h
        rw [Set.compl_subset_compl] at h
        exact h mem
      · intro x memsc memt
        exact memsc (h memt)
  }

/-!
  # 1.32 Proposition

  This proposition is about equivalent ways to decompose a partial order.

  (ia) 𝒪(P ⊕ₗ 1) ≃o 𝒪(P) ⊕ₗ 1
  (ib) 𝒪(1 ⊕ₗ P) ≃o 1 ⊕ₗ 𝒪(P)
  (ii) 𝒪(P1 ⊕ P2) ≃o 𝒪(P1) × 𝒪(P2)

  In our formalization we choose to represent `X ⊕ₗ 1` as `WithTop X` and
  `1 ⊕ₗ X` as `WithBot X`.
-/

namespace Ch_1_32_ia

@[simp]
noncomputable def φ [PartialOrder P] : 𝒪(WithTop P) → WithTop (𝒪(P)) :=
  λ | ⟨s, l⟩ =>
    if ⊤ ∈ s
    then ⊤
    else some ⟨{ x | some x ∈ s }, by
      intro a b le mem
      exact l (WithTop.coe_le_coe.2 le) mem⟩

@[simp]
def ψ [PartialOrder P] : WithTop (𝒪(P)) → 𝒪(WithTop P) :=
  λ
  | some s =>
    ⟨{ some x | x ∈ s }, by
      intro c d le ⟨x, hx1, hx2⟩
      subst c
      use (WithTop.untop_le d le)
      have le' := le
      rw [←WithTop.coe_untop_le d le] at le'
      constructor
      · apply s.lower' (WithTop.coe_le_coe.1 le') hx1
      · exact WithTop.coe_untop_le d le⟩
  | ⊤ => LowerSet.Iic ⊤

lemma left_inv [PartialOrder P] :
    Function.LeftInverse ψ
    (φ : 𝒪(WithTop P) → WithTop (𝒪(P))) := by
  intro s; ext x
  simp
  split
  case a.h.h_1 t u heq
  · split_ifs at heq with h
    apply WithTop.coe_injective at heq
    subst u
    constructor <;> intro h1
    · obtain ⟨y, hy1, hy2⟩ := h1
      subst x; exact hy1
    · cases x with
      | some x1 => use x1; simpa
      | none => exfalso; exact h h1
  case a.h.h_2 t heq
  · split_ifs at heq with h
    simp; apply s.lower' (WithTop.le_none) h

lemma right_inv [PartialOrder P] :
    Function.RightInverse ψ
    (φ : 𝒪(WithTop P) → WithTop (𝒪(P))) := by
  intro s; simp
  split_ifs with h
  · split at h
    case pos.h_1 x t heq
    · simp at h
    case pos.h_2 t heq
    · rfl
  · split at h
    case neg.h_1 y t u
    · congr; simp
      ext w; simp
      constructor <;> intro h1
      · obtain ⟨w1, hw1, hw2⟩ := h1
        simp at hw2; subst w; exact hw1
      · use w
    case neg.h_2 t heq
    · simp at h

lemma aux [PartialOrder P] {a : 𝒪(WithTop P)}
    (h : ⊤ ∈ a) : ∀ x, x ∈ a := by
  intro x; cases x with
  | some x => apply a.lower' (WithTop.le_none) h
  | none => exact h

lemma map_rel_iff [PartialOrder P] {a b : 𝒪(WithTop P)} :
    φ a ≤ φ b ↔ a ≤ b := by
  simp only [φ, LowerSet.carrier_eq_coe, SetLike.mem_coe]
  split_ifs with h1 h2 h2
  · simp only [le_refl, true_iff]
    intro x _
    exact aux h2 x
  · simp only [top_le_iff, false_iff]
    intro le
    apply h2 (le h1)
  · simp only [le_top, true_iff]
    intro x _
    exact aux h2 x
  · rw [WithTop.some_le_some]
    constructor <;> intro le
    · intro y mem
      cases y with
      | some z => exact @le z mem
      | none => exfalso; exact h1 mem
    · intro y mem
      exact le mem

noncomputable def Ch_1_32ia' [PartialOrder P] : OrderIso (𝒪(WithTop P)) (WithTop (𝒪(P))) :=
  {
    toFun := φ
    invFun := ψ
    left_inv := left_inv
    right_inv := right_inv
    map_rel_iff' := map_rel_iff
  }

end Ch_1_32_ia

namespace Ch_1_32_ib

@[simp]
noncomputable def toFun [PartialOrder P] : 𝒪(WithBot P) → WithBot (𝒪(P)) :=
  λ | ⟨s, l⟩ =>
    if ⊥ ∈ s
    then some ⟨{ x | some x ∈ s }, λ _ _ le mem ↦ l (WithBot.coe_le_coe.2 le) mem⟩
    else ⊥

@[simp]
def invFun [PartialOrder P] : WithBot (LowerSet P) → LowerSet (WithBot P) :=
  λ
  | some s =>
    ⟨{ some x | x ∈ s } ∪ {⊥}, λ c d le mem ↦ by
      cases mem with
      | inl mem =>
        obtain ⟨x, hx1, hx2⟩ := mem
        subst c
        cases d with
        | none => right; rw [WithBot.none_eq_bot]; simp
        | some d =>
          left; simp at le ⊢; exact s.lower' le hx1
      | inr mem => right; subst c; rw [←eq_bot_iff] at le; subst d; simp ⟩
  | ⊥ => ⟨∅, by intro _ _ _ _; simp_all⟩

def left_inv [PartialOrder P] :
    Function.LeftInverse invFun
    (toFun : 𝒪(WithBot P) → WithBot (𝒪(P))) := by
  intro ⟨s', hs⟩; simp; split_ifs with h
  · split
    case pos.h_1 x t heq
    · simp_all
      obtain ⟨t', ht⟩ := t
      simp only [LowerSet.mk.injEq] at heq
      subst t'
      ext y; constructor
      · intro mem
        cases mem with
        | inl eq => subst eq; exact h
        | inr ex => obtain ⟨z, hz1, hz2⟩ := ex; subst y; exact hz1
      · intro mem
        cases y with
        | none => simp; rw [WithBot.none_eq_bot]
        | some y => simp; exact mem
    case pos.h_2 t heq
    · simp_all
  · split
    case neg.h_1 x t heq
    · cases heq
    case neg.h_2 t _
    · ext x; simp only [LowerSet.coe_mk, Set.mem_empty_iff_false, false_iff]
      intro xmem
      exact h (hs (OrderBot.bot_le x) xmem)

def right_inv [PartialOrder P] :
    Function.RightInverse invFun
    (toFun : 𝒪(WithBot P) → WithBot (𝒪(P))) := by
  intro s; simp; split_ifs with h
  · split at h
    case pos.h_1 _ t s
    · congr
      ext x; simp
      constructor <;> intro mem
      · obtain ⟨x1, hx1, hx2⟩ := mem; simp at hx2;
        subst x; exact hx1
      · use x
    case pos.h_2 t s
    · simp at h
  · split at h
    case neg.h_1 _ t s
    · exfalso; apply h; simp
    case neg.h_2 t s
    · rfl

def map_rel_iff' [PartialOrder P] :
    ∀ {x y : 𝒪(WithBot P)}, toFun x ≤ toFun y ↔ x ≤ y := by
  intro x y
  simp; split_ifs with h1 h2 h2
  · simp
    constructor <;> intro le
    · intro a amem
      cases a with
      | some a' => exact le amem
      | none => exact h2
    · intro a amem
      exact le amem
  · simp; intro le; apply h2; exact le h1
  · simp; intro a amem; exfalso; apply h1; apply x.lower' (OrderBot.bot_le a) amem
  · simp; intro a amem; exfalso; apply h1; apply x.lower' (OrderBot.bot_le a) amem

noncomputable def Ch_1_32_ib' [PartialOrder P] : 𝒪(WithBot P) ≃o WithBot (𝒪(P)) :=
  {
    toFun := toFun
    invFun := invFun
    left_inv := left_inv
    right_inv := right_inv
    map_rel_iff' := map_rel_iff'
  }

end Ch_1_32_ib

namespace Ch_1_32_ii

@[simp]
def toFun [PartialOrder P₁] [PartialOrder P₂] : 𝒪(P₁ ⊕ P₂) → 𝒪(P₁) × 𝒪(P₂) :=
  λ s ↦
  (⟨{ a | .inl a ∈ s }, by
      intro a b le amem; apply s.lower' (Sum.inl_mono le) (by simp_all)⟩,
  ⟨{ b | .inr b ∈ s }, by
      intro a b le amem; apply s.lower' (Sum.inr_mono le) (by simp_all)⟩)

@[simp]
def invFun [PartialOrder P₁] [PartialOrder P₂] : 𝒪(P₁) × 𝒪(P₂) → 𝒪(P₁ ⊕ P₂) :=
  λ ⟨s, t⟩ ↦
  ⟨ { .inl a | a ∈ s } ∪ { .inr b | b ∈ t }, by
      intro a b le amem
      cases amem with
      | inl ha =>
        left; obtain ⟨a', ha1, ha2⟩ := ha; subst a
        cases b with
        | inl b' => use b'; exact ⟨s.lower' (Sum.inl_le_inl_iff.mp le) ha1 , rfl⟩
        | inr b' => cases le
      | inr ha =>
        right; obtain ⟨a', ha1, ha2⟩ := ha; subst a
        cases b with
        | inl b' => cases le
        | inr b' => use b'; exact ⟨t.lower' (Sum.inr_le_inr_iff.mp le) ha1, rfl⟩ ⟩

theorem left_inv [PartialOrder P₁] [PartialOrder P₂] : Function.LeftInverse invFun
    (toFun : 𝒪(P₁ ⊕ P₂) → 𝒪(P₁) × 𝒪(P₂)) := by
  intro s; simp; ext x; constructor <;> intro mem
  · cases mem with
    | inl h => obtain ⟨a, ha1, ha2⟩ := h; subst x; exact ha1
    | inr h => obtain ⟨a, ha1, ha2⟩ := h; subst x; exact ha1
  · cases x with
    | inl x' => simp; exact mem
    | inr x' => simp; exact mem
  done

theorem right_inv  [PartialOrder P₁] [PartialOrder P₂] : Function.RightInverse invFun
    (toFun : 𝒪(P₁ ⊕ P₂) → 𝒪(P₁) × 𝒪(P₂)) := by
  intro s; simp; rfl

theorem map_rel_iff' [PartialOrder P₁] [PartialOrder P₂] :
    ∀ {s t}, toFun s ≤ (toFun :𝒪(P₁ ⊕ P₂) → 𝒪(P₁) × 𝒪(P₂)) t ↔ s ≤ t := by
  intro s t
  constructor <;> intro le
  · intro a amem
    obtain ⟨le1, le2⟩ := le
    cases a with
    | inl _ => exact le1 amem
    | inr _ => exact le2 amem
  · constructor
    · intro _ amem; exact le amem
    · intro _ amem; exact le amem

theorem Ch_1_32_ii' [PartialOrder P₁] [PartialOrder P₂] : 𝒪(P₁ ⊕ P₂) ≃o 𝒪(P₁) × 𝒪(P₂) :=
  {
    toFun := toFun
    invFun := invFun
    left_inv := left_inv
    right_inv := right_inv
    map_rel_iff' := map_rel_iff'
  }

end Ch_1_32_ii


/-!
  ## 1.33 Examples

  Theres not much to formalize here. I suppose I could try to prove the isomorphisms,
  but those are not particularly illuminating.
-/

/-!
  # Maps between ordered sets

  We have already dealt with order isomorphisms. We now add to the mix order-preserving
  or monotone maps, as well as order embeddings.
-/

/-!
  ## 1.34 Definitions

  If P and Q are partially ordered sets, a map φ : P → Q is "order preserving" or
  "monotone" if and only if `∀ (x y : P), x ≤ y → φ x ≤ φ y`. In Lean, this is
  written as `Monotone φ`. Lean also has `MonotoneOn φ s` to mean
  `∀ x ∈ s, ∀ y ∈ s, x ≤ y → φ x ≤ φ y`. Lean also has a "bundled" type
  called `OrderHom` that consists of a function together with the proof that
  it is monotone. The type of monotone maps from P to Q is also denoted `P →o Q`.

  The map φ is called an "order embedding" if it satisfies
  `∀ x y : P, x ≤ y ↔ φ x ≤ φ y`. Lean offers a bundled type called `orderEmbedding P Q`
  that consists of

  (i) a function f

  (ii) a proof that f is injective

  (iii) a proof that the order embedding property is satisfied

  We already saw above in 1.4 that map betwee partial orders that satisfies (iii)
  also satisfies (ii). We called this `injective_of_le_iff_le`. But order embeddings can be
  defined assuming only that `≤` is defined, so the structure asks for a proof of
  injectivity. The type of order embeddings from P to Q is denoted `P ↪o Q`

  TODO: Figure out if we need to specify injectivity for an order embedding between
  `PartialOrder`s.
-/

/-!
  ## 1.35 Examples

  The first set of examples are not illuminating to formalize.

  If P is a partial order, then by 1.30, the map `λ x ↦ ↓ᵖx` is an
  order embedding from `P` to `𝒪(P)`.
-/

namespace Ch_1_35

@[simp]
def toFun [PartialOrder P] : P → 𝒪(P) := λ x ↦ ↓ᵖx

def map_rel_iff' [PartialOrder P] : ∀ {a b : P}, toFun a ≤ toFun b ↔ a ≤ b := by
  intro a b
  constructor <;> intro le
  · simp at le; exact le
  · simp; exact le

def inj' [PartialOrder P] : Function.Injective (toFun : P → 𝒪(P)) :=
  injective_of_le_imp_le toFun map_rel_iff'.mp

def toLowerSet_orderEmbedding [PartialOrder P] : P ↪o 𝒪(P) :=
  {
    toFun := toFun
    map_rel_iff' := map_rel_iff'
    inj' := inj'
  }

end Ch_1_35

/-!
  ## 1.36 Remarks

  The following are supposedly all easy to prove

  (1) Let `φ : P → Q` and `ψ : Q → R` be monotone maps. Then the composite
  map `ψ ∘ φ` is monotone. This is called `Monotone.comp`
-/

lemma example_1_36_1 [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    {φ : P → Q} {ψ : Q → R} (h1 : Monotone φ) (h2 : Monotone ψ) : Monotone (ψ ∘ φ) :=
  Monotone.comp h2 h1

/-!
  (2) Let φ : P ↪o Q and let φ(P) = { φ(x) | x : P } be the image of φ.
  Then P is order isomorphic to φ(P).

  The inverse function is going to have to take advantage of classical choice
  by choosing the preimage known to exist. This is a case where it is more
  direct to show `P ≃o' φ(P)` instead of using Lean's `OrderIso`.
-/

lemma example_1_36_2 [PartialOrder P] [PartialOrder Q] (φ : P ↪o Q) :
    (Set.univ : Set P) ≃o' { φ p | p : P } :=
  {
    toFun := λ p ↦ ⟨φ.toFun p, by simp⟩
    surj' := by
      intro ⟨q', ⟨p, hp⟩⟩
      use ⟨p, by simp⟩
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Function.Embedding.toFun_eq_coe,
        RelEmbedding.coe_toEmbedding, Subtype.mk.injEq]
      exact hp
    map_rel_iff' := by
      intro a b
      constructor <;> intro le
      · simp at le; exact le
      · simp; exact le
  }

/-!
  (3) An order embedding (as defined in the text) is automatically a one-to-one map.
  This is what we have already seen numerous times.
-/

lemma example_1_36_3 [PartialOrder P] [PartialOrder Q] (φ : P ↪o Q) :
    Function.Injective φ.toFun :=
  injective_of_le_imp_le φ.toFun φ.map_rel_iff'.mp

/-!
  (4) Partial orders P and Q are order isomorphic, if and only if there ixist monotone
  maps `φ : P → Q` and `ψ : Q → P` such that `φ ∘ ψ = (id : Q → Q)` and
  `ψ ∘ φ = (id : P → P)`.
-/

lemma example_1_36_4a [PartialOrder P] [PartialOrder Q] (χ : P ≃o Q) :
    ∃ (φ : P → Q) (ψ : Q → P), Monotone φ ∧ Monotone ψ ∧
    Function.LeftInverse φ ψ ∧ Function.RightInverse φ ψ := by
  use χ.toFun, χ.invFun
  split_ands
  · intro a b le; apply χ.map_rel_iff'.mpr le
  · intro a b le
    rw [←χ.right_inv a, ←χ.right_inv b] at le
    exact χ.map_rel_iff'.mp le
  · intro a; apply χ.right_inv
  · intro a; apply χ.left_inv

lemma example_1_36_4b [PartialOrder P] [PartialOrder Q] (φ : P → Q) (ψ : Q → P)
    (h1 : Monotone φ) (h2 : Monotone ψ) (h3 : Function.LeftInverse ψ φ)
    (h4 : Function.RightInverse ψ φ) : P ≃o Q :=
  {
    toFun := φ
    invFun := ψ
    left_inv := h3
    right_inv := h4
    map_rel_iff' := by
      intro a b
      constructor <;> intro le
      · rw [←h3 a, ←h3 b]
        exact h2 le
      · exact h1 le
  }

  /-!
    ## 1.37 Ordered sets of maps

    Functions `f : P → Q` are naturally ordered by the pointwise order defined by
    `f ≤ g` if and only if `∀ x : P, f x ≤ g x`. It seems this default instance
    has been defined in Lean already.

    Any (sub)set of functions inherits this order. So, for example, the set of
    monotone functions is ordered by the pointwise order. That is, there is
    a `PartialOrder` instance for `P →o Q`.

    The book notes that `P →o Fin 2 ≃o 𝒪(P)ᵒᵈ`.
  -/

instance [PartialOrder S] [Membership P S] : Membership P Sᵒᵈ :=
  { mem := λ p T ↦ p ∈ OrderDual.ofDual T }

@[simp]
theorem mem_toDual_iff [PartialOrder S] [Membership P S] {p : P} {T : S} :
    p ∈ OrderDual.toDual T ↔ p ∈ T := by rfl

@[simp]
theorem mem_ofDual_iff [PartialOrder S] [Membership P S] {p : P} {T : Sᵒᵈ} :
    p ∈ T ↔ p ∈ OrderDual.ofDual T := by rfl

theorem zero_or_one_of_Fin_2 (x : Fin 2): (x = 0) ∨ (x = 1) := by
  obtain ⟨v, hv⟩ := x
  cases v with
  | zero => left; rfl
  | succ k => cases k with
    | zero => right; rfl
    | succ d => exfalso; linarith

lemma example_1_37 [PartialOrder P] : (P →o Fin 2) ≃o 𝒪(P)ᵒᵈ :=
  {
    toFun := λ f ↦ ⟨{ p | f p = 0 }, by
      intro y x le mem
      apply f.monotone' at le; simp at le
      rw [mem] at le; simp at le; exact le ⟩ᵈ
    invFun := λ S ↦ ⟨λ p ↦ if p ∈ S then 0 else 1, by
      intro x y le; simp; split_ifs with memx memy memy <;> simp
      apply memx; apply (OrderDual.ofDual S).lower' le memy ⟩
    left_inv := by
      intro f; ext x
      simp; split_ifs with h
      · symm; rw [h]
      · cases zero_or_one_of_Fin_2 (f x) with
        | inl zero => exfalso; exact h zero
        | inr one => rw [one]
    right_inv := by
      intro s; simp;
      rw [←OrderDual.toDual_ofDual s, OrderDual.toDual_inj]
      rfl
    map_rel_iff' := by
      intro a b
      constructor <;> intro le
      · simp at le
        intro x
        cases zero_or_one_of_Fin_2 (b.toFun x) with
        | inl zero =>
          rw [zero]
          specialize le zero
          simp at le; rw [←le]; rfl
        | inr one => rw [one]; exact OrderTop.le_top (a x)
      · intro x xmem
        specialize le x
        simp at le
        rw [xmem] at le
        simp at le; exact le
  }
