import OrderTheory.Mathlib.lib

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

/-!
  ## 1.3 Chains and Antichains

  A chain is another name for a total or linear order. We can naturally express finite
  total orders of n elements with the type `Fin n`. These types naturally inherit a
  total order, so `≤` may be used on them as expected. Lean also has a predicate
  `IsChain : Set α → Prop` that works on sets instead of types.

  An antichain is an order in which `x ≤ y` if and only if `x = y`. To define a type
  as an antichain, one only has to define `≤` using `=`. There is also a predicate
  `IsAntichain : Set α → Prop` that works on sets.

  The fact that a subset of a chain is also a chain is written using `IsChain.mono`. The
  corresponding fact about antichains is written as `IsAntichain.subset`.

  TODO: Consider defining `Fin' n` as a type synonym for `Fin n` with an instance
  of `PartialOrder` that turns it into an antichain.
-/

/-!
  ## 1.4 Order Isomorphisms

  The definition used in the text book is importantly different from the one used
  in Lean. The textbook definition of an isomorphism between Partial Orders P and Q
  is a function `φ : P → Q` such that
    - (i) `φ` is surjective and
    - (ii) `x ≤ y` if and only if `φ x ≤ φ y`
  We include a formalization of this definition in case it makes sense to use it
  when proving two orders are isomorphic.
-/

class OrderIso' (P Q : Type*) [PartialOrder P] [PartialOrder Q] where
  toFun : P → Q
  surjective : Function.Surjective toFun
  map_rel_iff' : ∀ {a b}, toFun a ≤ toFun b ↔ a ≤ b

/-!
  Lean's definition of OrderIso requires an explicit inverse `invFun : Q → P` to be
  provided along with proofs that `invFun` forms both a left and right inverse of `toFun`.
  This style is inherently more constructive than the textbook version which is why
  it is preferred in Lean. The Lean definition is also more general in the sense that
  it does not assume P and Q are Partial Orders, only that they have `≤` defined.

  If we have an OrderIso', we can create an OrderIso, but that translation is not computable,
  because the inverse of an arbitrary OrderIso' is obtained by instantiating an existential.
  Nonetheless, we can do it. The next two lemmas are useful for this purpose but are
  not in Mathlib.
-/

/-- In a partial order, the converse of anti-symmetry also holds. -/
lemma le_le_iff_eq [inst : PartialOrder P] {a b : P} : a ≤ b ∧ b ≤ a ↔ a = b := by
  constructor
  · rintro ⟨h1, h2⟩
    exact inst.le_antisymm a b h1 h2
  · intro eq
    use le_of_eq eq
    exact le_of_eq eq.symm

/--
  If a function preserves and reflects the order relation on two partial orders,
  then the function must be injective.
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
noncomputable def OrderIsoOfBookOrderIso [PartialOrder P] [PartialOrder Q]
    (φ : OrderIso' P Q) : OrderIso P Q := by
  have h : Function.Bijective φ.toFun :=
        ⟨injective_of_le_iff_le φ.map_rel_iff', φ.surjective⟩
  rw [Function.bijective_iff_has_inverse] at h
  exact {
    toFun := φ.toFun
    invFun := h.choose
    left_inv := h.choose_spec.left
    right_inv := h.choose_spec.right
    map_rel_iff' := φ.map_rel_iff'
  }

/-!
  For the most part we will work with Lean's OrderIso, but we may prefer OrderIso'
  in cases where we want to mimic a proof found in the textbook.

  The inverse of an OrderIso φ is denoted `φ.symm`. This is a full OrderIso
  structure that comes equipped with all the necessary proofs that it is also
  an order isomorphism.
-/

/-!
  ## 1.5 Number systems

  The number systems ℝ, ℚ, and ℕ all form total orders. Lean has already defined
  default instances of these `LinearOrder`s. One detail to watch out for is that
  the textbook defines ℕ as excluding 0 and writes ℕ₀ to denote the natural numbers
  with 0. In Lean, ℕ includes 0, so we will do the same.

  We can define a partial order on ℕ as `m ≤ n` if and only if `m ∣ n`. Since this
  is not the default order on ℕ in Lean, we show how to define it here.
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
  class in order theory is the down-sets of P. The textbook denotes this as `O(P)`
  using a script O. We will see in 1.27 below how they are represented in Lean.

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
  the type of (closed) intervals of X (assuming ≤ is defined on X). It then also
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
  binary strings in Lean as `List (Fin 2)`. Here, `List` is the type of (finite)
  lists of some type. We take lists over `Fin 2` which is the finite type of naturals
  less than 2, (i.e., 0 and 1). We can generalize over arbitrary types, α, not just
  Fin 2, of course. Finite lists form a partial order according to
  `x ≤ y` if and only if `x` is a prefix of `y`. The prefix relation is denoted
  `x <+: y`. This does not appear to be a default instance in Lean, so we define
  it here. It seems that Lean already knows the prefix relation is transitive, so
  we start by showing it is reflexive and antisymmetric.
-/

theorem List.IsPrefix.refl (a : List α) : a <+: a := by use []; simp

theorem List.IsPrefix.antisymm : a <+: b → b <+: a → a = b := by
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
  used to represent the output of computations.

  TODO: Figure out how to work with streams and define a PartialOrder instance
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

instance Function.Option.instPartialOrder {X : Type u} {Y : Type v} :
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
  (We don't use `Set.Iii` because that's just `Set.univ`, the entire set of values.)
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
  several forward references to Domains and Domain Theory and the theory of Fixedpoints.
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
  Dealing with finite sets is surprisingly hard in Lean! While this observation
  may seem obvious, it is somewhat difficult to formally prove. Since it's
  used later, it's worth stating it here and leaving it unsolved.

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

/-
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

lemma image_lt_lt_iff_image_covby_covby [Fintype P] [Fintype Q] [PartialOrder P]
    [PartialOrder Q] [DecidableEq Q] (f : P → Q) (hf : f.Bijective) :
    (∀ x y, f x < f y ↔ x < y) ↔ (∀ x y, f x ⋖ f y ↔ x ⋖ y) := by
  constructor
  · intro h x y
    constructor
    · simp [CovBy]
      intro lt nlt
      constructor
      · exact (h x y).1 lt
      · by_contra h1; push_neg at h1
        obtain ⟨w, hw⟩ := h1
        specialize @nlt (f w)
        specialize nlt ((h x w).2 hw.left)
        apply nlt
        exact (h w y).2 hw.right
    · simp [CovBy]
      intro lt nlt
      constructor
      · exact (h x y).2 lt
      · by_contra h1; push_neg at h1
        obtain ⟨w, hw⟩ := h1
        obtain ⟨u, hu⟩ := hf.2 w
        rw [←hu] at hw
        specialize @nlt u
        specialize nlt ((h x u).1 hw.left)
        apply nlt
        exact (h u y).1 hw.right
  · intro h x y
    rw [covChain_of_fintype, covChain_of_fintype]
    constructor
    · intro lt
      obtain ⟨n, hn⟩ := lt
      use n
      revert x y
      induction n with
      | zero =>
        intro x y hn
        simp [CovChain] at hn ⊢
        exact hf.1 hn
      | succ k ih =>
        intro x y hn
        simp [CovChain] at hn ⊢
        obtain ⟨w, hw, covc⟩ := hn
        use (Fintype.bijInv hf w)
        have winv : w = f (Fintype.bijInv hf w) := by
          symm
          apply Fintype.rightInverse_bijInv hf
        constructor
        · rw [winv] at hw
          exact (h x _).1 hw
        · apply ih (Fintype.bijInv hf w) y
          rwa [← winv]
    · intro lt
      obtain ⟨n, hn⟩ := lt
      use n
      revert x y
      induction n with
      | zero =>
        intro x y hn
        simp [CovChain] at hn ⊢
        rw [hn]
      | succ k ih =>
        intro x y hn
        simp [CovChain] at hn ⊢
        obtain ⟨w, hw, covc⟩ := hn
        use (f w)
        constructor
        · exact (h x w).2 hw
        · apply ih w y covc

lemma orderIso_iff_image_covby_covby [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]
    [DecidableEq Q] (f : P → Q) (hf : f.Bijective) :
    (∃ φ : P ≃o Q, φ = f) ↔ (∀ x y, f x ⋖ f y ↔ x ⋖ y) := by
  rw [orderIso_iff_image_lt_lt, image_lt_lt_iff_image_covby_covby] <;> exact hf

/-!
  ## 1.18 Proposition

  Two ordered sets P and Q are order isomorphic if and only if they can be
  represented by the same diagram.

  Statement and proof omitted.
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

example [PartialOrder P] (x y : P) : OrderDual.toDual x ≤ OrderDual.toDual y ↔ y ≤ x := by simp

/-!
  The need to write `OrderDual.toDual` is rather annoying. It would be nice to be able
  to annotate a term with a hat or something and define the notation to take an element
  to it's order dual.

  The importance of duals lies in the duality principle. For any statement Φ, we can
  define a dual statement Φᵒᵈ that replaces every occurrence of ≤ with ≥. Then for
  any statement Φ, if it's true in all ordered sets, then so is it's dual statement
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

example {X : Type u} : (⊥ : Set X) = ∅ := Set.bot_eq_empty

example {X : Type u} : (⊤ : Set X) = Set.univ := Set.top_eq_univ

/-!
  ℕ has a bottom element, namely 0, but it has no top element. ℤ has no
  bottom or top element.
-/

example : ⊥ = 0 := bot_eq_zero

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

  The text talks of maximal elements of `Q : Set P`, and used the notation MaxQ
  to denote the set of maximal elements of Q. In Lean this is denote by
  `maximals (· ≤ ·) Q`. The use of `(· ≤ ·)` is required because `maximals` is
  well-defined for arbitrary binary relations.

  Of course the dual concepts are written `IsMin x` and `minimals`.

  For any nonempty finite subset Q of an order Q both `maximal _ Q` and
  `minimal _ Q` are nonempty. Similarly, for any `x ∈ Q`, there is some
  `y ∈ maximals _ Q` such that `x ≤ y`. As with many facts about finite sets,
  these are surprisingly hard to prove.

  TODO: Prove these facts about finite sets.

  Any total function `f : X → Y` is maximal among partial functions
  `X → Option Y`.
-/

theorem Function.Option.isMax_isSome {f : X → Option Y} (hf : ∀ x, (f x).isSome) :
    IsMax f := by
  intro g le
  simp [LE.le] at le ⊢
  intro x _
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
  is ≤ everything in Q.

  To access this instance of the order on the sum of P and Q we can write
  `P ⊕ₗ Q` with a subscript l on the `⊕`. There is a translation between
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

/-- Definition of forward function defining the OrderIso for 1.26 -/
def φ' {n : ℕ} (A : Set (Fin n)) : Fin n → Prop := λ i ↦ i ∈ A

/--
  Proof that φ' is an OrderIso. The proof of map_rel_iff' is
  essentially what is in the textbook, but OrderIso requires us to
  explicitly define the inverse, while OrderIso' only requires us
  to demonstrate that the function is surjective.
-/
def φ : OrderIso (Set (Fin n)) (Fin n → Prop) := {
  toFun := φ'
  invFun := λ s ι ↦ s ι
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_rel_iff' := by
    simp; intro A B
    rw [Set.subset_def]
    unfold φ'
    simp [LE.le]
}

/--
  An alternative approach that shows φ is a OrderIso'
-/
def φ_text : OrderIso' (Set (Fin n)) (Fin n → Prop) := {
  toFun := φ'
  map_rel_iff' := φ.map_rel_iff'
  surjective := by
    intro s
    use { ι | s ι }
    unfold φ'; simp
}

end Ch_1_26

/-!
  # Down-sets and up-sets
-/

/-!
  ## 1.27 Definitions and remarks

  A down-set `Q : Set P` of a partial order P is defined by the property that
  if `x ∈ Q` and `(y : P) ≤ x`, then `y ∈ Q`. An up-set of P is defined dually.
  This is sometime called a "decreasing set" or an "order ideal". Lean represents
  this with a type called `LowerSet P` which has a carrier set of type `Set P`
  and a proof that the down-set property holds. The dula notion of an up-set
  is called `UpperSet P` in lean. It is also sometimes called an "increasing set"
  or an "order filter".

  Given `Q : Set P` we can define `{ x | ∃ y ∈ Q, x ≤ Q }` to be the downward
  closure of Q. The text denotes this as `↓Q`. In Lean this is called
  `lowerClosure Q` (dually `upperClosure Q`). The down-set `lowerClosure Q` has
  type `LowerSet P`.

  A "principal down-set" or "principal ideal" is the downward closure of a singleton
  set `{x}`. The text uses `↓x` to represent the principle down-set of x. The set
  `Set.Iic x` happens to be a `LowerSet`. Lean has `LowerSet.Iic x`
  that bundles `Set.Iic x` together with a proof that is a `LowerSet`. There is
  thus an equivalence between `lowerClosure {x}` and `LowerSet.Iic x`.
  -/

example [PartialOrder P] (x : P) : lowerClosure {x} = LowerSet.Iic x := sorry

/-
  The textbook uses ↓x and ↑x to represent the principal order-ideal
  and the principal order-filter of x. In Lean, we express those with
  LowerSet.Iic x and LowerSet.Ici x respectively.

  Similarly the textbook uses O(P) to represent the downsets of P ordered
  by inclusion. In Lean we can simply write (LowerSet P), and since that
  type is SetLike, it has a PartialOrder instance as expected.
-/

lemma Ch_1_30 [PartialOrder P] (x y : P) : List.TFAE [
    x ≤ y,
    Set.Iic x ⊆ Set.Iic y,
    ∀ (Q : Set P), IsLowerSet Q → y ∈ Q → x ∈ Q ] := by
  tfae_have 1 ↔ 2
  · constructor
    · intro le a mem
      simp at mem ⊢
      exact mem.trans le
    · intro sub
      specialize @sub x (by simp)
      change x ∈ LowerSet.Iic y at sub
      exact LowerSet.mem_Iic_iff.1 sub
  tfae_have 2 → 3
  · intro sub Q ls mem
    have : x ≤ x := by rfl
    rw [←LowerSet.mem_Iic_iff] at this
    specialize sub this
    change x ∈ LowerSet.Iic y at sub
    unfold IsLowerSet at ls
    exact ls sub mem
  tfae_have 3 → 2
  · intro h a mem
    simp at mem
    specialize h (Set.Iic y) (isLowerSet_Iic y) (by simp)
    simp at h ⊢
    exact mem.trans h
  tfae_finish

lemma Ch_1_30_1_iff_2 [PartialOrder P] (x y : P) : x ≤ y ↔ LowerSet.Iic x ⊆ LowerSet.Iic y := by
  constructor
  · intro le a mem
    simp at mem ⊢
    exact mem.trans le
  · intro sub
    specialize @sub x (by simp)
    change x ∈ LowerSet.Iic y at sub
    exact LowerSet.mem_Iic_iff.1 sub

lemma Ch_1_30_2_iff_3 [PartialOrder P] (x y : P) :
    LowerSet.Iic x ⊆ LowerSet.Iic y ↔ ∀ (Q : LowerSet P), y ∈ Q → x ∈ Q := by
  constructor
  · intro sub Q mem
    specialize @sub x (by simp)
    change x ∈ LowerSet.Iic y at sub
    simp at sub
    apply Q.lower' sub mem
  · intro h a mem
    simp at mem ⊢
    specialize h (LowerSet.Iic y) (by simp)
    simp at h ⊢
    exact mem.trans h

lemma Ch_1_30_1_iff_3 [PartialOrder P] (x y : P) : x ≤ y ↔ ∀ (Q : LowerSet P), y ∈ Q → x ∈ Q := by
  rw [Ch_1_30_1_iff_2, Ch_1_30_2_iff_3]

lemma Ch_1_30' [PartialOrder P] (x y : P) : List.TFAE [
    x ≤ y,
    LowerSet.Iic x ⊆ LowerSet.Iic y,
    ∀ (Q : LowerSet P), y ∈ Q → x ∈ Q ] := by
  tfae_have 1 ↔ 2
  · exact Ch_1_30_1_iff_2 x y
  tfae_have 2 ↔ 3
  · exact Ch_1_30_2_iff_3 x y
  tfae_finish

attribute [local simp] WithTop.map WithTop.le_none

example [PartialOrder P] [PartialOrder Q] (f : P ≃o Q) : WithTop P ≃o WithTop Q :=
  {
  toFun := WithTop.map f.toFun --Option.map f.toFun
  invFun := WithTop.map f.invFun
  left_inv := (Equiv.optionCongr f.toEquiv).left_inv
  right_inv := (Equiv.optionCongr f.toEquiv).right_inv
  map_rel_iff' := @fun a b => by
    cases' a with a _ <;> cases' b with b _
    · simp
    · simp; constructor <;> intro le <;>
      simp [WithTop.none_eq_top, WithTop.some_eq_coe] at le
    · simp
    · simp
  }


@[simp]
noncomputable def CH_1_32ia_toFun [PartialOrder P] : LowerSet (WithTop P) → WithTop (LowerSet P) :=
  λ | ⟨s, l⟩ =>
    if ⊤ ∈ s
    then ⊤
    else some ⟨{ x | some x ∈ s }, by
      intro a b le mem
      unfold IsLowerSet at l
      exact l (WithTop.coe_le_coe.2 le) mem⟩

@[simp]
def CH_1_32ia_invFun [PartialOrder P] : WithTop (LowerSet P) → LowerSet (WithTop P) :=
  λ
  | some s =>
    ⟨{ some x | x ∈ s }, by
      intro c d le mem
      obtain ⟨x, hx1, hx2⟩ := mem
      rw [←hx2] at le
      use (WithTop.untop_le d le)
      have le' := le
      rw [←WithTop.coe_untop_le d le] at le'
      constructor
      · apply s.lower' (WithTop.coe_le_coe.1 le') hx1
      · exact WithTop.coe_untop_le d le ⟩
  | ⊤ => LowerSet.Iic ⊤

lemma CH_1_32_left_inv [PartialOrder P] :
    Function.LeftInverse CH_1_32ia_invFun
    (CH_1_32ia_toFun : LowerSet (WithTop P) → WithTop (LowerSet P)) := by
  intro s; ext x
  simp
  split
  case a.h.h_1 t u heq
  · split_ifs at heq with h
    apply WithTop.coe_injective at heq
    subst u; simp
    constructor <;> intro h1
    · obtain ⟨y, hy1, hy2⟩ := h1
      subst x; exact hy1
    · cases x with
      | some x1 => use x1
      | none => exfalso; exact h h1
  case a.h.h_2 t heq
  · split_ifs at heq with h
    constructor <;> intro _
    · apply s.lower' (WithTop.le_none) h
    · simp

lemma CH_1_32_right_inv [PartialOrder P] :
    Function.RightInverse CH_1_32ia_invFun
    (CH_1_32ia_toFun : LowerSet (WithTop P) → WithTop (LowerSet P)) := by
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

lemma CH_1_32_aux [PartialOrder P] {a : LowerSet (WithTop P)}
    (h : ⊤ ∈ a) : ∀ x, x ∈ a := by
  intro x; cases x with
  | some x => apply a.lower' (WithTop.le_none) h
  | none => exact h

lemma CH_1_32_map_rel_iff [PartialOrder P] {a b : LowerSet (WithTop P)} :
    CH_1_32ia_toFun a ≤ CH_1_32ia_toFun b ↔ a ≤ b := by
  simp
  split_ifs with h1 h2 h2
  · simp
    intro x _
    exact CH_1_32_aux h2 x
  · simp
    intro le
    apply h2
    change a ⊆ b at le
    exact le ⊤ h1
  · simp
    intro x _
    exact CH_1_32_aux h2 x
  · simp
    constructor <;> intro le
    · intro y mem; simp at mem ⊢
      cases y with
      | some z =>
        exact @le z mem
      | none => exfalso; exact h1 mem
    · intro y mem
      simp at mem ⊢
      change a ⊆ b at le
      exact le _ mem

noncomputable def Ch_1_32ia' [PartialOrder P] : OrderIso (LowerSet (WithTop P)) (WithTop (LowerSet P)) :=
  {
    toFun := CH_1_32ia_toFun
    invFun := CH_1_32ia_invFun
    left_inv := CH_1_32_left_inv
    right_inv := CH_1_32_right_inv
    map_rel_iff' := CH_1_32_map_rel_iff
  }

/- def Ch_1_32ib [PartialOrder P] : OrderIso (LowerSet (WithBot P)) (WithBot (LowerSet P)) :=
  WithBot.toDual ∘ Ch_1_32ia -/
