import OrderTheory.Mathlib.lib

open scoped Classical
/-
  In this file, we focus on the core definitions found in Chapter 1
  of Introduction to Lattices and Order.

  The first chapter is largely informal and introduces very basic
  definitions. There are a few lemmas which we formalize in this file.


-/

/--
  The textbook's definition of Order-isomorphism is different from
  the one in Lean. For one, the Lean definition of OrderIso is valid
  for anything satisfying the LE class. The textbook definition only works
  in the more restrictive case in which the order is at least a Partial Order.
  The definition from the textbook is given here. We include it so that
  we might follow the proofs from the book more closely in certain cases.
-/
class BookOrderIso (P Q : Type*) [PartialOrder P] [PartialOrder Q] where
  toFun : P → Q
  surjective : Function.Surjective toFun
  map_rel_iff' : ∀ {a b}, toFun a ≤ toFun b ↔ a ≤ b

/-
  If we have a BookOrderIso, we can create an OrderIso, but that
  translation is not computable, because the inverse of an arbitrary
  BookOrderIso is obtained by instantiating an existential. Nonetheless,
  we can do it. The next two lemmas are useful
-/

-- This didn't seem to be in Mathlib. It is used on page 3.
lemma le_le_iff_eq [PartialOrder P] {a b : P} : a ≤ b ∧ b ≤ a ↔ a = b := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [le_iff_eq_or_lt] at h1 h2
    cases' h1 with h1 h1 <;> cases' h2 with h2 h2 <;> try tauto
    exfalso
    exact not_lt_of_lt h1 h2
  · intro eq
    use le_of_eq eq
    exact le_of_eq eq.symm

-- This is also on page 3.
lemma injective_of_le_iff_le [PartialOrder P] [PartialOrder Q]
    {f : P → Q} (h2 : ∀ {a b}, f a ≤ f b ↔ a ≤ b) : Function.Injective f := by
  intro a b eq
  rw [←le_le_iff_eq] at eq
  rw [@h2 a b, @h2 b a] at eq
  exact le_le_iff_eq.1 eq

/--
  A noncomputable function that defines an OrderIso from a BookOrderIso.
-/
noncomputable def OrderIsoOfBookOrderIso [PartialOrder P] [PartialOrder Q]
    (φ : BookOrderIso P Q) : OrderIso P Q := by
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

-- True if there are xᵢ such that x = x₀ ⋖ x₁ ⋖ x₂ ⋖ ... xₙ = y
def CovChain [PartialOrder P] (x y : P) : ℕ → Prop
  | 0  => x = y
  | .succ n =>  ∃ w, x ⋖ w ∧ CovChain w y n

-- A passing comment on page 11 says "Observe that if P is finite,
-- x < y if and only if there exists a finite sequence of covering
-- relations x = x₀ ⋖ x₁ ⋖ ... ⋖ nₙ = y." This is surprisingly hard
-- to prove due to the fiddly nature of finite sets.
lemma covChain_of_fintype [PartialOrder P] [Fintype P] {x y : P} :
    x < y ↔ ∃ n, CovChain x y n := sorry

-- Using the unproven lemma above, we can prove Lemma 1.17
lemma Ch_1_17 [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]
    [DecidableEq Q] (f : P → Q) (hf : f.Bijective): List.TFAE [
      ∃ φ : P ≃o Q, φ = f,
      ∀ x y, f x < f y ↔ x < y,
      ∀ x y, f x ⋖ f y ↔ x ⋖ y ] := by
  tfae_have 1 → 2
  · rintro ⟨φ, eq⟩ x y; rw [←eq]; simp
  tfae_have 2 → 1
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
  tfae_have 2 → 3
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
  tfae_have 3 → 2
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
  tfae_finish

-- Definition of function used in Proposition 1.26
def phi_1_26 {n : ℕ} (A : Set (Fin n)) : Fin n → Prop := λ i ↦ i ∈ A

/--
  Proof that phi_1_26 is an OrderIso. The proof of map_rel_iff' is
  essentially what is in the textbook, but OrderIso requires us to
  explicitly define the inverse, while BookOrderIso only requires us
  to demonstrate that the function is surjective.
-/
def Ch_1_26 : OrderIso (Set (Fin n)) (Fin n → Prop) := {
  toFun := phi_1_26
  invFun := λ s ι ↦ s ι
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_rel_iff' := by
    simp; intro A B
    rw [Set.subset_def]
    unfold phi_1_26
    simp [LE.le]
}

/--
  An alternative approach that shows phi_1_26 is a BookOrderIso
-/
def Ch_1_26' : BookOrderIso (Set (Fin n)) (Fin n → Prop) := {
  toFun := phi_1_26
  map_rel_iff' := Ch_1_26.map_rel_iff'
  surjective := by
    intro s
    use { ι | s ι }
    unfold phi_1_26; simp
}

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
