import Mathlib.Order.WithBot
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Cover
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Minimal
import Mathlib.Data.Sum.Order
import Mathlib.Order.Chain
import Mathlib.Tactic

--import Std.Data.List.Lemmas

variable {α : Type} {P Q : Type}

def WithTop.untop_le [PartialOrder α] {y : α} (x : WithTop α) : x ≤ some y → α :=
  match x with
  | some a => λ _ ↦ a
  | none => λ le ↦ by exfalso; apply WithTop.not_top_le_coe y le

@[simp]
theorem WithTop.coe_untop_le [PartialOrder α] {y : α} (x : WithTop α) (h : x ≤ some y) :
    ↑(WithTop.untop_le x h) = x := by
  cases x with
  | coe a => simp [untop_le]
  | top => exfalso; apply WithTop.not_top_le_coe y h

-- Not in Mathlib!?!
instance instLowerSetHasSubset [Preorder P] : HasSubset (LowerSet P) :=
{
  Subset := λ H K ↦ ∀ x, x ∈ H → x ∈ K
}

instance instLowerSetHasSSubset [Preorder P] : HasSSubset (LowerSet P) :=
{
  SSubset := λ H K ↦ H < K
}

instance instUpperSetHasSSubset [Preorder P] : HasSSubset (UpperSet P) :=
{
  SSubset := λ H K ↦ H < K
}

instance instUpperSetHasSubset [Preorder P] : HasSubset (UpperSet P) :=
{
  Subset := λ H K ↦ ∀ x, x ∈ H → x ∈ K
}

instance LowerSet.instEmptyCollection [LE P] : EmptyCollection (LowerSet P) :=
{
  emptyCollection := ⟨∅, isLowerSet_empty⟩
}

@[simp]
theorem LowerSet.subset_lift [Preorder P] {S T : LowerSet P} :
    S ⊆ T ↔ S.carrier ⊆ T.carrier := by rfl

@[simp]
theorem LowerSet.ssubset_lift [Preorder P] {S T : LowerSet P} :
    S ⊂ T ↔ S.carrier ⊂ T.carrier := by rfl

@[simp]
theorem LowerSet.lt_lift [Preorder P] {S T : LowerSet P} :
    S < T ↔ S.carrier < T.carrier := by rfl

@[simp]
theorem UpperSet.subset_lift [Preorder P] {S T : UpperSet P} :
    S ⊆ T ↔ S.carrier ⊆ T.carrier := by rfl

instance instLowerSetUnion [Preorder α] : Union (LowerSet α) :=
  { union := λ s t ↦ ⟨s.carrier ∪ t.carrier, by
      intro x y le mem
      cases mem with
      | inl mem => left; exact s.lower le mem
      | inr mem => right; exact t.lower le mem ⟩
  }

instance instUpperSetUnion [Preorder α] : Union (UpperSet α) :=
  { union := λ s t ↦ ⟨s.carrier ∪ t.carrier, by
      intro x y le mem
      cases mem with
      | inl mem => left; exact s.upper le mem
      | inr mem => right; exact t.upper le mem ⟩
  }



theorem LowerSet.emptyCollection_iff [LE P] : (∅ : LowerSet P) = ⟨∅, isLowerSet_empty⟩ := rfl

theorem LowerSet.eq_empty_carrier [Preorder P] (ls : LowerSet P) :
    ls = ∅ ↔ ls.carrier = ∅ := by
  rw [emptyCollection_iff]
  constructor <;> intro h
  · rw [h]
  · obtain ⟨carrier, lower⟩ := ls
    simp_all

theorem LowerSet.Iic_mem_self [Preorder P] (x : P ) : x ∈ Iic x :=
  LowerSet.mem_Iic_iff.2 (by rfl)

@[ext]
theorem OrderDual.ext [LE P] (s t : (LowerSet P)ᵒᵈ) (h : OrderDual.toDual s = OrderDual.toDual t) :
    s = t := by exact h

attribute [local simp] WithTop.map WithTop.le_none

def WithTop.orderIso [PartialOrder P] [PartialOrder Q] (f : P ≃o Q) :
    WithTop P ≃o WithTop Q :=
  {
  toFun := WithTop.map f.toFun
  invFun := WithTop.map f.invFun
  left_inv := (Equiv.optionCongr f.toEquiv).left_inv
  right_inv := (Equiv.optionCongr f.toEquiv).right_inv
  map_rel_iff' := @fun a b => by
    cases' a with a _ <;> cases' b with b _ <;>
    · simp [Option.map, WithTop.none_eq_top, WithTop.some_eq_coe]
  }

instance OrderDual.instHasCompl [HasCompl P] [LE P] : HasCompl (Pᵒᵈ) :=
  {
    compl := OrderDual.toDual ∘ compl ∘ OrderDual.toDual
  }

@[simp]
theorem OrderDual.hasCompl_def [HasCompl P] [LE P] {s : Pᵒᵈ} :
    sᶜ = (OrderDual.toDual ∘ compl ∘ OrderDual.toDual) s := by rfl

instance OrderDual.hasSubset [HasSubset P] [LE P] : HasSubset (Pᵒᵈ) :=
  {
    Subset := λ s t ↦ OrderDual.ofDual s ⊆ OrderDual.ofDual t
  }

@[simp]
theorem OrderDual.hasSubset_def [HasSubset P] [LE P] {s t : Pᵒᵈ} (h : s ⊆ t) :
    OrderDual.ofDual s ⊆ OrderDual.ofDual t := by simp [HasSubset.Subset] at h; exact h

lemma List.prefix_of_prefix_append {l1 l2 l3 : List α} (h : l1 ++ l3 <+: l2) : l1 <+: l2 := by
  obtain ⟨u, hu⟩ := h
  use l3 ++ u
  simp_all

lemma List.prefix_append_of_prefix {l1 l2 l3 : List α} (h : l1 <+: l2) : l1 <+: l2 ++ l3 := by
  obtain ⟨u, hu⟩ := h
  use u ++ l3
  rw [←hu]
  simp

lemma List.prefix_of_ne_concat {l1 l2 : List α} {a : α} (h : l1 ≠ l2 ++ [a]) (h2 : l1 <+: l2 ++ [a]) : l1 <+: l2 := by
  obtain ⟨u, hu⟩ := h2
  by_cases mt : u = []
  · subst u; simp at hu; contradiction
  · use List.take (List.length u - 1) u
    cases List.eq_nil_or_concat u with
    | inl _ => contradiction
    | inr h1 =>
      obtain ⟨L, b, hlb⟩ := h1
      subst u
      simp at hu
      rw [←List.append_assoc] at hu
      simp only [concat_eq_append, length_append, length_singleton, add_tsub_cancel_right,
        take_left']
      exact Eq.symm (append_inj_left' (id (Eq.symm hu)) rfl)

/-- Could this go into Mathlib? -/
theorem List.prefix_of_eq_append {l1 l2 l3 l4 : List α} (h : l1 ++ l2 = l3 ++ l4) :
    l1 <+: l3 ∨ l3 <+: l1 := by
  have len : l1.length ≤ l3.length ∨ l3.length ≤ l1.length := by
    apply LinearOrder.le_total
  cases len with
  | inl len =>
    apply_fun List.take (l1.length) at h
    rw[List.take_left, List.take_append_of_le_length len] at h
    rw [h]
    exact Or.inl (List.take_prefix (List.length l1) l3)
  | inr len =>
    apply_fun List.take (l3.length) at h
    rw [List.take_left, List.take_append_of_le_length len] at h
    rw [←h]
    exact Or.inr (List.take_prefix (List.length l3) l1)

theorem List.prefix_of_eq_append_append {l1 l2 l3 l1' l2' l3' : List α}
    (h : l1 ++ l2 ++ l3 = l1' ++ l2' ++ l3') : l1 <+: l1' ∨ l1' <+: l1 := by
  rw [List.append_assoc, List.append_assoc] at h
  exact List.prefix_of_eq_append h
