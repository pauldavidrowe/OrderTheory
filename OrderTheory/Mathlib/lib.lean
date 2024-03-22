import Mathlib.Order.WithBot
import Mathlib.Order.UpperLower.Basic

def WithTop.untop_le [PartialOrder α] {y : α} (x : WithTop α) : x ≤ some y → α :=
  match x with
  | some a => λ _ ↦ a
  | none => λ le ↦ by exfalso; apply WithTop.not_top_le_coe y le

@[simp]
theorem WithTop.coe_untop_le [PartialOrder α] {y : α} (x : WithTop α) (h : x ≤ some y) :
    ↑(WithTop.untop_le x h) = x := by
  cases x with
  | some a => simp [untop_le]; rfl
  | none => exfalso; apply WithTop.not_top_le_coe y h

-- Not in Mathlib!?!
instance instLowerSetHasSubset [Preorder P] : HasSubset (LowerSet P) :=
{
  Subset := λ H K ↦ ∀ x, x ∈ H → x ∈ K
}

instance instUpperSetHasSubset [Preorder P] : HasSubset (UpperSet P) :=
{
  Subset := λ H K ↦ ∀ x, x ∈ H → x ∈ K
}

instance LowerSet.instEmptyCollection [LE P] : EmptyCollection (LowerSet P) :=
{
  emptyCollection := ⟨∅, isLowerSet_empty⟩
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

theorem WithTop.orderIso [PartialOrder P] [PartialOrder Q] (f : P ≃o Q) :
    WithTop P ≃o WithTop Q :=
  {
  toFun := WithTop.map f.toFun
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
