import Mathlib

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
