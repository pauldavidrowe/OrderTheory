import OrderTheory.Chapter01

/-!
  # Exercises for Chapter 1

  Not all exercises are relevant to the project of foramlization.
  In particular, exercises that involve drawing diagrams or making
  complete lists of certain kinds of orders are not remotely illuminated
  by having a formal treatment. Therefore, the below represent a selection
  of exercises, more or less based on my personal preferences. Of particular note
  is that exercises dealing with facts about finite orders are omitted unless and
  until I get more familiar with dealing with finite sets in any sane way.
-/

/-!
  ## Exercise 1.5

  The text has it about all binary strings, but I rephrase it in terms of finite
  binary strings because I don't have all binary strings defined as an order I know
  how to deal with.

  Prove that the ordered set of finite binary strings is a "tree". That is, it is
  an ordered set with ⊥ such that `∀ x : P, IsChain ↓ᵖx`.
-/

/-- A class defining trees as in the text. -/
class OrderTree (P : Type u) [PartialOrder P] [OrderBot P] : Type v where
  tree' : (∀ x : P, IsChain_le (↓ᵖx).carrier)

lemma exercise_1_5 : OrderTree (List (Fin 2)) :=
  {
    tree' := by
      intro l
      induction l using List.list_reverse_induction with
      | base =>
        intro x xmem y ymem _
        obtain ⟨u, hu⟩ := xmem
        obtain ⟨v, hv⟩ := ymem
        apply List.append_eq_nil.mp at hu
        apply List.append_eq_nil.mp at hv
        left; rw [hu.1, hv.1]
      | ind frnt bk ih =>
        intro x xmem y ymem neq
        by_cases hx : x <+: frnt
        · by_cases hy : y <+: frnt
          · apply ih hx hy neq
          · simp at ymem
            have yeq : y = frnt ++ [bk] := by
              by_contra h1
              apply hy
              exact List.prefix_of_ne_concat h1 ymem
            subst y
            left
            exact xmem
        · by_cases y <+: frnt
          · simp at xmem
            have xeq : x = frnt ++ [bk] := by
              by_contra h1
              apply hx
              exact List.prefix_of_ne_concat h1 xmem
            subst x
            right
            exact ymem
          · simp at xmem
            have xeq : x = frnt ++ [bk] := by
              by_contra h1
              apply hx
              exact List.prefix_of_ne_concat h1 xmem
            subst x
            right
            exact ymem
  }

/-!
  ## Exercise 1.6

  Define an order on `List (Fin 2)` such that `u ≤ v` if and only if
  `v <+: u` or `∃ x y z, v = x ++ [0] ++ y ∧ u = x ++ [1] ++ z`. Show that
  `≤` is an order on `List (Fin 2)` and that it is a chain with `⊤` but no `⊥`.
-/
namespace Ex_1_6 

def P := List (Fin 2)

instance instBinStringLE : LE P :=
{
  le := λ u v ↦ (v <+: u) ∨ 
  (∃ x, x ++ [0] <+: v ∧ x ++ [1] <+: u)
}

instance instBinStringLT : LT P := 
  {
    lt := λ u v ↦ instBinStringLE.le u v ∧ ¬instBinStringLE.le v u
  }

/-- Could this go into Mathlib? -/
def List.IsPrefix.of_eq_append {l1 l2 l3 l4 : List α} (h : l1 ++ l2 = l3 ++ l4) :
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

lemma le_refl : ∀ a : P, a ≤ a := by
  intro a; left; apply List.prefix_rfl 
  
lemma le_trans : ∀ a b c : P, a ≤ b → b ≤ c → a ≤ c := by 
  intro a b c leab lebc 
  simp [instBinStringLE] at leab lebc 
  cases leab with 
  | inl h1 => cases lebc with 
    | inl h2 => left; exact List.IsPrefix.trans h2 h1
    | inr h2 => 
      obtain ⟨b', hb'⟩ := h1 
      obtain ⟨x, ⟨y, h1⟩, ⟨z, h2⟩⟩ := h2
      subst b; subst a; subst c 
      right
      use x 
      constructor
      · use y 
      · use z ++ b'; simp 
  | inr h1 => cases lebc with 
    | inl h2 => 
      obtain ⟨x, ⟨⟨y, hy⟩, ⟨z, hz⟩⟩⟩ := h1 
      obtain ⟨a', ha'⟩ := h2 
      subst b; subst a 
      rw [List.append_assoc] at ha' 
      cases List.IsPrefix.of_eq_append ha' with 
      | inl h => 
        left 
        apply List.IsPrefix.trans h 
        use [1] ++ z; simp 
      | inr h => 
        obtain ⟨xc, hxc⟩ := h; subst c 
        rw [List.append_assoc] at ha'
        apply List.append_cancel_left at ha' 
        rw [List.singleton_append, List.append_eq_cons] at ha' 
        cases ha' with 
          | inl ha' => rw [ha'.1]; left; simp 
          | inr ha' => 
            obtain ⟨s, hs1, _⟩ := ha' 
            subst xc; right; use x; 
            constructor 
            · use s; simp 
            · use z 
    | inr h2 => 
      obtain ⟨x1, ⟨⟨y1, hy1⟩, ⟨z1, hz1⟩⟩⟩ := h1 
      obtain ⟨x2, ⟨⟨y2, hy2⟩, ⟨z2, hz2⟩⟩⟩ := h2 
      subst b; subst a; subst c 
      rw [List.append_assoc, List.append_assoc] at hz2 
      have h := List.IsPrefix.of_eq_append hz2 
      cases h with 
      | inl h => 
        obtain ⟨s, hs⟩ := h 
        subst x1 
        rw [List.append_assoc] at hz2
        apply List.append_cancel_left at hz2
        simp at hz2; symm at hz2 
        rw [List.append_eq_cons] at hz2
        cases hz2 with 
        | inl h => 
          rw [h.1]; right; use x2; constructor
          · use y2
          · use z1; simp  
        | inr h => 
          obtain ⟨t, ht1, _⟩ := h
          subst s 
          right; use x2; constructor
          · use y2
          · use t ++ [1] ++ z1; simp 
      | inr h => 
        obtain ⟨s, hs⟩ := h 
        subst x2 
        rw [List.append_assoc] at hz2
        apply List.append_cancel_left at hz2
        simp at hz2
        rw [List.append_eq_cons] at hz2
        cases hz2 with 
        | inl h => 
          rw [h.1]; right; use x1; constructor
          · use y2; simp 
          · use z1 
        | inr h => 
          obtain ⟨t, ht1, _⟩ := h
          subst s 
          right; use x1; constructor
          · use t ++ [0] ++ y2; simp 
          · use z1

lemma le_antisymm : ∀ a b : P, a ≤ b → b ≤ a → a = b := by 
  intro a b le1 le2 
  cases le1 with 
  | inl le1 => cases le2 with 
    | inl le2 => exact List.IsPrefix.antisymm le2 le1
    | inr le2 => 
      exfalso 
      obtain ⟨s, ⟨y, h1⟩, ⟨z, h2⟩⟩ := le2 
      obtain ⟨x, hx⟩ := le1 
      subst a; subst b 
      rw [List.append_assoc, List.append_assoc, List.append_assoc] at hx
      apply List.append_cancel_left at hx 
      cases hx 
  | inr le1 => cases le2 with 
    | inl le2 => 
      obtain ⟨s, ⟨y, h1⟩, ⟨z, h2⟩⟩ := le1 
      obtain ⟨x, hx⟩ := le2
      subst a; subst b 
      rw [List.append_assoc, List.append_assoc, List.append_assoc] at hx
      apply List.append_cancel_left at hx 
      cases hx 
    | inr le2 => 
      obtain ⟨s, ⟨y, h1⟩, ⟨z, h2⟩⟩ := le1 
      obtain ⟨t, ⟨u, hu⟩, ⟨v, hv⟩⟩ := le2 
      subst a; subst b 
      exfalso
      rw [List.append_assoc, List.append_assoc] at hu
      have h := List.IsPrefix.of_eq_append hu 
      cases h with 
      | inl h => 
        obtain ⟨x, hx⟩ := h
        subst s 
        rw [List.append_assoc, List.append_assoc, List.append_assoc] at hv 
        rw [List.append_assoc] at hu  
        apply List.append_cancel_left at hv 
        apply List.append_cancel_left at hu 
        rw [List.singleton_append] at hv hu
        symm at hv hu 
        rw [List.append_eq_cons] at hv hu 
        cases hv with 
        | inl hv => cases hu with 
          | inl hu => simp_all  
          | inr hu => rw [hv.1] at hu; simp at hu 
        | inr hv => 
          obtain ⟨s, hs⟩ := hv 
          rw [hs.1] at hu; simp at hu 
      | inr h => 
        obtain ⟨x, hx⟩ := h
        subst t 
        rw [List.append_assoc, List.append_assoc, List.append_assoc] at hv 
        rw [List.append_assoc] at hu  
        apply List.append_cancel_left at hv 
        apply List.append_cancel_left at hu 
        nth_rewrite 2 [List.singleton_append] at hv hu
        rw [List.append_eq_cons] at hv hu 
        cases hv with 
        | inl hv => cases hu with 
          | inl hu => simp_all  
          | inr hu => rw [hv.1] at hu; simp at hu 
        | inr hv => 
          obtain ⟨s, hs⟩ := hv 
          rw [hs.1] at hu; simp at hu 
              
lemma le_total : ∀ a b : P, a ≤ b ∨ b ≤ a := by 
  intro a
  induction a using List.list_reverse_induction with 
  | base => 
    intro b; right; left; use b; simp 
  | ind f x ih => 
    intro b 
    specialize ih b 
    cases ih with 
    | inl ih => cases ih with 
      | inl ih => 
        left; left 
        obtain ⟨u, hu⟩ := ih
        subst f 
        use u ++ [x]; simp 
      | inr ih => 
        obtain ⟨u, hu1, hu2⟩ := ih 
        left; right; 
        use u; constructor 
        · exact hu1 
        · exact List.prefix_append_of_prefix hu2 
    | inr ih => cases ih with 
      | inl ih => 
        obtain ⟨u, hu⟩ := ih 
        cases u with 
        | nil => 
          rw [List.append_nil] at hu 
          subst f
          left; left; use [x] 
        | cons h t => 
          subst b 
          fin_cases x <;> fin_cases h 
          · right; left; use t; simp 
          · right; right; use f; constructor 
            · exact List.prefix_rfl 
            · use t; simp 
          · left; right; use f; constructor 
            · use t; simp 
            · exact List.prefix_rfl 
          · right; left; use t; simp 
      | inr ih => 
        obtain ⟨u, hu1, hu2⟩ := ih 
        right; right; use u; constructor 
        · apply List.prefix_append_of_prefix hu1 
        · exact hu2 
            
def instBinStringLinearOrder : LinearOrder P :=
  {
    le := instBinStringLE.le 
    lt := instBinStringLT.lt 
    lt_iff_le_not_le := λ x y ↦ by
      constructor 
      · intro lt; exact lt 
      · intro lt; exact lt 
    le_refl := le_refl 
    le_trans := le_trans      
    le_antisymm := le_antisymm
    le_total := le_total 
  }

def instBinStringOrderTop : OrderTop P := 
  {
    top := []
    le_top := λ a ↦ by left; use a; simp 
  }

end Ex_1_6 
