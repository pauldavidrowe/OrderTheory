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
