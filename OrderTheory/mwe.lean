import mathlib

open OrderDual
theorem IsLUB.of_dual {α : Type*} [Preorder α] {s : Set α} {a : α} (h : IsGLB (toDual '' s) (toDual a)) : IsLUB s a := h
