import mathlib

lemma Finset.sup_isLUB {α : Type} [SemilatticeSup α] [OrderBot α] (F : Finset α) :
    IsLUB F (sup F id) := ⟨λ x h => id_eq x ▸ le_sup h, λ _ h => Finset.sup_le h⟩

lemma Finset.sup'_isLUB {α : Type} [SemilatticeSup α] {F : Finset α} (ne : F.Nonempty) :
    IsLUB F (sup' F ne id) := ⟨λ x h => id_eq x ▸ le_sup' id h, λ _ h => Finset.sup'_le ne id h⟩

lemma Finset.inf_isGLB {α : Type} [SemilatticeInf α] [OrderTop α] (F : Finset α) :
    IsGLB F (inf F id) := ⟨λ x h => id_eq x ▸ inf_le h, λ _ h => Finset.le_inf h⟩

lemma Finset.inf'_isGLB {α : Type} [SemilatticeInf α] {F : Finset α} (ne : F.Nonempty) :
    IsGLB F (inf' F ne id) := ⟨λ x h => id_eq x ▸ inf'_le id h, λ _ h => Finset.le_inf' ne id h⟩
