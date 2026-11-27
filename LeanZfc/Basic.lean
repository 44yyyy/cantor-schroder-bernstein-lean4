import LeanZfc.Axioms

namespace LeanZfc

noncomputable section

/-
# Basic Set Operations
-/

/-
## Subset Properties
-/

theorem subset_refl (A : Set) : A ⊆ A := by
  intro x hx
  exact hx

theorem subset_trans {A B C : Set} (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  intro x hx
  exact hBC x (hAB x hx)

theorem subset_antisymm {A B : Set} (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
  apply extensionality
  intro x
  apply Iff.intro
  exact hAB x
  exact hBA x

theorem empty_subset (A : Set) : ∅ ⊆ A := by
  intro x hx
  simp at hx

/-
## Binary Union (A ∪ B)
-/

def union (A B : Set) : Set :=
  ⋃ (pair A B)

instance : Union Set where
  union := union

@[simp]
theorem mem_union_iff (A B x : Set) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  apply Iff.intro
  intro hx
  change x ∈ ⋃ (pair A B) at hx
  rw [mem_setunion_iff] at hx
  cases hx with
  | intro Y h =>
    cases h with
    | intro hY hxY =>
      rw [mem_pair_iff] at hY
      cases hY with
      | inl hYA =>
        rw [hYA] at hxY
        exact Or.inl hxY
      | inr hYB =>
        rw [hYB] at hxY
        exact Or.inr hxY
  intro hx
  change x ∈ ⋃ (pair A B)
  rw [mem_setunion_iff]
  cases hx with
  | inl hxA =>
    apply Exists.intro A
    apply And.intro
    rw [mem_pair_iff]
    exact Or.inl rfl
    exact hxA
  | inr hxB =>
    apply Exists.intro B
    apply And.intro
    rw [mem_pair_iff]
    exact Or.inr rfl
    exact hxB

theorem union_comm (A B : Set) : A ∪ B = B ∪ A := by
  apply extensionality
  intro x
  simp [Or.comm]

theorem subset_union_left (A B : Set) : A ⊆ A ∪ B := by
  intro x hx
  simp
  exact Or.inl hx

theorem subset_union_right (A B : Set) : B ⊆ A ∪ B := by
  intro x hx
  simp
  exact Or.inr hx

/-
## Binary Intersection (A ∩ B)
-/

def inter (A B : Set) : Set :=
  sep A (fun x => x ∈ B)

instance : Inter Set where
  inter := inter

@[simp]
theorem mem_inter_iff (A B x : Set) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  mem_sep_iff A (fun z => z ∈ B) x

theorem inter_comm (A B : Set) : A ∩ B = B ∩ A := by
  apply extensionality
  intro x
  simp [And.comm]

theorem inter_subset_left (A B : Set) : A ∩ B ⊆ A := by
  intro x hx
  rw [mem_inter_iff] at hx
  cases hx with
  | intro hxA _ =>
    exact hxA

theorem inter_subset_right (A B : Set) : A ∩ B ⊆ B := by
  intro x hx
  rw [mem_inter_iff] at hx
  cases hx with
  | intro _ hxB =>
    exact hxB

/-
## Set Difference (A \ B)
-/

def sdiff (A B : Set) : Set :=
  sep A (fun x => x ∉ B)

instance : SDiff Set where
  sdiff := sdiff

@[simp]
theorem mem_sdiff_iff (A B x : Set) : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B :=
  mem_sep_iff A (fun z => z ∉ B) x

theorem sdiff_subset (A B : Set) : A \ B ⊆ A := by
  intro x hx
  rw [mem_sdiff_iff] at hx
  cases hx with
  | intro hxA _ =>
    exact hxA

theorem sdiff_inter_empty (A B : Set) : (A \ B) ∩ B = ∅ := by
  apply extensionality
  intro x
  apply Iff.intro
  intro hx
  rw [mem_inter_iff, mem_sdiff_iff] at hx
  cases hx with
  | intro hdiff hxB =>
    cases hdiff with
    | intro _ hnotB =>
      exact False.elim (hnotB hxB)
  intro hx
  simp at hx

theorem union_sdiff_of_subset {A B : Set} (h : B ⊆ A) : B ∪ (A \ B) = A := by
  apply extensionality
  intro x
  apply Iff.intro
  intro hx
  rw [mem_union_iff] at hx
  cases hx with
  | inl hxB =>
    exact h x hxB
  | inr hxDiff =>
    rw [mem_sdiff_iff] at hxDiff
    cases hxDiff with
    | intro hxA _ =>
      exact hxA
  intro hxA
  rw [mem_union_iff]
  by_cases hxB : x ∈ B
  exact Or.inl hxB
  apply Or.inr
  rw [mem_sdiff_iff]
  exact And.intro hxA hxB

end

end LeanZfc
