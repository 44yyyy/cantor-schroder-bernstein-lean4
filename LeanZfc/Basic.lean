import LeanZfc.Axioms

namespace LeanZfc

noncomputable section

/-
# Basic Stuff
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
## Binary Union
-/

def union (A B : Set) : Set :=
  ⋃ (pair A B)

instance : Union Set where
  union := union

@[simp]
theorem mem_union_iff (A B x : Set) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  apply Iff.intro
  intro hx
  dsimp [Union.union, union] at hx
  rw [mem_setunion_iff] at hx
  let ⟨Y, hY, hxY⟩ := hx
  rw [mem_pair_iff] at hY
  cases hY with
  | inl hYA =>
    rw [hYA] at hxY
    exact Or.inl hxY
  | inr hYB =>
    rw [hYB] at hxY
    exact Or.inr hxY
  intro hx
  dsimp [Union.union, union]
  rw [mem_setunion_iff]
  cases hx with
  | inl hxA =>
    exact ⟨A, by simp, hxA⟩
  | inr hxB =>
    exact ⟨B, by simp, hxB⟩

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
## Binary Intersection
-/

def intersection (A B : Set) : Set :=
  sep A (fun x => x ∈ B)

instance : Inter Set where
  inter := intersection

@[simp]
theorem mem_intersection_iff (A B x : Set) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  mem_sep_iff A (fun z => z ∈ B) x

theorem intersection_comm (A B : Set) : A ∩ B = B ∩ A := by
  apply extensionality
  intro x
  simp [And.comm]

theorem intersection_subset_left (A B : Set) : A ∩ B ⊆ A := by
  intro x hx
  simp at hx
  exact hx.1

theorem intersection_subset_right (A B : Set) : A ∩ B ⊆ B := by
  intro x hx
  simp at hx
  exact hx.2

/-
## Set Difference
-/

def setdiff (A B : Set) : Set :=
  sep A (fun x => x ∉ B)

instance : SDiff Set where
  sdiff := setdiff

@[simp]
theorem mem_setdiff_iff (A B x : Set) : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B :=
  mem_sep_iff A (fun z => z ∉ B) x

theorem setdiff_subset (A B : Set) : A \ B ⊆ A := by
  intro x hx
  simp at hx
  exact hx.1

theorem setdiff_inter_empty (A B : Set) : (A \ B) ∩ B = ∅ := by
  apply extensionality
  intro x
  apply Iff.intro
  intro hx
  simp at hx
  exact False.elim (hx.1.2 hx.2)
  intro hx
  simp at hx

theorem union_setdiff_of_subset {A B : Set} (h : B ⊆ A) : B ∪ (A \ B) = A := by
  apply extensionality
  intro x
  apply Iff.intro
  intro hx
  simp at hx
  cases hx with
  | inl hxB => exact h x hxB
  | inr hxDiff => exact hxDiff.1
  intro hxA
  simp
  by_cases hxB : x ∈ B
  exact Or.inl hxB
  exact Or.inr ⟨hxA, hxB⟩

end

end LeanZfc
