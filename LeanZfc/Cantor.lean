import LeanZfc.Functions

namespace LeanZfc

noncomputable section

/-
# Cantor's Theorem
-/

/-
## Diagonal Set Construction
-/

def cantorDiag (f A : Set) : Set :=
  sep A (fun x => x ∉ app f x)

theorem cantorDiag_subset (f A : Set) : cantorDiag f A ⊆ A := by
  intro x hx
  change x ∈ sep A _ at hx
  rw [mem_sep_iff] at hx
  rcases hx with ⟨hxA, _⟩
  exact hxA

theorem cantorDiag_mem_powerset (f A : Set) : cantorDiag f A ∈ 𝒫 A := by
  rw [mem_powerset_iff]
  exact cantorDiag_subset f A

theorem mem_cantorDiag_iff (f A x : Set) : x ∈ cantorDiag f A ↔ x ∈ A ∧ x ∉ app f x := by
  change x ∈ sep A _ ↔ _
  rw [mem_sep_iff]

/-
## Cantor's Theorem (No Surjection from A onto 𝒫 A)
-/

theorem cantors_theorem (A : Set) : ¬ ∃ f, Surjective f A (𝒫 A) := by
  intro hex
  rcases hex with ⟨f, hsurj⟩
  rcases hsurj with ⟨_, honto⟩
  have hD : cantorDiag f A ∈ 𝒫 A := cantorDiag_mem_powerset f A
  rcases honto (cantorDiag f A) hD with ⟨a, haA, hfa⟩
  by_cases haD : a ∈ cantorDiag f A
  have hnot : a ∉ app f a := by
    rw [mem_cantorDiag_iff] at haD
    rcases haD with ⟨_, hnot⟩
    exact hnot
  rw [hfa] at hnot
  exact hnot haD
  have hin : a ∈ cantorDiag f A := by
    rw [mem_cantorDiag_iff]
    apply And.intro haA
    rw [hfa]
    exact haD
  exact haD hin

end

end LeanZfc
