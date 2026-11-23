namespace LeanZfc

/-
# ZFC Primitives and Axioms
-/

/-
# Sets
-/

axiom Set : Type

/-
# Membership relation
-/

axiom mem : Set -> Set -> Prop
  -- mem A x means x ∈ A

instance : Membership Set Set where
  mem := mem
  -- Hooking into Lean's built in ∈, ∉, ∀x ∈ A, ∃x ∈ A

/-
# Subset relation
-/

def Subset (A B : Set) : Prop :=
  ∀ x, x ∈ A → x ∈ B

infix:50 " ⊆ " => Subset -- Mapping it

/-
# Axioms
-/

/-
# 1. Extensionality
-/

@[ext]
axiom extensionality {A B : Set} : (∀ x, x ∈ A ↔ x ∈ B) → A = B

/-
## 2. Empty Set
-/

axiom empty_yes : ∃ E : Set, ∀ x, x ∉ E

noncomputable def empty : Set :=
  Classical.choose empty_yes

noncomputable instance : EmptyCollection Set where
  emptyCollection := empty

@[simp]
theorem no_mem_empty (x : Set) : x ∉ (∅ : Set) :=
  Classical.choose_spec empty_yes x

/-
## 3. Pairing
-/

axiom pairing_yes (a b : Set) : ∃ P : Set, ∀ x, x ∈ P ↔ x = a ∨ x = b

noncomputable def pair (a b : Set) : Set :=
  Classical.choose (pairing_yes a b)

@[simp]
theorem mem_pair_iff (a b x : Set) : x ∈ pair a b ↔ x = a ∨ x = b :=
  Classical.choose_spec (pairing_yes a b) x

/-
## 4. Union
-/

axiom union_yes (A : Set) : ∃ U : Set, ∀ x, x ∈ U ↔ ∃ Y ∈ A, x ∈ Y

noncomputable def setunion (A : Set) : Set :=
  Classical.choose (union_yes A)

prefix:110 "⋃ " => setunion

@[simp]
theorem mem_setunion_iff (A x : Set) : x ∈ ⋃ A ↔ ∃ Y ∈ A, x ∈ Y :=
  Classical.choose_spec (union_yes A) x

/-
## 5. Power Set
-/

axiom powerset_yes (A : Set) : ∃ P : Set, ∀ Y, Y ∈ P ↔ Y ⊆ A

noncomputable def powerset (A : Set) : Set :=
  Classical.choose (powerset_yes A)

prefix:110 "𝒫 " => powerset

@[simp]
theorem mem_powerset_iff (A Y : Set) : Y ∈ 𝒫 A ↔ Y ⊆ A :=
  Classical.choose_spec (powerset_yes A) Y

/-
## 6. Separation
-/

axiom separation_yes (A : Set) (P : Set → Prop) :
  ∃ S : Set, ∀ x, x ∈ S ↔ x ∈ A ∧ P x

noncomputable def sep (A : Set) (P : Set → Prop) : Set :=
  Classical.choose (separation_yes A P)

@[simp]
theorem mem_sep_iff (A : Set) (P : Set → Prop) (x : Set) :
  x ∈ sep A P ↔ x ∈ A ∧ P x :=
  Classical.choose_spec (separation_yes A P) x

/-
## Check: Uniqueness of the Empty Set
-/

theorem empty_unique (E : Set) (hE : ∀ x, x ∉ E) : E = ∅ := by
  apply extensionality
  intro x
  apply Iff.intro
  intro hx
  exact False.elim (hE x hx)
  intro hx
  exact False.elim (no_mem_empty x hx)

end LeanZfc
