namespace LeanZfc

/-
# Foundational ZFC Primitives and Axioms
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
theorem mem_pair (a b x : Set) : x ∈ pair a b ↔ x = a ∨ x = b :=
  Classical.choose_spec (pairing_yes a b) x
