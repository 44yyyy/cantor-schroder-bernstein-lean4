import LeanZfc.Basic

namespace LeanZfc

noncomputable section

/-
# Singletons, Pairs, Cartesian Products
-/

/-
## Singletons
-/

def singleton (a : Set) : Set :=
  pair a a

@[simp]
theorem mem_singleton_iff (a x : Set) : x ∈ singleton a ↔ x = a := by
  apply Iff.intro
  intro hx
  change x ∈ pair a a at hx
  rw [mem_pair_iff] at hx
  cases hx with
  | inl h => exact h
  | inr h => exact h
  intro hx
  change x ∈ pair a a
  rw [mem_pair_iff]
  exact Or.inl hx

theorem singleton_inj {a b : Set} (h : singleton a = singleton b) : a = b := by
  have ha : a ∈ singleton a := by
    rw [mem_singleton_iff]
  rw [h, mem_singleton_iff] at ha
  exact ha

/-
## Ordered Pairs (Kuratowski Definition: (a, b) = {{a}, {a, b}})
-/

def opair (a b : Set) : Set :=
  pair (singleton a) (pair a b)

theorem mem_opair_iff (a b x : Set) : x ∈ opair a b ↔ x = singleton a ∨ x = pair a b := by
  change x ∈ pair (singleton a) (pair a b) ↔ _
  rw [mem_pair_iff]

theorem pair_eq_singleton_iff {a b c : Set} : pair a b = singleton c ↔ a = c ∧ b = c := by
  apply Iff.intro
  intro h
  have ha : a ∈ singleton c := by
    rw [← h, mem_pair_iff]
    exact Or.inl rfl
  have hb : b ∈ singleton c := by
    rw [← h, mem_pair_iff]
    exact Or.inr rfl
  rw [mem_singleton_iff] at ha hb
  exact And.intro ha hb
  intro h
  rw [h.1, h.2]
  rfl

theorem opair_fst_eq {a b c d : Set} (h : opair a b = opair c d) : a = c := by
  have hs : singleton a ∈ opair c d := by
    rw [← h, mem_opair_iff]
    exact Or.inl rfl
  rw [mem_opair_iff] at hs
  cases hs with
  | inl h1 =>
    exact singleton_inj h1
  | inr h2 =>
    have hcd : c = a ∧ d = a := (pair_eq_singleton_iff.mp h2.symm)
    exact hcd.1.symm

theorem opair_snd_eq {a b c d : Set} (h : opair a b = opair c d) : b = d := by
  have hac : a = c := opair_fst_eq h
  rw [← hac] at h
  have hp1 : pair a b ∈ opair a d := by
    rw [← h, mem_opair_iff]
    exact Or.inr rfl
  rw [mem_opair_iff] at hp1
  cases hp1 with
  | inl h_ab_sing =>
    have hab : a = a ∧ b = a := pair_eq_singleton_iff.mp h_ab_sing
    have hp2 : pair a d ∈ opair a b := by
      rw [h, mem_opair_iff]
      exact Or.inr rfl
    rw [mem_opair_iff] at hp2
    cases hp2 with
    | inl h_ad_sing =>
      have had : a = a ∧ d = a := pair_eq_singleton_iff.mp h_ad_sing
      rw [hab.2, had.2]
    | inr h_ad_eq =>
      rw [← h_ad_eq] at h_ab_sing
      have had : a = a ∧ d = a := pair_eq_singleton_iff.mp h_ab_sing
      rw [hab.2, had.2]
  | inr h_ab_eq =>
    have hb : b ∈ pair a d := by
      rw [← h_ab_eq, mem_pair_iff]
      exact Or.inr rfl
    rw [mem_pair_iff] at hb
    cases hb with
    | inl hba =>
      have hd : d ∈ pair a b := by
        rw [h_ab_eq, mem_pair_iff]
        exact Or.inr rfl
      rw [mem_pair_iff] at hd
      cases hd with
      | inl hda => rw [hba, hda]
      | inr hdb => exact hdb.symm
    | inr hbd => exact hbd

@[simp]
theorem opair_inj (a b c d : Set) : opair a b = opair c d ↔ a = c ∧ b = d := by
  apply Iff.intro
  intro h
  exact And.intro (opair_fst_eq h) (opair_snd_eq h)
  intro h
  rw [h.1, h.2]

/-
## Cartesian Product (A ×ˢ B)
-/

def product (A B : Set) : Set :=
  sep (𝒫 (𝒫 (A ∪ B))) (fun p => ∃ a ∈ A, ∃ b ∈ B, p = opair a b)

infixr:70 " ×ˢ " => product

@[simp]
theorem mem_product_iff (A B p : Set) : p ∈ A ×ˢ B ↔ ∃ a ∈ A, ∃ b ∈ B, p = opair a b := by
  change p ∈ sep (𝒫 (𝒫 (A ∪ B))) _ ↔ _
  rw [mem_sep_iff]
  apply Iff.intro
  intro h
  exact h.2
  intro h
  apply And.intro
  cases h with
  | intro a ha =>
    cases ha with
    | intro haA hb =>
      cases hb with
      | intro b hb =>
        cases hb with
        | intro hbB hp =>
          rw [hp, mem_powerset_iff]
          intro z hz
          rw [mem_opair_iff] at hz
          rw [mem_powerset_iff]
          intro w hw
          rw [mem_union_iff]
          cases hz with
          | inl hz1 =>
            rw [hz1, mem_singleton_iff] at hw
            rw [hw]
            exact Or.inl haA
          | inr hz2 =>
            rw [hz2, mem_pair_iff] at hw
            cases hw with
            | inl hwa =>
              rw [hwa]
              exact Or.inl haA
            | inr hwb =>
              rw [hwb]
              exact Or.inr hbB
  exact h

theorem opair_mem_product {A B a b : Set} (ha : a ∈ A) (hb : b ∈ B) : opair a b ∈ A ×ˢ B := by
  rw [mem_product_iff]
  apply Exists.intro a
  apply And.intro ha
  apply Exists.intro b
  apply And.intro hb
  rfl

end

end LeanZfc
