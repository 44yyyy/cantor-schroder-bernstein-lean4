import LeanZfc.Pairs

namespace LeanZfc

noncomputable section

/-
# Functions
-/

/-
## Function Definition (Sets of Ordered Pairs)
-/

def func (f A B : Set) : Prop :=
  f ⊆ A ×ˢ B ∧
  (∀ a ∈ A, ∃ b ∈ B, opair a b ∈ f) ∧
  (∀ a ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B, opair a b₁ ∈ f → opair a b₂ ∈ f → b₁ = b₂)

theorem func_mem_product {f A B p : Set} (hf : func f A B) (hp : p ∈ f) : p ∈ A ×ˢ B := by
  cases hf with
  | intro hsub _ =>
    exact hsub p hp

theorem func_total {f A B a : Set} (hf : func f A B) (ha : a ∈ A) :
    ∃ b ∈ B, opair a b ∈ f := by
  cases hf with
  | intro _ hrest =>
    cases hrest with
    | intro htot _ =>
      exact htot a ha

theorem func_unique {f A B a b₁ b₂ : Set} (hf : func f A B)
    (ha : a ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (h1 : opair a b₁ ∈ f) (h2 : opair a b₂ ∈ f) : b₁ = b₂ := by
  cases hf with
  | intro _ hrest =>
    cases hrest with
    | intro _ huniq =>
      exact huniq a ha b₁ hb₁ b₂ hb₂ h1 h2

/-
## Function Application (f(a))
-/

def app (f a : Set) : Set :=
  open Classical in
  if h : ∃ b, opair a b ∈ f then Classical.choose h else ∅

theorem app_spec {f a : Set} (h : ∃ b, opair a b ∈ f) : opair a (app f a) ∈ f := by
  open Classical in
  change opair a (if h' : ∃ b, opair a b ∈ f then Classical.choose h' else ∅) ∈ f
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem opair_app_mem {f A B a : Set} (hf : func f A B) (ha : a ∈ A) :
    opair a (app f a) ∈ f := by
  have hex : ∃ b, opair a b ∈ f := by
    cases func_total hf ha with
    | intro b hb =>
      cases hb with
      | intro _ hmem =>
        apply Exists.intro b
        exact hmem
  exact app_spec hex

theorem app_mem_codomain {f A B a : Set} (hf : func f A B) (ha : a ∈ A) :
    app f a ∈ B := by
  have hp : opair a (app f a) ∈ f := opair_app_mem hf ha
  have hprod : opair a (app f a) ∈ A ×ˢ B := func_mem_product hf hp
  rw [mem_product_iff] at hprod
  cases hprod with
  | intro a' ha' =>
    cases ha' with
    | intro _ hb =>
      cases hb with
      | intro b hb =>
        cases hb with
        | intro hbB heq =>
          rw [opair_inj] at heq
          cases heq with
          | intro _ heqb =>
            rw [heqb]
            exact hbB

theorem app_eq_of_mem {f A B a b : Set} (hf : func f A B)
    (ha : a ∈ A) (hb : b ∈ B) (hmem : opair a b ∈ f) : app f a = b := by
  have h1 : opair a (app f a) ∈ f := opair_app_mem hf ha
  have h2 : app f a ∈ B := app_mem_codomain hf ha
  exact func_unique hf ha h2 hb h1 hmem

/-
## Constructing Functions from Rules
-/

def makefunc (A B : Set) (g : Set → Set) : Set :=
  sep (A ×ˢ B) (fun p => ∃ a ∈ A, p = opair a (g a))

theorem mem_makefunc_iff (A B : Set) (g : Set → Set) (p : Set) :
    p ∈ makefunc A B g ↔ ∃ a ∈ A, g a ∈ B ∧ p = opair a (g a) := by
  change p ∈ sep (A ×ˢ B) _ ↔ _
  rw [mem_sep_iff, mem_product_iff]
  apply Iff.intro
  intro h
  rcases h with ⟨⟨_, _, b, hbB, hp'⟩, ⟨a, haA, hp⟩⟩
  rw [hp, opair_inj] at hp'
  rcases hp' with ⟨_, hgb⟩
  rw [← hgb] at hbB
  exact ⟨a, haA, hbB, hp⟩
  intro h
  rcases h with ⟨a, haA, hgB, hp⟩
  exact ⟨⟨a, haA, g a, hgB, hp⟩, ⟨a, haA, hp⟩⟩

theorem makefunc_func {A B : Set} {g : Set → Set} (hg : ∀ a ∈ A, g a ∈ B) :
    func (makefunc A B g) A B := by
  apply And.intro
  intro p hp
  rw [mem_makefunc_iff] at hp
  cases hp with
  | intro a ha =>
    cases ha with
    | intro haA hrest =>
      cases hrest with
      | intro hgB hp =>
        rw [hp]
        exact opair_mem_product haA hgB
  apply And.intro
  intro a ha
  apply Exists.intro (g a)
  apply And.intro (hg a ha)
  rw [mem_makefunc_iff]
  apply Exists.intro a
  apply And.intro ha
  apply And.intro (hg a ha)
  rfl
  intro a ha b₁ hb₁ b₂ hb₂ h1 h2
  rw [mem_makefunc_iff] at h1 h2
  cases h1 with
  | intro a₁ ha₁ =>
    cases ha₁ with
    | intro _ hrest₁ =>
      cases hrest₁ with
      | intro _ heq₁ =>
        cases h2 with
        | intro a₂ ha₂ =>
          cases ha₂ with
          | intro _ hrest₂ =>
            cases hrest₂ with
            | intro _ heq₂ =>
              rw [opair_inj] at heq₁ heq₂
              cases heq₁ with
              | intro ha₁a hb₁g =>
                cases heq₂ with
                | intro ha₂a hb₂g =>
                  rw [hb₁g, ← ha₁a, ha₂a, ← hb₂g]

theorem app_makefunc {A B : Set} {g : Set → Set} (hg : ∀ a ∈ A, g a ∈ B)
    {a : Set} (ha : a ∈ A) : app (makefunc A B g) a = g a := by
  apply app_eq_of_mem (makefunc_func hg) ha (hg a ha)
  rw [mem_makefunc_iff]
  apply Exists.intro a
  apply And.intro ha
  apply And.intro (hg a ha)
  rfl

/-
## Injectivity, Surjectivity, and Bijectivity
-/

def Injective (f A B : Set) : Prop :=
  func f A B ∧ ∀ a₁ ∈ A, ∀ a₂ ∈ A, app f a₁ = app f a₂ → a₁ = a₂

def Surjective (f A B : Set) : Prop :=
  func f A B ∧ ∀ b ∈ B, ∃ a ∈ A, app f a = b

def Bijective (f A B : Set) : Prop :=
  Injective f A B ∧ Surjective f A B

end

end LeanZfc
