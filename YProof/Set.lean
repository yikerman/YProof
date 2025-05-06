import Mathlib.Data.Set.Basic
open Set

namespace YSet.Subset

variable {U : Type}
variable (x : U)
variable (A B C : Set U)

example (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2

example (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  apply h2
  apply h1
  exact h3

example (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  have h4 : x ∈ B := h1 h3
  exact h2 h4

example (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
  intro h3
  have h4 := h1 h3
  exact h2 h4

theorem subset_refl : A ⊆ A := by
  intro x hx
  exact hx

theorem subset_trans (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x hx
  have h3 := h1 hx
  have h4 := h2 h3
  exact h4

theorem subset_antisymm (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B :=
  Set.ext (fun _ => Iff.intro
    (fun hx => h1 hx)
    (fun hx => h2 hx))

end YSet.Subset

namespace YSet.Complement

variable {U : Type}
variable (x : U)
variable (A B : Set U)

example (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  by_contra h3
  have h4 := h3 h1
  exact h2 h4

theorem mem_compl_iff : x ∈ Aᶜ ↔ x ∉ A := by
  rfl

theorem compl_subset_compl_of_subset (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x h2
  rw [mem_compl_iff x A]
  rw [mem_compl_iff] at h2
  by_contra hc
  have h3 := h1 hc
  exact h2 h3

theorem compl_compl : Aᶜᶜ = A := by
  apply subset_antisymm

  intro x hx
  rw [mem_compl_iff] at hx
  rw [mem_compl_iff] at hx
  push_neg at hx
  exact hx

  intro x hx
  rw [mem_compl_iff]
  rw [mem_compl_iff]
  push_neg
  exact hx
  
example : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  
  intro h1
  apply compl_subset_compl_of_subset
  exact h1

  intro h1 
  have h2 := compl_subset_compl_of_subset Bᶜ Aᶜ h1
  rw [compl_compl] at h2
  rw [compl_compl] at h2
  exact h2
  

end YSet.Complement
