import Mathlib.Data.Set.Basic
open Set

-- YProof's Basic Set theorems
namespace YSet

variable {U : Type}
-- ∀ A, B sets
variable (A B C D: Set U)

example (x : U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2

example (x : U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  apply h2
  apply h1
  exact h3

theorem subset_union_left : A ⊆ A ∪ B := by
  intro x hx
  left
  exact hx

theorem inter_subset_left : A ∩ B ⊆ A := by
  intro x hx
  exact hx.1

end YSet
