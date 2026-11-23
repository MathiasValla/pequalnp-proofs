import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic

theorem PEqualNP.Outside.L_meta_713 : ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r := by
  intro n m r S B h
  classical
  have he : (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)) =
      B.biUnion (fun p => Finset.univ.filter (fun i : Fin m => p ∈ S i)) := by
    ext i
    simp
  rw [he]
  calc
    _ ≤ ∑ p ∈ B, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ B, r := Finset.sum_le_sum (fun p _ => h p)
    _ = B.card * r := by simp [Nat.mul_comm]
