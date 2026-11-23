import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_707

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

lemma side_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  apply Bool.eq_iff_iff.mpr
  simp only [sideTrue, decide_eq_true_eq]
  constructor
  · rintro (hv | ⟨j, hj, hji, hv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hj, hji, (h j hji).symm.trans hv⟩
  · rintro (hv | ⟨j, hj, hji, hv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hj, hji, (h j hji).trans hv⟩

lemma fuel_stable {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) (d e : ℕ) (hd : i.val < d) (he : i.val < e) :
    C.gateValFuel U d i = C.gateValFuel U e i := by
  have aux : ∀ k : ℕ, ∀ i : Fin C.size, i.val = k → ∀ d e : ℕ,
      i.val < d → i.val < e → C.gateValFuel U d i = C.gateValFuel U e i := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi d e hd he
      cases d with
      | zero => omega
      | succ d =>
        cases e with
        | zero => omega
        | succ e =>
          simp only [gateValFuel]
          apply congrArg₂ Bool.and <;> apply side_congr <;> intro j hj
          all_goals exact ih j.val (by omega) j rfl d e (by omega) (by omega)
  exact aux i.val i rfl d e hd he

lemma gate_unroll {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  calc
    C.gateVal U i = C.gateValFuel U (C.size+1) i :=
      fuel_stable C U i C.size (C.size+1) i.isLt (by omega)
    _ = _ := rfl

abbrev Side (n k : ℕ) := Finset (Fin n) × Finset (Fin k)

def sideVal {n k : ℕ} (U : Finset (Fin n)) (v : Fin k → Bool) (E : Side n k) : Bool :=
  decide ((∃ p ∈ E.1, p ∈ U) ∨ ∃ j ∈ E.2, v j = true)

lemma sideVal_congr {n k : ℕ} (U : Finset (Fin n)) (v w : Fin k → Bool)
    (E : Side n k) (h : ∀ j ∈ E.2, v j = w j) : sideVal U v E = sideVal U w E := by
  apply Bool.eq_iff_iff.mpr
  simp only [sideVal, decide_eq_true_eq]
  constructor
  · rintro (hv | ⟨j, hj, hv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hj, (h j hj).symm.trans hv⟩
  · rintro (hv | ⟨j, hj, hv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hj, (h j hj).trans hv⟩

lemma sideTrue_eq {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (v : Fin k → Bool) (h : ∀ j ∈ F, j < i) :
    sideTrue U B F i v = sideVal U v (B,F) := by
  apply Bool.eq_iff_iff.mpr
  simp only [sideTrue, sideVal, decide_eq_true_eq]
  constructor
  · rintro (hv | ⟨j, hj, _, hv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hj, hv⟩
  · rintro (hv | ⟨j, hj, hv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hj, h j hj, hv⟩

def substSide {n N M : ℕ} (E : Fin N → Side n M)
    (B : Finset (Fin n)) (F : Finset (Fin N)) : Side n M :=
  (B ∪ F.attach.biUnion (fun j => (E j.val).1),
    F.attach.biUnion (fun j => (E j.val).2))

lemma subst_eval {n N M : ℕ} (U : Finset (Fin n)) (v : Fin M → Bool)
    (E : Fin N → Side n M) (B : Finset (Fin n)) (F : Finset (Fin N)) :
    sideVal U v (substSide E B F) = sideVal U (fun j => sideVal U v (E j)) (B,F) := by
  apply Bool.eq_iff_iff.mpr
  simp [sideVal, substSide, Finset.mem_biUnion]
  constructor
  · rintro (⟨p, hp | ⟨a, ha, hpa⟩, hpU⟩ | ⟨j, ⟨a, ha, hja⟩, hv⟩)
    · exact Or.inl ⟨p, hp, hpU⟩
    · exact Or.inr ⟨a, ha, Or.inl ⟨p, hpa, hpU⟩⟩
    · exact Or.inr ⟨a, ha, Or.inr ⟨j, hja, hv⟩⟩
  · rintro (⟨p, hp, hpU⟩ | ⟨a, ha, (⟨p, hpa, hpU⟩ | ⟨j, hja, hv⟩)⟩)
    · exact Or.inl ⟨p, Or.inl hp, hpU⟩
    · exact Or.inl ⟨p, Or.inr ⟨a, ha, hpa⟩, hpU⟩
    · exact Or.inr ⟨j, ⟨a, ha, hja⟩, hv⟩

lemma sideVal_single {n M : ℕ} (U : Finset (Fin n)) (v : Fin M → Bool) (j : Fin M) :
    sideVal U v (∅,{j}) = v j := by
  simp [sideVal]

noncomputable def expand {n N M : ℕ} (S : Finset (Fin N))
    (B : Fin N → Finset (Fin n)) (F : Fin N → Finset (Fin N))
    (hlt : ∀ i j, j ∈ F i → j < i)
    (keep : ∀ i : Fin N, i ∉ S → Fin M) (i : Fin N) : Side n M :=
  if hi : i ∈ S then
    (B i ∪ (F i).attach.biUnion (fun j => (expand S B F hlt keep j.val).1),
      (F i).attach.biUnion (fun j => (expand S B F hlt keep j.val).2))
  else (∅, {keep i hi})
termination_by i.val
decreasing_by all_goals exact hlt i j.val j.property

lemma expand_selected {n N M : ℕ} (S : Finset (Fin N))
    (B : Fin N → Finset (Fin n)) (F : Fin N → Finset (Fin N))
    (hlt : ∀ i j, j ∈ F i → j < i) (keep : ∀ i : Fin N, i ∉ S → Fin M)
    (i : Fin N) (hi : i ∈ S) :
    expand S B F hlt keep i = substSide (expand S B F hlt keep) (B i) (F i) := by
  rw [expand, dite_eq_left hi]
  rfl

lemma expand_retained {n N M : ℕ} (S : Finset (Fin N))
    (B : Fin N → Finset (Fin n)) (F : Fin N → Finset (Fin N))
    (hlt : ∀ i j, j ∈ F i → j < i) (keep : ∀ i : Fin N, i ∉ S → Fin M)
    (i : Fin N) (hi : i ∉ S) : expand S B F hlt keep i = (∅,{keep i hi}) := by
  rw [expand, dite_eq_right hi]

lemma expand_bound {n N M : ℕ} (S : Finset (Fin N))
    (B : Fin N → Finset (Fin n)) (F : Fin N → Finset (Fin N))
    (hlt : ∀ i j, j ∈ F i → j < i) (keep : ∀ i : Fin N, i ∉ S → Fin M)
    (old : Fin M → Fin N) (hk : ∀ i hi, old (keep i hi) = i) :
    ∀ i : Fin N, ∀ j ∈ (expand S B F hlt keep i).2, old j ≤ i := by
  have aux : ∀ k : ℕ, ∀ i : Fin N, i.val = k →
      ∀ j ∈ (expand S B F hlt keep i).2, old j ≤ i := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi j hj
      by_cases hs : i ∈ S
      · rw [expand_selected S B F hlt keep i hs] at hj
        obtain ⟨a, _, hja⟩ := Finset.mem_biUnion.mp hj
        exact (ih a.val.val (by have := hlt i a.val a.property; omega)
          a.val rfl j hja).trans (hlt i a.val a.property).le
      · rw [expand_retained S B F hlt keep i hs] at hj
        have he : j = keep i hs := Finset.mem_singleton.mp hj
        rw [he, hk]
  intro i
  exact aux i.val i rfl

lemma compress {n : ℕ} (C : AndCountCircuit n) (hw : C.WellFormed)
    (D : Set (Finset (Fin n))) (S : Finset (Fin C.size))
    (hs : ∀ i ∈ S, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size),
      (∀ j ∈ F, j < i) ∧ ∀ U ∈ D, C.gateVal U i = true ↔
        ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) :
    ∃ C' : AndCountCircuit n, C'.WellFormed ∧ C'.size + S.card ≤ C.size ∧
      ∀ U ∈ D, C'.eval U = C.eval U := by
  classical
  have data : ∀ i : Fin C.size, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size),
      (∀ j ∈ F, j < i) ∧ (i ∈ S → ∀ U ∈ D, C.gateVal U i = true ↔
        ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨B, F, hlt, he⟩ := hs i hi
      exact ⟨B, F, hlt, fun _ => he⟩
    · exact ⟨∅, ∅, by simp, fun h => False.elim (hi h)⟩
  let B (i : Fin C.size) := Classical.choose (data i)
  let F (i : Fin C.size) := Classical.choose (Classical.choose_spec (data i))
  have hlt (i j : Fin C.size) (hj : j ∈ F i) : j < i :=
    (Classical.choose_spec (Classical.choose_spec (data i))).1 j hj
  have he (i : Fin C.size) (hi : i ∈ S) (U : Finset (Fin n)) (hU : U ∈ D) :
      C.gateVal U i = true ↔ ((∃ v ∈ B i, v ∈ U) ∨ ∃ j ∈ F i, C.gateVal U j = true) :=
    (Classical.choose_spec (Classical.choose_spec (data i))).2 hi U hU
  let Q := Finset.univ \ S
  let old : Fin Q.card ↪o Fin C.size := Q.orderEmbOfFin rfl
  let keep (i : Fin C.size) (hi : i ∉ S) : Fin Q.card :=
    (Q.orderIsoOfFin rfl).symm ⟨i, by simp [Q, hi]⟩
  have hk (i : Fin C.size) (hi : i ∉ S) : old (keep i hi) = i := by
    exact congrArg Subtype.val ((Q.orderIsoOfFin rfl).apply_symm_apply ⟨i, by simp [Q, hi]⟩)
  let E := expand S B F hlt keep
  let C' : AndCountCircuit n :=
    { size := Q.card
      leftVars := fun k => (substSide E (C.leftVars (old k)) (C.leftGates (old k))).1
      leftGates := fun k => (substSide E (C.leftVars (old k)) (C.leftGates (old k))).2
      rightVars := fun k => (substSide E (C.rightVars (old k)) (C.rightGates (old k))).1
      rightGates := fun k => (substSide E (C.rightVars (old k)) (C.rightGates (old k))).2
      outVars := (substSide E C.outVars C.outGates).1
      outGates := (substSide E C.outVars C.outGates).2 }
  have hb (i : Fin C.size) (k : Fin Q.card) (hik : old k = i)
      (B₀ : Finset (Fin n)) (F₀ : Finset (Fin C.size))
      (hF : ∀ j ∈ F₀, j < i) : ∀ j ∈ (substSide E B₀ F₀).2, j < k := by
    intro j hj
    obtain ⟨a, _, hja⟩ := Finset.mem_biUnion.mp hj
    have h₁ : old j ≤ a.val := expand_bound S B F hlt keep old hk a.val j hja
    have h₂ : a.val < i := hF a.val a.property
    apply old.lt_iff_lt.mp
    rw [hik]
    exact h₁.trans_lt h₂
  have hw' : C'.WellFormed := by
    intro k
    exact ⟨hb (old k) k rfl (C.leftVars (old k)) (C.leftGates (old k)) (hw (old k)).1,
      hb (old k) k rfl (C.rightVars (old k)) (C.rightGates (old k)) (hw (old k)).2⟩
  have values (U : Finset (Fin n)) (hU : U ∈ D) :
      ∀ i : Fin C.size, sideVal U (C'.gateVal U) (E i) = C.gateVal U i := by
    have aux : ∀ z : ℕ, ∀ i : Fin C.size, i.val = z →
        sideVal U (C'.gateVal U) (E i) = C.gateVal U i := by
      intro z
      induction z using Nat.strong_induction_on with
      | ind z ih =>
        intro i hi
        by_cases hS : i ∈ S
        · rw [show E i = substSide E (B i) (F i) from expand_selected S B F hlt keep i hS,
            subst_eval]
          have hside : sideVal U (fun j => sideVal U (C'.gateVal U) (E j)) (B i,F i) =
              sideVal U (C.gateVal U) (B i,F i) := by
            apply sideVal_congr
            intro j hj
            exact ih j.val (by have := hlt i j hj; omega) j rfl
          rw [hside]
          apply Bool.eq_iff_iff.mpr
          simpa only [sideVal, decide_eq_true_eq] using (he i hS U hU).symm
        · rw [show E i = (∅,{keep i hS}) from expand_retained S B F hlt keep i hS,
            sideVal_single]
          let k := keep i hS
          have hki : old k = i := hk i hS
          change C'.gateVal U k = C.gateVal U i
          apply Eq.trans (b := C.gateVal U (old k)) ?_ (congrArg (C.gateVal U) hki)
          rw [gate_unroll C' U k, gate_unroll C U (old k)]
          apply congrArg₂ Bool.and
          · rw [sideTrue_eq U _ _ k _ (hw' k).1,
              sideTrue_eq U _ _ (old k) _ (hw (old k)).1]
            change sideVal U (C'.gateVal U)
                (substSide E (C.leftVars (old k)) (C.leftGates (old k))) = _
            rw [subst_eval]
            apply sideVal_congr
            intro j hj
            have hjlt : j < i := by rw [← hki]; exact (hw (old k)).1 j hj
            exact ih j.val (by have := hjlt; omega) j rfl
          · rw [sideTrue_eq U _ _ k _ (hw' k).2,
              sideTrue_eq U _ _ (old k) _ (hw (old k)).2]
            change sideVal U (C'.gateVal U)
                (substSide E (C.rightVars (old k)) (C.rightGates (old k))) = _
            rw [subst_eval]
            apply sideVal_congr
            intro j hj
            have hjlt : j < i := by rw [← hki]; exact (hw (old k)).2 j hj
            exact ih j.val (by have := hjlt; omega) j rfl
    intro i
    exact aux i.val i rfl
  refine ⟨C', hw', ?_, ?_⟩
  · change Q.card + S.card ≤ C.size
    simpa only [Q, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)).le
  · intro U hU
    change sideVal U (C'.gateVal U) (substSide E C.outVars C.outGates) =
      sideVal U (C.gateVal U) (C.outVars,C.outGates)
    rw [subst_eval]
    exact sideVal_congr U _ _ _ (fun j _ => values U hU j)

end PEqualNP.Outside.L_meta_707

theorem PEqualNP.Outside.L_meta_707 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (S : Finset (Fin C.size)),
      (∀ i ∈ S, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size), (∀ j ∈ F, j < i) ∧
        ∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + S.card ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  intro n C hw D S hs
  exact PEqualNP.Outside.L_meta_707.compress C hw D S hs
