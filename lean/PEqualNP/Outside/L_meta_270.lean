import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_270

namespace Cuts

variable {α : Type} [DecidableEq α]

-- The ordinary circuit may consult any earlier result.
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, ∃ z ∈ ops a b, build ops goal k (insert z available)

-- A live set contains just the wires actually read by the remaining computation.
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k+1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

-- Any pair of rows which the output separates must stay separated at each cut.
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

end Cuts

open PEqualNP.CircuitLowerBounds

abbrev F (n : ℕ) := (Fin n → Bool) → Bool

def mono {n : ℕ} (f : F n) : Prop :=
  ∀ x y, (∀ p, x p = true → y p = true) → f x = true → f y = true

def single {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def support {n : ℕ} (f : F n) : Finset (Fin n) :=
  Finset.univ.filter fun p => f (single p) = true

def isPrivate {n : ℕ} (S : Finset (Fin n)) (f : F n) : Prop :=
  support f ⊆ S ∧ 2 ≤ (support f).card

def zeroF {n : ℕ} : F n := fun _ => false

def andF {n : ℕ} (a b : F n) : F n := fun x => a x && b x
def orF {n : ℕ} (a b : F n) : F n := fun x => a x || b x

noncomputable def ops {n : ℕ} (a b : F n) : Finset (F n) := by
  classical
  exact {andF a b, orF a b}

noncomputable def free {n : ℕ} (S : Finset (Fin n)) : Finset (F n) := by
  classical
  exact Finset.univ.filter fun f => mono f ∧ ¬ isPrivate S f

theorem zero_free {n : ℕ} (S : Finset (Fin n)) : zeroF ∈ free S := by
  classical
  simp [free, mono, zeroF, isPrivate, support]

theorem input_free {n : ℕ} (S : Finset (Fin n)) (p : Fin n) :
    (fun x : Fin n → Bool => x p) ∈ free S := by
  classical
  have hs : support (fun x : Fin n → Bool => x p) = {p} := by
    ext q
    simp [support, single, eq_comm]
  simp only [free, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun x y h hx => h p hx, by simp [isPrivate, hs]⟩

def gateF {n : ℕ} (L : List (F n)) (g : Gate) : F n :=
  fun x => g.op.eval (g.inputs.map fun j => (L.getD j zeroF) x)

def run {n : ℕ} : List Gate → List (F n) → List (F n)
  | [], L => L
  | g :: gs, L => run gs (L ++ [gateF L g])

noncomputable def cost {n : ℕ} (S : Finset (Fin n)) : List Gate → List (F n) → ℕ := by
  classical
  exact fun gs L => match gs with
    | [] => 0
    | g :: rest => (if isPrivate S (gateF L g) then 1 else 0) + cost S rest (L ++ [gateF L g])

def good (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem getD_mono {n : ℕ} (L : List (F n))
    (hL : ∀ f ∈ L, mono f) (j : ℕ) : mono (L.getD j zeroF) := by
  by_cases h : j < L.length
  · apply hL
    simp only [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · rw [List.getD_eq_default L zeroF (by omega)]
    simp [mono, zeroF]

theorem gate_mono {n : ℕ} (L : List (F n)) (g : Gate)
    (hL : ∀ f ∈ L, mono f) (hg : good g) : mono (gateF L g) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hg.2
  have ha := getD_mono L hL a
  have hb := getD_mono L hL b
  intro x y hxy hx
  rcases hg.1 with hop | hop
  · simp only [gateF, hab, hop, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hx ⊢
    exact ⟨ha x y hxy hx.1, hb x y hxy hx.2⟩
  · simp only [gateF, hab, hop, List.map_cons, List.map_nil, GateOp.eval,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hx ⊢
    exact hx.elim (fun h => Or.inl (ha x y hxy h)) (fun h => Or.inr (hb x y hxy h))

theorem run_build {n : ℕ} (S : Finset (Fin n)) (goal : F n)
    (gs : List Gate) : ∀ (L : List (F n)) (A : Finset (F n)),
    free S ⊆ A → (∀ f ∈ L, f ∈ A) → (∀ f ∈ L, mono f) →
    (∀ g ∈ gs, good g) →
    (goal ∈ run gs L ∨ goal = zeroF) → Cuts.build ops goal (cost S gs L) A := by
  classical
  induction gs with
  | nil =>
    intro L A hA hL hm hg ht
    rcases ht with ht | rfl
    · exact hL goal ht
    · exact hA (zero_free S)
  | cons g gs ih =>
    intro L A hA hL hm hg ht
    have hgood := hg g (by simp)
    have hzmono := gate_mono L g hm hgood
    have hgs : ∀ g ∈ gs, good g := fun g h => hg g (by simp [h])
    have hm' : ∀ f ∈ L ++ [gateF L g], mono f := by
      intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hm f hf
      · simpa using (List.mem_singleton.mp hf) ▸ hzmono
    by_cases hp : isPrivate S (gateF L g)
    · obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hgood.2
      have hav (j : ℕ) : L.getD j zeroF ∈ A := by
        by_cases hj : j < L.length
        · apply hL
          simp only [List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem hj
        · rw [List.getD_eq_default L zeroF (by omega)]
          exact hA (zero_free S)
      have hz : gateF L g ∈ ops (L.getD a zeroF) (L.getD b zeroF) := by
        rcases hgood.1 with hop | hop
        · apply Finset.mem_insert.mpr
          left
          funext x
          simp [gateF, hab, hop, GateOp.eval, andF]
        · apply Finset.mem_insert.mpr
          right
          apply Finset.mem_singleton.mpr
          funext x
          simp [gateF, hab, hop, GateOp.eval, orF]
      have htail := ih (L ++ [gateF L g]) (insert (gateF L g) A)
        (fun f hf => Finset.mem_insert_of_mem (hA hf))
        (by
          intro f hf
          rcases List.mem_append.mp hf with hf | hf
          · exact Finset.mem_insert_of_mem (hL f hf)
          · simp_all)
        hm' hgs ht
      simp only [cost, ite_eq_left hp, Nat.one_add]
      exact Or.inr ⟨L.getD a zeroF, hav a, L.getD b zeroF, hav b, gateF L g, hz, htail⟩
    · have hz : gateF L g ∈ A := hA (by simp [free, hzmono, hp])
      have htail := ih (L ++ [gateF L g]) A hA
        (by
          intro f hf
          rcases List.mem_append.mp hf with hf | hf
          · exact hL f hf
          · simpa using (List.mem_singleton.mp hf) ▸ hz)
        hm' hgs ht
      simpa only [cost, ite_eq_right hp, Nat.zero_add] using htail

theorem cut_bound {n k c : ℕ} (S : Finset (Fin n)) (goal : F n) (p : ℕ)
    (hbuild : Cuts.build ops goal p (free S))
    (hsingle : ∀ q, goal (single q) = true ↔ q ∈ S)
    (havoid : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun q => x q = true).card ≤ k →
      (∀ q ∈ S, x q = false) → goal x = false)
    (hck : c ≤ k) (hcs : c + 1 ≤ S.card) : c ≤ p := by
  classical
  by_contra hcp
  obtain ⟨s, hs, hrun⟩ := Cuts.compress hbuild
  have hcard : s.card ≤ c := (Cuts.live_card hrun).trans (by omega)
  have hfree (f : F n) (hf : f ∈ s) : mono f ∧ ¬ isPrivate S f := by
    simpa only [free, Finset.mem_filter, Finset.mem_univ, true_and] using hs hf
  let R (f : F n) : Finset (Fin n) :=
    if h : support f ⊆ S then support f
    else {Classical.choose (Finset.not_subset.mp h)}
  let T := s.biUnion R
  have hR (f : F n) (hf : f ∈ s) : (R f).card ≤ 1 := by
    dsimp [R]
    split
    · have := (hfree f hf).2
      simp only [isPrivate, not_and] at this
      have := this (by assumption)
      omega
    · simp
  have hT : T.card ≤ c := by
    calc
      T.card ≤ ∑ f ∈ s, (R f).card := Finset.card_biUnion_le
      _ ≤ ∑ _f ∈ s, 1 := Finset.sum_le_sum hR
      _ = s.card := by simp
      _ ≤ c := hcard
  obtain ⟨q, hqS, hqT⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := T) (t := S) (by omega)
  let x : Fin n → Bool := fun r => decide (r ∈ T ∧ r ∉ S)
  have hxsize : (Finset.univ.filter fun r => x r = true).card ≤ k := by
    apply (Finset.card_le_card (show (Finset.univ.filter fun r => x r = true) ⊆ T from ?_)).trans
      (hT.trans hck)
    intro r hr
    exact (of_decide_eq_true (Finset.mem_filter.mp hr).2).1
  have hxzero : ∀ r ∈ S, x r = false := by
    intro r hr
    simp [x, hr]
  let D (f : F n) : Prop := f (single q) = true ∧ f x = false
  have hd : D goal := ⟨(hsingle q).mpr hqS, havoid x hxsize hxzero⟩
  have hops : ∀ a b : F n, ∀ z ∈ ops a b, D z → D a ∨ D b := by
    intro a b z hz hd
    simp only [ops, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;>
      cases ha : a (single q) <;> cases hb : b (single q) <;>
      cases ha' : a x <;> cases hb' : b x <;>
      simp_all [D, andF, orF]
  obtain ⟨f, hf, hD⟩ := Cuts.live_separates D hd hops hrun
  by_cases hsub : support f ⊆ S
  · apply hqT
    apply Finset.mem_biUnion.mpr
    refine ⟨f, hf, ?_⟩
    dsimp only [R]
    rw [dite_eq_left hsub]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD.1⟩
  · let r := Classical.choose (Finset.not_subset.mp hsub)
    have hr : r ∈ support f ∧ r ∉ S := Classical.choose_spec (Finset.not_subset.mp hsub)
    have hrT : r ∈ T := Finset.mem_biUnion.mpr ⟨f, hf, by simp [R, hsub, r]⟩
    have hfx : f x = true := (hfree f hf).1 (single r) x
      (by
        intro t ht
        have ht' : t = r := by simpa [single] using ht
        subst t
        simp [x, hrT, hr.2])
      (by simpa [support] using hr.1)
    exact Bool.noConfusion (hfx.symm.trans hD.2)

theorem map_getD' {α β : Type} (L : List α) (φ : α → β) (j : ℕ) (d : α) :
    (L.map φ).getD j (φ d) = φ (L.getD j d) := by
  induction L generalizing j with
  | nil => simp
  | cons a L ih => cases j <;> simp [ih]

theorem run_eval {n : ℕ} (gs : List Gate) (L : List (F n)) (x : Fin n → Bool) :
    (run gs L).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
        (L.map fun f => f x) := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih =>
    have hstep : gateF L g x =
        g.op.eval (g.inputs.map fun j => (L.map fun f => f x).getD j false) := by
      unfold gateF
      congr 1
      apply List.map_congr_left
      intro j hj
      exact (map_getD' L (fun f => f x) j zeroF).symm
    simp only [run, ih, List.map_append, List.map_singleton, List.foldl_cons, hstep]

def inputsF (n : ℕ) : List (F n) := List.ofFn fun p : Fin n => fun x => x p

theorem run_circuit {n : ℕ} (C : Circuit) (o : ℕ) (x : Fin n → Bool) :
    ((run C.gates (inputsF n)).getD o zeroF) x = (C.wires (List.ofFn x)).getD o false := by
  rw [← map_getD' (run C.gates (inputsF n)) (fun f => f x) o zeroF, run_eval]
  simp [Circuit.wires, inputsF, List.map_ofFn, zeroF, Function.comp_def]

theorem output_cost {n k c o : ℕ} (S : Finset (Fin n)) (C : Circuit)
    (hg : ∀ g ∈ C.gates, good g)
    (hsingle : ∀ p : Fin n, (C.wires (List.ofFn (single p))).getD o false = true ↔ p ∈ S)
    (havoid : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun q => x q = true).card ≤ k →
      (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD o false = false)
    (hck : c ≤ k) (hcs : c + 1 ≤ S.card) : c ≤ cost S C.gates (inputsF n) := by
  classical
  let goal := (run C.gates (inputsF n)).getD o zeroF
  have hgoal : goal ∈ run C.gates (inputsF n) ∨ goal = zeroF := by
    by_cases h : o < (run C.gates (inputsF n)).length
    · left
      dsimp [goal]
      rw [List.getD_eq_getElem _ _ h]
      exact List.getElem_mem h
    · right
      exact List.getD_eq_default _ _ (by omega)
  have hb : Cuts.build ops goal (cost S C.gates (inputsF n)) (free S) :=
    run_build S goal C.gates (inputsF n) (free S) (fun _ h => h)
      (by
        intro f hf
        obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hf
        exact input_free S p)
      (by
        intro f hf
        obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hf
        exact fun x y h hx => h p hx)
      hg hgoal
  apply cut_bound S goal _ hb _ _ hck hcs
  · intro p
    simpa only [goal, run_circuit] using hsingle p
  · intro x hx hz
    simpa only [goal, run_circuit] using havoid x hx hz

theorem private_unique {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (f : F n) {i j : Fin m} (hi : isPrivate (S i) f) (hj : isPrivate (S j) f) : i = j := by
  by_contra hij
  have hh : support f ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi.1 hp, hj.1 hp⟩
  have hcard := Finset.card_le_card hh
  have hsmall := hS i j hij
  have := hi.2
  omega

theorem sum_cost {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) : ∀ L : List (F n), ∑ i : Fin m, cost (S i) gs L ≤ gs.length := by
  classical
  induction gs with
  | nil => intro L; simp [cost]
  | cons g gs ih =>
    intro L
    have hhead : (∑ i : Fin m, if isPrivate (S i) (gateF L g) then 1 else 0) ≤ 1 := by
      let T := Finset.univ.filter fun i : Fin m => isPrivate (S i) (gateF L g)
      have hT : T.card ≤ 1 := Finset.card_le_one.mpr (by
        intro i hi j hj
        exact private_unique S hS _ (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
      simpa only [T, Finset.sum_boole, Nat.cast_id] using hT
    simp only [cost, Finset.sum_add_distrib, List.length_cons]
    have htail := ih (L ++ [gateF L g])
    omega

end PEqualNP.Outside.L_meta_270



theorem PEqualNP.Outside.L_meta_270 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS hcard hg hs ha hck hcs
  apply (Finset.sum_le_sum (fun i _ =>
    PEqualNP.Outside.L_meta_270.output_cost (S i) C hg (hs i) (ha i) (hck i) (hcs i))).trans
  exact PEqualNP.Outside.L_meta_270.sum_cost S hS C.gates _
