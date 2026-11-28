import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1455_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

lemma wires_append_gate (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x =
      Circuit.wires ⟨gs, 0⟩ x ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rcases C with ⟨gs, o⟩
  simp only [Circuit.wires]
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma wires_prefix (gs1 gs2 : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs1.length) :
    (Circuit.wires ⟨gs1 ++ gs2, 0⟩ x).getD i false =
      (Circuit.wires ⟨gs1, 0⟩ x).getD i false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, wires_append_gate]
    have hlen : (Circuit.wires ⟨gs1 ++ gs2, 0⟩ x).length = x.length + (gs1 ++ gs2).length :=
      wires_length ⟨gs1 ++ gs2, 0⟩ x
    have hi2 : i < (Circuit.wires ⟨gs1 ++ gs2, 0⟩ x).length := by
      rw [hlen, List.length_append]; omega
    rw [List.getD_append _ _ _ _ hi2]
    exact ih

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  have h := wires_prefix [] C.gates x i (by simpa using hi)
  simpa [Circuit.wires] using h

lemma wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i =>
          (Circuit.wires ⟨C.gates.take j, 0⟩ x).getD i false) := by
  have hsplit : C.gates = (C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1) := by
    rw [← List.take_succ_eq_append_getElem hj, List.take_append_drop]
  have hlen : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have h1 : (C.wires x).getD (x.length + j) false =
      (Circuit.wires ⟨C.gates.take j ++ [C.gates[j]], 0⟩ x).getD (x.length + j) false := by
    have hp := wires_prefix (C.gates.take j ++ [C.gates[j]]) (C.gates.drop (j + 1)) x
      (x.length + j) (by simp only [List.length_append, List.length_singleton, hlen]; omega)
    simpa only [Circuit.wires, ← hsplit] using hp
  rw [h1, wires_append_gate]
  have hwlen : (Circuit.wires ⟨C.gates.take j, 0⟩ x).length = x.length + j := by
    rw [wires_length, hlen]
  rw [List.getD_append_right _ _ _ _ (by omega), hwlen, Nat.sub_self]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate]
  rfl

lemma wires_getD_gate_rb (C : Circuit) (x : List Bool) (hRB : ReadsBack x.length C)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  rw [wires_getD_gate C x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < x.length + j := hRB j hj i hi
  have hlen : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  have hp := wires_prefix (C.gates.take j) (C.gates.drop j) x i (by omega)
  simpa only [Circuit.wires, ← hsplit] using hp.symm

lemma wires_append (gs1 gs2 : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs1 ++ gs2, o⟩ x = Circuit.wires ⟨gs2, 0⟩ (Circuit.wires ⟨gs1, 0⟩ x) := by
  simp [Circuit.wires, List.foldl_append]

def bitsOf {k : ℕ} (Y : Finset (Fin k)) : List Bool :=
  List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false, true]

lemma bitsOf_length {k : ℕ} (Y : Finset (Fin k)) : (bitsOf Y).length = k + 2 := by
  simp [bitsOf]

lemma bitsOf_getD_lt {k : ℕ} (Y : Finset (Fin k)) (w : ℕ) (hw : w < k) :
    (bitsOf Y).getD w false = decide (⟨w, hw⟩ ∈ Y) := by
  unfold bitsOf
  rw [List.getD_append _ _ _ _ (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

lemma bitsOf_getD_k {k : ℕ} (Y : Finset (Fin k)) : (bitsOf Y).getD k false = false := by
  unfold bitsOf
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma bitsOf_getD_k1 {k : ℕ} (Y : Finset (Fin k)) : (bitsOf Y).getD (k + 1) false = true := by
  unfold bitsOf
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma poset_minimal {n : ℕ} (R : Fin n → Fin n → Prop)
    (hTrans : ∀ i j h, R i j → R j h → R i h)
    (hAnti : ∀ i j, R i j → R j i → i = j)
    (T : Finset (Fin n)) (hT : T.Nonempty) :
    ∃ i ∈ T, ∀ j ∈ T, R j i → j = i := by
  classical
  induction hcard : T.card generalizing T with
  | zero => exact absurd (Finset.card_eq_zero.mp hcard) hT.ne_empty
  | succ m ih =>
    obtain ⟨x, hx⟩ := hT
    by_cases hmin : ∀ j ∈ T, R j x → j = x
    · exact ⟨x, hx, hmin⟩
    · push_neg at hmin
      let T' := T.erase x
      have hT'card : T'.card = m := by
        rw [Finset.card_erase_of_mem hx, hcard]; rfl
      obtain ⟨y, hyT, hyx, hyne⟩ := hmin
      have hT'ne : T'.Nonempty := ⟨y, Finset.mem_erase.mpr ⟨hyne, hyT⟩⟩
      obtain ⟨i, hiT', himin⟩ := ih T' hT'ne hT'card
      have hiT : i ∈ T := Finset.mem_of_mem_erase hiT'
      refine ⟨i, hiT, fun j hjT hji => ?_⟩
      by_cases hjx : j = x
      · rw [hjx] at hji
        have hyi : R y i := hTrans y x i hyx hji
        have hy_eq_i : y = i := himin y (Finset.mem_erase.mpr ⟨hyne, hyT⟩) hyi
        rw [← hy_eq_i] at hji
        exact absurd (hAnti y x hyx hji) hyne
      · exact himin j (Finset.mem_erase.mpr ⟨hjx, hjT⟩) hji

lemma lower_step_general {k a f : ℕ} (D : Circuit)
    (gA gA' : Finset (Fin k)) (hsub : gA ⊆ gA')
    (hrecA : ∀ Y : Finset (Fin k), (gA \ Y).card ≤ a → (Y \ gA).card ≤ f →
      (D.wires (bitsOf Y)).getD D.output false = false)
    (hrecA' : ∀ Y : Finset (Fin k), (gA' \ Y).card ≤ a → (Y \ gA').card ≤ f →
      (D.wires (bitsOf Y)).getD D.output false = true) :
    a + f + 1 ≤ (gA' \ gA).card := by
  by_contra hlt
  push_neg at hlt
  let Δ := gA' \ gA
  have hΔ : Δ.card ≤ a + f := Nat.le_of_lt_succ hlt
  obtain ⟨V, hVsub, hVcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_right f Δ.card)
  let Y := gA ∪ V
  have h1 : (gA \ Y).card ≤ a := by
    have : gA \ Y = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_left
    simp [this]
  have h2 : (Y \ gA).card ≤ f := by
    have : Y \ gA ⊆ V := by
      intro x hx; simp only [Y, Finset.mem_sdiff, Finset.mem_union] at hx
      rcases hx with ⟨h | h, hn⟩
      · exact absurd h hn
      · exact h
    exact (Finset.card_le_card this).trans (by rw [hVcard]; exact Nat.min_le_left _ _)
  have h3 : (Y \ gA').card ≤ f := by
    have hYsub : Y ⊆ gA' := Finset.union_subset hsub (hVsub.trans Finset.sdiff_subset)
    have : Y \ gA' = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hYsub
    simp [this]
  have h4 : (gA' \ Y).card ≤ a := by
    have heq : gA' \ Y = Δ \ V := by
      ext x; simp only [Y, Δ, Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [heq, Finset.card_sdiff_of_subset hVsub, hVcard]
    have : Δ.card - min f Δ.card ≤ a := by
      rcases le_total f Δ.card with hle | hle
      · rw [min_eq_left hle]; omega
      · rw [min_eq_right hle]; omega
    exact this
  have hf := hrecA Y h1 h2
  have ht := hrecA' Y h4 h3
  rw [hf] at ht
  simp at ht

def dpRowAux (k w : ℕ) (prev : List ℕ) (base : ℕ) : ℕ → List Gate × List ℕ
  | 0 => ([], [k + 1])
  | r + 1 =>
    let sub := dpRowAux k w prev base r
    let cur := base + sub.1.length
    let gAnd : Gate := ⟨.and, [w, prev.getD r (k + 1)]⟩
    let gOr : Gate := ⟨.or, [prev.getD (r + 1) k, cur]⟩
    (sub.1 ++ [gAnd, gOr], sub.2 ++ [cur + 1])

def dpBuild (k off f : ℕ) : ℕ → List Gate × List ℕ
  | 0 => ([], (k + 1) :: List.replicate (f + 1) k)
  | m + 1 =>
    let prev := dpBuild k off f m
    let cur := dpRowAux k (off + m) prev.2 (k + 2 + prev.1.length) (f + 1)
    (prev.1 ++ cur.1, cur.2)

def buildThresh (k off t f : ℕ) : Circuit :=
  let res := dpBuild k off f t
  ⟨res.1, res.2.getD (f + 1) k⟩

lemma dpRowAux_spec (k w : ℕ) (prev : List ℕ) (base : ℕ)
    (hw : w < base) (hprev : ∀ r ≤ f + 1, prev.getD r k < base)
    (hprev0 : prev.getD 0 (k + 1) < base) (hk1 : k + 1 < base) :
    ∀ r ≤ f + 1,
      let res := dpRowAux k w prev base r
      res.1.length = 2 * r ∧
      res.2.length = r + 1 ∧
      (∀ g ∈ res.1, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧
      (∀ j < res.1.length, ∀ i ∈ (res.1.getD j ⟨.or, []⟩).inputs, i < base + j) ∧
      (∀ s ≤ r, res.2.getD s k < base + res.1.length) ∧
      res.2.getD 0 (k + 1) = k + 1 := by
  intro r
  induction r with
  | zero =>
    intro _
    unfold dpRowAux
    refine ⟨by simp, by simp, by simp, by simp, ?_, rfl⟩
    intro s hs
    have : s = 0 := by omega
    subst this; simpa using hk1
  | succ r ih =>
    intro hr
    obtain ⟨hlenG, hlenR, hgG, hrbG, houtR, h0⟩ := ih (by omega)
    unfold dpRowAux
    set sub := dpRowAux k w prev base r
    set cur := base + sub.1.length
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hlenG]; omega
    · simp only [List.length_append, List.length_singleton, hlenR]
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
      rcases hg with h | rfl | rfl
      · exact hgG g h
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr rfl, rfl⟩
    · intro j hj i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      by_cases hlt : j < sub.1.length
      · rw [List.getD_append _ _ _ _ hlt] at hi
        exact hrbG j hlt i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        have hcase : j - sub.1.length = 0 ∨ j - sub.1.length = 1 := by omega
        rcases hcase with h0' | h1'
        · rw [h0', List.getD_cons_zero] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · omega
          · cases r with
            | zero => omega
            | succ r' =>
              have hltp : prev.getD (r' + 1) (k + 1) < base := by
                by_cases hlenP : r' + 1 < prev.length
                · have heq : prev.getD (r' + 1) (k + 1) = prev.getD (r' + 1) k := by
                    simp [List.getD_eq_getElem?_getD, hlenP]
                  rw [heq]; exact hprev (r' + 1) (by omega)
                · rw [List.getD_eq_default _ _ (by omega)]; exact hk1
              omega
        · rw [h1', List.getD_cons_succ, List.getD_cons_zero] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · have := hprev (r + 1) hr; omega
          · omega
    · intro s hs
      simp only [List.length_append, List.length_cons, List.length_nil]
      by_cases hslt : s < sub.2.length
      · rw [List.getD_append _ _ _ _ hslt]
        have := houtR s (by omega); omega
      · have hseq : s = sub.2.length := by omega
        rw [hseq, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
        omega
    · rw [List.getD_append _ _ _ _ (by rw [hlenR]; omega)]
      exact h0

lemma dpRowAux_eval (k w : ℕ) (prev : List ℕ) (init : List Bool) (hw : w < init.length)
    (hk : k < init.length) (hk1 : k + 1 < init.length)
    (hinit_k : init.getD k false = false) (hinit_k1 : init.getD (k + 1) false = true)
    (f : ℕ) (hprev_len : prev.length = f + 2)
    (hprev_lt : ∀ r ≤ f + 1, prev.getD r k < init.length) :
    ∀ r ≤ f + 1, ∀ s ≤ r,
        (Circuit.wires ⟨(dpRowAux k w prev init.length r).1, 0⟩ init).getD ((dpRowAux k w prev init.length r).2.getD s k) false =
          if s = 0 then true
          else (init.getD (prev.getD s k) false ||
                (init.getD w false && init.getD (prev.getD (s - 1) k) false)) := by
  intro r
  induction r with
  | zero =>
    intro _ s hs
    have h0 : s = 0 := by omega
    subst h0
    simp only [dpRowAux, Circuit.wires, List.foldl_nil, List.getD_cons_zero, ite_true]
    exact hinit_k1
  | succ r ih =>
    intro hr s hs
    have hspec := dpRowAux_spec (f := f) k w prev init.length hw hprev_lt
      (by
        have h0p : 0 < prev.length := by omega
        have heq : prev.getD 0 (k + 1) = prev.getD 0 k := by simp [List.getD_eq_getElem?_getD, h0p]
        rw [heq]; exact hprev_lt 0 (by omega))
      hk1 r (by omega)
    simp only [dpRowAux]
    set sub := dpRowAux k w prev init.length r
    set cur := init.length + sub.1.length
    set gAnd : Gate := ⟨.and, [w, prev.getD r (k + 1)]⟩
    set gOr : Gate := ⟨.or, [prev.getD (r + 1) k, cur]⟩
    by_cases hslt : s < sub.2.length
    · rw [List.getD_append _ _ _ _ hslt]
      have hout : sub.2.getD s k < init.length + sub.1.length := hspec.2.2.2.2.1 s (by omega)
      rw [wires_prefix sub.1 [gAnd, gOr] init _ hout]
      exact ih (by omega) s (by omega)
    · have hseq : s = r + 1 := by omega
      subst hseq
      rw [List.getD_append_right _ _ _ _ (by rw [hspec.2.1]), hspec.2.1, Nat.sub_self, List.getD_cons_zero]
      have hfold : sub.1 ++ [gAnd, gOr] = (sub.1 ++ [gAnd]) ++ [gOr] := by simp
      rw [hfold, wires_append_gate]
      have hlen1 : (Circuit.wires ⟨sub.1 ++ [gAnd], 0⟩ init).length = cur + 1 := by
        rw [wires_length, List.length_append, List.length_singleton]; omega
      rw [List.getD_append_right _ _ _ _ (by omega), hlen1, Nat.sub_self, List.getD_cons_zero]
      have hcur_val : (Circuit.wires ⟨sub.1 ++ [gAnd], 0⟩ init).getD cur false =
          (init.getD w false && init.getD (prev.getD r k) false) := by
        rw [wires_append_gate]
        have hlen0 : (Circuit.wires ⟨sub.1, 0⟩ init).length = cur := by rw [wires_length]
        rw [List.getD_append_right _ _ _ _ (by omega), hlen0, Nat.sub_self, List.getD_cons_zero]
        have hw0 : (Circuit.wires ⟨sub.1, 0⟩ init).getD w false = init.getD w false :=
          wires_getD_input ⟨sub.1, 0⟩ init w hw
        have hpr_eq : prev.getD r (k + 1) = prev.getD r k := by
          simp [List.getD_eq_getElem?_getD, show r < prev.length by omega]
        have hp0 : (Circuit.wires ⟨sub.1, 0⟩ init).getD (prev.getD r (k + 1)) false =
            init.getD (prev.getD r k) false := by
          rw [hpr_eq]
          exact wires_getD_input ⟨sub.1, 0⟩ init _ (hprev_lt r (by omega))
        simp only [gAnd, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw0, hp0]
      have hp1 : (Circuit.wires ⟨sub.1 ++ [gAnd], 0⟩ init).getD (prev.getD (r + 1) k) false =
          init.getD (prev.getD (r + 1) k) false :=
        wires_getD_input ⟨sub.1 ++ [gAnd], 0⟩ init _ (hprev_lt (r + 1) hr)
      simp only [gOr, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hcur_val, hp1, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]

lemma dpBuild_spec (k off f : ℕ) :
    ∀ m : ℕ, off + m ≤ k →
      let res := dpBuild k off f m
      res.1.length = 2 * m * (f + 1) ∧
      res.2.length = f + 2 ∧
      (∀ g ∈ res.1, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧
      (∀ j < res.1.length, ∀ i ∈ (res.1.getD j ⟨.or, []⟩).inputs, i < k + 2 + j) ∧
      (∀ r ≤ f + 1, res.2.getD r k < k + 2 + res.1.length) ∧
      res.2.getD 0 (k + 1) = k + 1 := by
  intro m
  induction m with
  | zero =>
    intro _
    dsimp only [dpBuild]
    refine ⟨by simp, by simp, by simp, by simp, ?_, rfl⟩
    intro r _
    cases r with
    | zero => simp
    | succ r' =>
      by_cases hlt : r' < f + 1
      · simp [List.getD_eq_getElem?_getD, hlt]
      · simp [List.getD_eq_getElem?_getD, hlt]
  | succ m ih =>
    intro hoff
    obtain ⟨hlenG, hlenR, hgG, hrbG, houtR, h0⟩ := ih (by omega)
    simp only [dpBuild]
    set prev := dpBuild k off f m
    have hrow := dpRowAux_spec (f := f) k (off + m) prev.2 (k + 2 + prev.1.length)
      (by omega) houtR (by rw [h0]; omega) (by omega) (f + 1) le_rfl
    set cur := dpRowAux k (off + m) prev.2 (k + 2 + prev.1.length) (f + 1)
    have hcur1 : cur.1.length = 2 * (f + 1) := hrow.1
    refine ⟨?_, hrow.2.1, ?_, ?_, ?_, hrow.2.2.2.2.2⟩
    · rw [List.length_append, hlenG, hcur1]; ring
    · intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hgG g h1
      · exact hrow.2.2.1 g h2
    · intro j hj i hi
      simp only [List.length_append] at hj
      by_cases hlt : j < prev.1.length
      · rw [List.getD_append _ _ _ _ hlt] at hi
        exact hrbG j hlt i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        have := hrow.2.2.2.1 (j - prev.1.length) (by omega) i hi
        omega
    · intro r hr
      simp only [List.length_append]
      have := hrow.2.2.2.2.1 r hr
      omega

lemma dpBuild_eval (k off f : ℕ) (Y : Finset (Fin k)) :
    ∀ m : ℕ, off + m ≤ k →
      ∀ r ≤ f + 1,
        (Circuit.wires ⟨(dpBuild k off f m).1, 0⟩ (bitsOf Y)).getD ((dpBuild k off f m).2.getD r k) false =
          decide (r ≤ ((Finset.range m).filter fun j =>
            ∃ hlt : off + j < k, (⟨off + j, hlt⟩ : Fin k) ∈ Y).card) := by
  intro m
  induction m with
  | zero =>
    intro _ r hr
    simp only [dpBuild, Circuit.wires, List.foldl_nil, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty]
    cases r with
    | zero =>
      simp only [List.getD_cons_zero, Nat.zero_le, decide_true]
      exact bitsOf_getD_k1 Y
    | succ r' =>
      have hlt : r' < f + 1 := by omega
      simp only [List.getD_cons_succ, List.getD_replicate, hlt, ite_true, Nat.not_succ_le_zero, decide_false]
      exact bitsOf_getD_k Y
  | succ m ih =>
    intro hoff r hr
    have hprev_spec := dpBuild_spec k off f m (by omega)
    simp only [dpBuild]
    set prev := dpBuild k off f m
    set cur := dpRowAux k (off + m) prev.2 (k + 2 + prev.1.length) (f + 1)
    rw [wires_append]
    have hbase_len : (Circuit.wires ⟨prev.1, 0⟩ (bitsOf Y)).length = k + 2 + prev.1.length := by
      rw [wires_length, bitsOf_length]
    have hev := dpRowAux_eval k (off + m) prev.2 (Circuit.wires ⟨prev.1, 0⟩ (bitsOf Y))
      (by rw [hbase_len]; omega) (by rw [hbase_len]; omega) (by rw [hbase_len]; omega)
      (by rw [wires_getD_input _ _ k (by rw [bitsOf_length]; omega), bitsOf_getD_k])
      (by rw [wires_getD_input _ _ (k + 1) (by rw [bitsOf_length]; omega), bitsOf_getD_k1])
      f hprev_spec.2.1
      (fun s hs => by rw [hbase_len]; exact hprev_spec.2.2.2.2.1 s hs)
      (f + 1) le_rfl r hr
    rw [hbase_len] at hev
    rw [hev]
    have hfilt : ((Finset.range (m + 1)).filter fun j =>
        ∃ hlt : off + j < k, (⟨off + j, hlt⟩ : Fin k) ∈ Y).card =
        ((Finset.range m).filter fun j =>
          ∃ hlt : off + j < k, (⟨off + j, hlt⟩ : Fin k) ∈ Y).card +
        (if (⟨off + m, by omega⟩ : Fin k) ∈ Y then 1 else 0) := by
      rw [Finset.range_add_one, Finset.filter_insert]
      have hnm : m ∉ (Finset.range m).filter (fun j => ∃ hlt : off + j < k, (⟨off + j, hlt⟩ : Fin k) ∈ Y) := by
        simp
      by_cases hmY : (⟨off + m, by omega⟩ : Fin k) ∈ Y
      · have hlt_m : off + m < k := by omega
        have hex : ∃ hlt : off + m < k, (⟨off + m, hlt⟩ : Fin k) ∈ Y := ⟨hlt_m, hmY⟩
        rw [if_pos hex, if_pos hmY]
        exact Finset.card_insert_of_notMem hnm
      · have hnex : ¬ ∃ hlt : off + m < k, (⟨off + m, hlt⟩ : Fin k) ∈ Y := by
          rintro ⟨_, h⟩; exact hmY h
        rw [if_neg hnex, if_neg hmY, Nat.add_zero]
    rw [hfilt]
    cases r with
    | zero => simp
    | succ r' =>
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
      have hw_val : (Circuit.wires ⟨prev.1, 0⟩ (bitsOf Y)).getD (off + m) false =
          decide ((⟨off + m, by omega⟩ : Fin k) ∈ Y) := by
        rw [wires_getD_input _ _ (off + m) (by rw [bitsOf_length]; omega), bitsOf_getD_lt Y _ (by omega)]
      rw [hw_val, ih (by omega) (r' + 1) hr, ih (by omega) r' (by omega)]
      by_cases hmY : (⟨off + m, by omega⟩ : Fin k) ∈ Y
      · simp only [hmY, decide_true, Bool.true_and, ite_true]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega
      · simp only [hmY, decide_false, Bool.false_and, Bool.or_false, ite_false, Nat.add_zero]

lemma buildThresh_spec (k off t f : ℕ) (hoff : off + t ≤ k) (hft : f + 1 ≤ t) :
    let D := buildThresh k off t f
    FanInTwo D ∧
    ReadsBack (k + 2) D ∧
    D.output < k + 2 + D.size ∧
    notCount D = 0 ∧
    D.size ≤ 2 * (t + 1) ^ 2 ∧
    ∀ Y : Finset (Fin k),
      (D.wires (bitsOf Y)).getD D.output false =
        decide (f + 1 ≤ ((Finset.range t).filter fun j =>
          ∃ hlt : off + j < k, (⟨off + j, hlt⟩ : Fin k) ∈ Y).card) := by
  have hdp := dpBuild_spec k off f t hoff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hop, hlen⟩ := hdp.2.2.1 g hg
    refine ⟨?_, by omega⟩
    rcases hop with h | h <;> simp [h]
  · intro j hj i hi
    exact hdp.2.2.2.1 j hj i hi
  · exact hdp.2.2.2.2.1 (f + 1) le_rfl
  · unfold notCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro g hg
    rcases (hdp.2.2.1 g hg).1 with h | h <;> simp [h]
  · simp only [buildThresh, Circuit.size, hdp.1]
    have : 2 * t * (f + 1) ≤ 2 * (t + 1) * (t + 1) := by
      have h1 : t ≤ t + 1 := Nat.le_succ t
      have h2 : f + 1 ≤ t + 1 := by omega
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
    simpa [sq, Nat.mul_assoc] using this
  · intro Y
    exact dpBuild_eval k off f Y t hoff (f + 1) le_rfl

lemma prefix_sum_offset {n : ℕ} (cost : Fin n → ℕ) (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), cost j) + cost i ≤
      ∑ j : Fin n, cost j := by
  have hmem : i ∉ Finset.univ.filter (fun j : Fin n => j.val < i.val) := by simp
  have hsub : insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) ⊆ Finset.univ :=
    Finset.subset_univ _
  calc (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), cost j) + cost i
      = ∑ j ∈ insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)), cost j := by
        rw [Finset.sum_insert hmem, Nat.add_comm]
    _ ≤ ∑ j : Fin n, cost j := Finset.sum_le_sum_of_subset hsub

lemma prefix_sum_disjoint {n : ℕ} (cost : Fin n → ℕ) (i j : Fin n) (hij : i.val < j.val) :
    (∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val < i.val), cost r) + cost i ≤
      ∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val < j.val), cost r := by
  have hmem : i ∉ Finset.univ.filter (fun r : Fin n => r.val < i.val) := by simp
  have hsub : insert i (Finset.univ.filter (fun r : Fin n => r.val < i.val)) ⊆
      Finset.univ.filter (fun r : Fin n => r.val < j.val) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rcases hr with rfl | hr
    · exact hij
    · omega
  calc (∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val < i.val), cost r) + cost i
      = ∑ r ∈ insert i (Finset.univ.filter (fun r : Fin n => r.val < i.val)), cost r := by
        rw [Finset.sum_insert hmem, Nat.add_comm]
    _ ≤ ∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val < j.val), cost r :=
      Finset.sum_le_sum_of_subset hsub

def delayStep (ts : List ℕ) (g : Gate) : List ℕ :=
  let mx := g.inputs.foldl (fun v j => max v (ts.getD j 0)) 0
  ts ++ [match g.op with
    | .not => (g.inputs.head?.map (fun j => ts.getD j 0)).getD 0
    | _ => mx + 1]

def timesOf (k : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl delayStep (List.replicate (k + 2) 0)

lemma delayStep_eq (ts : List ℕ) (g : Gate) :
    delayStep ts g = ts ++ [match g.op with
      | .not => (g.inputs.head?.map (fun j => ts.getD j 0)).getD 0
      | _ => g.inputs.foldl (fun v j => max v (ts.getD j 0)) 0 + 1] := rfl

lemma delayStep_length (ts : List ℕ) (g : Gate) :
    (delayStep ts g).length = ts.length + 1 := by
  simp [delayStep]

lemma foldl_delayStep_length (gs : List Gate) (ts : List ℕ) :
    (gs.foldl delayStep ts).length = ts.length + gs.length := by
  induction gs generalizing ts with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, delayStep_length]; omega

lemma foldl_delayStep_prefix (gs1 gs2 : List Gate) (ts : List ℕ) (i : ℕ)
    (hi : i < ts.length + gs1.length) :
    ((gs1 ++ gs2).foldl delayStep ts).getD i 0 =
      (gs1.foldl delayStep ts).getD i 0 := by
  rw [List.foldl_append]
  set ts1 := gs1.foldl delayStep ts
  have hlen1 : ts1.length = ts.length + gs1.length := foldl_delayStep_length gs1 ts
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs2.foldl delayStep ts1).length = ts1.length + gs2.length :=
      foldl_delayStep_length gs2 ts1
    rw [delayStep_eq, List.getD_append _ _ _ _ (by omega)]
    exact ih

lemma foldl_delayStep_init (gs : List Gate) (ts : List ℕ) (i : ℕ) (hi : i < ts.length) :
    (gs.foldl delayStep ts).getD i 0 = ts.getD i 0 := by
  have h := foldl_delayStep_prefix [] gs ts i (by simpa using hi)
  simpa using h

lemma timesOf_length (k : ℕ) (gs : List Gate) :
    (timesOf k gs).length = k + 2 + gs.length := by
  unfold timesOf
  rw [foldl_delayStep_length, List.length_replicate]

lemma timesOf_getD_input (k : ℕ) (gs : List Gate) (i : ℕ) (hi : i < k + 2) :
    (timesOf k gs).getD i 0 = 0 := by
  unfold timesOf
  rw [foldl_delayStep_init gs (List.replicate (k + 2) 0) i (by simpa using hi)]
  simp [List.getD_replicate, hi]

lemma timesOf_getD_gate (k : ℕ) (D : Circuit) (j : ℕ) (hj : j < D.gates.length) :
    (timesOf k D.gates).getD (k + 2 + j) 0 =
      let ts := timesOf k (D.gates.take j)
      let g := gateAt D j
      let mx := g.inputs.foldl (fun v i => max v (ts.getD i 0)) 0
      match g.op with
      | .not => (g.inputs.head?.map (fun i => ts.getD i 0)).getD 0
      | _ => mx + 1 := by
  have hsplit : D.gates = (D.gates.take j ++ [D.gates[j]]) ++ D.gates.drop (j + 1) := by
    rw [← List.take_succ_eq_append_getElem hj, List.take_append_drop]
  have hlen : (D.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have h1 : (timesOf k D.gates).getD (k + 2 + j) 0 =
      (timesOf k (D.gates.take j ++ [D.gates[j]])).getD (k + 2 + j) 0 := by
    unfold timesOf
    have hp := foldl_delayStep_prefix (D.gates.take j ++ [D.gates[j]]) (D.gates.drop (j + 1))
      (List.replicate (k + 2) 0) (k + 2 + j)
      (by simp only [List.length_replicate, List.length_append, List.length_singleton, hlen]; omega)
    simpa only [← hsplit] using hp
  rw [h1]
  unfold timesOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have htslen : ((D.gates.take j).foldl delayStep (List.replicate (k + 2) 0)).length = k + 2 + j := by
    rw [foldl_delayStep_length, List.length_replicate, hlen]
  rw [delayStep_eq, List.getD_append_right _ _ _ _ (by omega), htslen, Nat.sub_self, List.getD_cons_zero]
  have hgate : gateAt D j = D.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate]

lemma notCount_zero_ne (D : Circuit) (hNot : notCount D = 0) (g : Gate) (hg : g ∈ D.gates) :
    g.op ≠ GateOp.not := by
  unfold notCount at hNot
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hNot
  have h := hNot g hg
  simpa using h

lemma gate_op_and_or (D : Circuit) (hFit : FanInTwo D) (hNot : notCount D = 0)
    (j : ℕ) (hj : j < D.gates.length) :
    ((gateAt D j).op = .and ∨ (gateAt D j).op = .or) ∧ (gateAt D j).inputs.length ≤ 2 := by
  have hgmem : gateAt D j ∈ D.gates := by
    have : gateAt D j = D.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
    rw [this]; exact List.getElem_mem hj
  have hne : (gateAt D j).op ≠ GateOp.not := notCount_zero_ne D hNot _ hgmem
  obtain ⟨h1, h2⟩ := hFit (gateAt D j) hgmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with ha | ho | hn
  · exact ⟨Or.inl ha, h2⟩
  · exact ⟨Or.inr ho, h2⟩
  · exact absurd hn hne

lemma le_foldl_max_init (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (init : ℕ), init ≤ l.foldl (fun v j => max v (f j)) init
  | [], init => le_rfl
  | a :: l, init =>
    le_trans (le_max_left init (f a)) (le_foldl_max_init f l (max init (f a)))

lemma le_foldl_max_mem (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (init x : ℕ), x ∈ l → f x ≤ l.foldl (fun v j => max v (f j)) init
  | [], _, _, hx => by simp at hx
  | a :: l, init, x, hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hmem
    · exact le_trans (le_max_right init (f x)) (le_foldl_max_init f l (max init (f x)))
    · exact le_foldl_max_mem f l (max init (f a)) x hmem

lemma timesOf_gate_pos (k : ℕ) (D : Circuit) (hFit : FanInTwo D) (hNot : notCount D = 0)
    (j : ℕ) (hj : j < D.gates.length) :
    1 ≤ (timesOf k D.gates).getD (k + 2 + j) 0 := by
  rw [timesOf_getD_gate k D j hj]
  obtain ⟨hop, _⟩ := gate_op_and_or D hFit hNot j hj
  rcases hop with h | h <;> simp [h]

lemma timesOf_gate_input_lt (k : ℕ) (D : Circuit) (hFit : FanInTwo D) (hRB : ReadsBack (k + 2) D)
    (hNot : notCount D = 0) (j : ℕ) (hj : j < D.gates.length) (w' : ℕ)
    (hw' : w' ∈ (gateAt D j).inputs) :
    (timesOf k D.gates).getD w' 0 + 1 ≤ (timesOf k D.gates).getD (k + 2 + j) 0 := by
  rw [timesOf_getD_gate k D j hj]
  obtain ⟨hop, _⟩ := gate_op_and_or D hFit hNot j hj
  have hwlt : w' < k + 2 + j := hRB j hj w' hw'
  have hlen : (D.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hsplit : D.gates = D.gates.take j ++ D.gates.drop j := (List.take_append_drop j D.gates).symm
  have hp : (timesOf k (D.gates.take j)).getD w' 0 = (timesOf k D.gates).getD w' 0 := by
    unfold timesOf
    have h := foldl_delayStep_prefix (D.gates.take j) (D.gates.drop j) (List.replicate (k + 2) 0) w'
      (by rw [List.length_replicate, hlen]; omega)
    simpa only [← hsplit] using h.symm
  have hle := le_foldl_max_mem (fun i => (timesOf k (D.gates.take j)).getD i 0) (gateAt D j).inputs 0 w' hw'
  rw [hp] at hle
  rcases hop with h | h <;> simp only [h] <;> omega

lemma eval_mono (k : ℕ) (D : Circuit) (hFit : FanInTwo D) (hRB : ReadsBack (k + 2) D)
    (hNot : notCount D = 0) (Y1 Y2 : Finset (Fin k)) (hsub : Y1 ⊆ Y2) :
    ∀ w < k + 2 + D.gates.length,
      (D.wires (bitsOf Y1)).getD w false = true →
      (D.wires (bitsOf Y2)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hlt : w < k + 2
    · rw [wires_getD_input _ _ w (by rw [bitsOf_length]; exact hlt)] at htrue ⊢
      by_cases hk : w < k
      · rw [bitsOf_getD_lt _ _ hk] at htrue ⊢
        simp only [decide_eq_true_eq] at htrue ⊢
        exact hsub htrue
      · by_cases heq : w = k
        · subst heq; rw [bitsOf_getD_k] at htrue; simp at htrue
        · have heq1 : w = k + 1 := by omega
          subst heq1; rw [bitsOf_getD_k1]
    · set j := w - (k + 2)
      have hj : j < D.gates.length := by omega
      have hw_eq : w = k + 2 + j := by omega
      rw [hw_eq] at htrue ⊢
      have hlen1 : (bitsOf Y1).length = k + 2 := bitsOf_length Y1
      have hlen2 : (bitsOf Y2).length = k + 2 := bitsOf_length Y2
      rw [← hlen1, wires_getD_gate_rb D (bitsOf Y1) (by rw [hlen1]; exact hRB) j hj] at htrue
      rw [← hlen2, wires_getD_gate_rb D (bitsOf Y2) (by rw [hlen2]; exact hRB) j hj]
      obtain ⟨hop, _⟩ := gate_op_and_or D hFit hNot j hj
      rcases hop with h | h <;> rw [h] at htrue ⊢
      · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at htrue ⊢
        rintro _ ⟨i, hi, rfl⟩
        have hilt : i < w := by have := hRB j hj i hi; omega
        exact ih i hilt (by omega) (htrue _ ⟨i, hi, rfl⟩)
      · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at htrue ⊢
        obtain ⟨_, ⟨i, hi, rfl⟩, hit⟩ := htrue
        have hilt : i < w := by have := hRB j hj i hi; omega
        exact ⟨_, ⟨i, hi, rfl⟩, ih i hilt (by omega) hit⟩

lemma eval_mono_false (k : ℕ) (D : Circuit) (hFit : FanInTwo D) (hRB : ReadsBack (k + 2) D)
    (hNot : notCount D = 0) (Y1 Y2 : Finset (Fin k)) (hsub : Y1 ⊆ Y2)
    (w : ℕ) (hw : w < k + 2 + D.gates.length)
    (hf : (D.wires (bitsOf Y2)).getD w false = false) :
    (D.wires (bitsOf Y1)).getD w false = false := by
  cases h : (D.wires (bitsOf Y1)).getD w false
  · rfl
  · have := eval_mono k D hFit hRB hNot Y1 Y2 hsub w hw h
    rw [hf] at this; simp at this

lemma fast_exact_support (k : ℕ) (D : Circuit) (hFit : FanInTwo D) (hRB : ReadsBack (k + 2) D)
    (hNot : notCount D = 0) (F T : Finset (Fin k)) :
    ∀ d : ℕ, ∀ w < k + 2 + D.gates.length, (timesOf k D.gates).getD w 0 ≤ d →
    ∀ m n : ℕ, 0 < m → 0 < n →
      (∀ X ⊆ T \ F, X.card < m → (D.wires (bitsOf (F ∪ X))).getD w false = false) →
      (∀ Y ⊆ T \ F, Y.card < n → (D.wires (bitsOf ((F ∪ T) \ Y))).getD w false = true) →
      m * n ≤ 2 ^ d ∧
      (m * n = 2 ^ d →
        ∃ U ⊆ T \ F, U.card = 2 ^ d ∧
          (∀ x ∈ U, ∃ X ⊆ U, x ∈ X ∧ X.card ≤ m ∧ (D.wires (bitsOf (F ∪ X))).getD w false = true) ∧
          (∀ x ∈ U, ∃ Y ⊆ U, x ∈ Y ∧ Y.card ≤ n ∧ (D.wires (bitsOf ((F ∪ T) \ Y))).getD w false = false)) := by
  intro d
  induction d with
  | zero =>
    intro w hw htw m n hm hn hM hN
    have hw_lt : w < k + 2 := by
      by_contra hge
      set j := w - (k + 2)
      have hj : j < D.gates.length := by omega
      have hw_eq : w = k + 2 + j := by omega
      have ht := timesOf_gate_pos k D hFit hNot j hj
      rw [hw_eq] at htw; omega
    have hw_k : w < k := by
      by_contra hge
      by_cases heq : w = k
      · have htrue := hN ∅ (Finset.empty_subset _) hn
        rw [heq, wires_getD_input _ _ k (by rw [bitsOf_length]; omega), bitsOf_getD_k] at htrue
        simp at htrue
      · have heq1 : w = k + 1 := by omega
        have hfalse := hM ∅ (Finset.empty_subset _) hm
        rw [heq1, wires_getD_input _ _ (k + 1) (by rw [bitsOf_length]; omega), bitsOf_getD_k1] at hfalse
        simp at hfalse
    let j : Fin k := ⟨w, hw_k⟩
    have hj_notF : j ∉ F := by
      intro hjF
      have hfalse := hM ∅ (Finset.empty_subset _) hm
      rw [wires_getD_input _ _ w (by rw [bitsOf_length]; omega), bitsOf_getD_lt _ _ hw_k] at hfalse
      simp [j, hjF] at hfalse
    have hj_T : j ∈ T := by
      have htrue := hN ∅ (Finset.empty_subset _) hn
      rw [wires_getD_input _ _ w (by rw [bitsOf_length]; omega), bitsOf_getD_lt _ _ hw_k] at htrue
      simp only [Finset.sdiff_empty, Finset.mem_union, decide_eq_true_eq] at htrue
      rcases htrue with h | h
      · exact absurd h hj_notF
      · exact h
    have hjΔ : j ∈ T \ F := Finset.mem_sdiff.mpr ⟨hj_T, hj_notF⟩
    have hm1 : m = 1 := by
      by_contra hne
      have h1lt : 1 < m := by omega
      have hfalse := hM {j} (Finset.singleton_subset_iff.mpr hjΔ) (by simpa using h1lt)
      rw [wires_getD_input _ _ w (by rw [bitsOf_length]; omega), bitsOf_getD_lt _ _ hw_k] at hfalse
      simp [j] at hfalse
    have hn1 : n = 1 := by
      by_contra hne
      have h1lt : 1 < n := by omega
      have htrue := hN {j} (Finset.singleton_subset_iff.mpr hjΔ) (by simpa using h1lt)
      rw [wires_getD_input _ _ w (by rw [bitsOf_length]; omega), bitsOf_getD_lt _ _ hw_k] at htrue
      simp [j] at htrue
    refine ⟨by rw [hm1, hn1]; simp, fun _ => ?_⟩
    refine ⟨{j}, Finset.singleton_subset_iff.mpr hjΔ, by simp, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
      refine ⟨{j}, Finset.Subset.refl _, Finset.mem_singleton_self j, by simp [hm1], ?_⟩
      rw [wires_getD_input _ _ w (by rw [bitsOf_length]; omega), bitsOf_getD_lt _ _ hw_k]
      simp [j]
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
      refine ⟨{j}, Finset.Subset.refl _, Finset.mem_singleton_self j, by simp [hn1], ?_⟩
      rw [wires_getD_input _ _ w (by rw [bitsOf_length]; omega), bitsOf_getD_lt _ _ hw_k]
      simp [j]
  | succ d ih =>
    intro w hw htw m n hm hn hM hN
    by_cases hle : (timesOf k D.gates).getD w 0 ≤ d
    · have h1 := (ih w hw hle m n hm hn hM hN).1
      have hpos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
      have hpow : 2 ^ d < 2 ^ (d + 1) := by rw [pow_succ]; omega
      exact ⟨by omega, fun heq => by omega⟩
    · have hw_ge : k + 2 ≤ w := by
        by_contra hlt
        have ht0 := timesOf_getD_input k D.gates w (by omega)
        omega
      set j := w - (k + 2)
      have hj : j < D.gates.length := by omega
      have hw_eq : w = k + 2 + j := by omega
      obtain ⟨hop, hlen_inp⟩ := gate_op_and_or D hFit hNot j hj
      have hgate_eval : ∀ Z : Finset (Fin k),
          (D.wires (bitsOf Z)).getD w false =
            (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => (D.wires (bitsOf Z)).getD i false) := by
        intro Z
        have hlenZ : (bitsOf Z).length = k + 2 := bitsOf_length Z
        rw [hw_eq, ← hlenZ, wires_getD_gate_rb D (bitsOf Z) (by rw [hlenZ]; exact hRB) j hj]
      rcases hinp : (gateAt D j).inputs with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩
      · rcases hop with ha | ho
        · have hf := hM ∅ (Finset.empty_subset _) hm
          rw [hgate_eval, hinp, ha] at hf
          simp [GateOp.eval] at hf
        · have ht := hN ∅ (Finset.empty_subset _) hn
          rw [hgate_eval, hinp, ho] at ht
          simp [GateOp.eval] at ht
      · have hw1_lt : w1 < k + 2 + j := hRB j hj w1 (by rw [hinp]; simp)
        have hw1_bd : w1 < k + 2 + D.gates.length := by omega
        have ht1_le := timesOf_gate_input_lt k D hFit hRB hNot j hj w1 (by rw [hinp]; simp)
        have ht1 : (timesOf k D.gates).getD w1 0 ≤ d := by rw [hw_eq] at htw; omega
        have heq_w : ∀ Z : Finset (Fin k),
            (D.wires (bitsOf Z)).getD w false = (D.wires (bitsOf Z)).getD w1 false := by
          intro Z
          rw [hgate_eval, hinp]
          rcases hop with h | h <;> simp [h, GateOp.eval]
        have h1 := (ih w1 hw1_bd ht1 m n hm hn
          (fun X hX hc => by rw [← heq_w]; exact hM X hX hc)
          (fun Y hY hc => by rw [← heq_w]; exact hN Y hY hc)).1
        have hpos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
        have hpow : 2 ^ d < 2 ^ (d + 1) := by rw [pow_succ]; omega
        exact ⟨by omega, fun heq => by omega⟩
      · have hw1_lt : w1 < k + 2 + j := hRB j hj w1 (by rw [hinp]; simp)
        have hw2_lt : w2 < k + 2 + j := hRB j hj w2 (by rw [hinp]; simp)
        have hw1_bd : w1 < k + 2 + D.gates.length := by omega
        have hw2_bd : w2 < k + 2 + D.gates.length := by omega
        have ht1_le := timesOf_gate_input_lt k D hFit hRB hNot j hj w1 (by rw [hinp]; simp)
        have ht2_le := timesOf_gate_input_lt k D hFit hRB hNot j hj w2 (by rw [hinp]; simp)
        have ht1 : (timesOf k D.gates).getD w1 0 ≤ d := by rw [hw_eq] at htw; omega
        have ht2 : (timesOf k D.gates).getD w2 0 ≤ d := by rw [hw_eq] at htw; omega
        have heval_and : (gateAt D j).op = .and → ∀ Z : Finset (Fin k),
            (D.wires (bitsOf Z)).getD w false =
              ((D.wires (bitsOf Z)).getD w1 false && (D.wires (bitsOf Z)).getD w2 false) := by
          intro ha Z
          rw [hgate_eval, hinp, ha]
          simp [GateOp.eval]
        have heval_or : (gateAt D j).op = .or → ∀ Z : Finset (Fin k),
            (D.wires (bitsOf Z)).getD w false =
              ((D.wires (bitsOf Z)).getD w1 false || (D.wires (bitsOf Z)).getD w2 false) := by
          intro ho Z
          rw [hgate_eval, hinp, ho]
          simp [GateOp.eval]
        rcases hop with ha | ho
        ·
          have hN1 : ∀ Y ⊆ T \ F, Y.card < n → (D.wires (bitsOf ((F ∪ T) \ Y))).getD w1 false = true := by
            intro Y hY hc
            have h := hN Y hY hc
            rw [heval_and ha] at h; exact (Bool.and_eq_true _ _ |>.mp h).1
          have hN2 : ∀ Y ⊆ T \ F, Y.card < n → (D.wires (bitsOf ((F ∪ T) \ Y))).getD w2 false = true := by
            intro Y hY hc
            have h := hN Y hY hc
            rw [heval_and ha] at h; exact (Bool.and_eq_true _ _ |>.mp h).2
          have hex1 : ∃ s, ∃ X ⊆ T \ F, X.card = s ∧ (D.wires (bitsOf (F ∪ X))).getD w1 false = true := by
            refine ⟨(T \ F).card, T \ F, Finset.Subset.refl _, rfl, ?_⟩
            have h := hN1 ∅ (Finset.empty_subset _) hn
            have heq : F ∪ (T \ F) = (F ∪ T) \ ∅ := by rw [Finset.sdiff_empty]; ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
            rw [heq]; exact h
          have hex2 : ∃ s, ∃ X ⊆ T \ F, X.card = s ∧ (D.wires (bitsOf (F ∪ X))).getD w2 false = true := by
            refine ⟨(T \ F).card, T \ F, Finset.Subset.refl _, rfl, ?_⟩
            have h := hN2 ∅ (Finset.empty_subset _) hn
            have heq : F ∪ (T \ F) = (F ∪ T) \ ∅ := by rw [Finset.sdiff_empty]; ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
            rw [heq]; exact h
          classical
          obtain ⟨m1, hm1_def⟩ : ∃ m1, m1 = Nat.find hex1 := ⟨_, rfl⟩
          obtain ⟨m2, hm2_def⟩ : ∃ m2, m2 = Nat.find hex2 := ⟨_, rfl⟩
          obtain ⟨X1, hX1sub, hX1card, hX1true⟩ : ∃ X ⊆ T \ F, X.card = m1 ∧ (D.wires (bitsOf (F ∪ X))).getD w1 false = true := by
            rw [hm1_def]; exact Nat.find_spec hex1
          obtain ⟨X2, hX2sub, hX2card, hX2true⟩ : ∃ X ⊆ T \ F, X.card = m2 ∧ (D.wires (bitsOf (F ∪ X))).getD w2 false = true := by
            rw [hm2_def]; exact Nat.find_spec hex2
          have hm_le : m ≤ m1 + m2 := by
            by_contra hlt
            have hcard : (X1 ∪ X2).card < m := by
              have := Finset.card_union_le X1 X2; omega
            have hf := hM (X1 ∪ X2) (Finset.union_subset hX1sub hX2sub) hcard
            have ht1' := eval_mono k D hFit hRB hNot (F ∪ X1) (F ∪ (X1 ∪ X2))
              (Finset.union_subset_union_right Finset.subset_union_left) w1 hw1_bd hX1true
            have ht2' := eval_mono k D hFit hRB hNot (F ∪ X2) (F ∪ (X1 ∪ X2))
              (Finset.union_subset_union_right Finset.subset_union_right) w2 hw2_bd hX2true
            rw [heval_and ha, ht1', ht2'] at hf; exact Bool.noConfusion hf
          have hM1 : ∀ X ⊆ T \ F, X.card < m1 → (D.wires (bitsOf (F ∪ X))).getD w1 false = false := by
            intro X hX hc
            cases h : (D.wires (bitsOf (F ∪ X))).getD w1 false
            · rfl
            · exact absurd ⟨X, hX, rfl, h⟩ (Nat.find_min hex1 (by omega))
          have hM2 : ∀ X ⊆ T \ F, X.card < m2 → (D.wires (bitsOf (F ∪ X))).getD w2 false = false := by
            intro X hX hc
            cases h : (D.wires (bitsOf (F ∪ X))).getD w2 false
            · rfl
            · exact absurd ⟨X, hX, rfl, h⟩ (Nat.find_min hex2 (by omega))
          have hb1 : m1 * n ≤ 2 ^ d := by
            by_cases hm10 : m1 = 0
            · rw [hm10, Nat.zero_mul]; exact Nat.zero_le _
            · exact (ih w1 hw1_bd ht1 m1 n (by omega) hn hM1 hN1).1
          have hb2 : m2 * n ≤ 2 ^ d := by
            by_cases hm20 : m2 = 0
            · rw [hm20, Nat.zero_mul]; exact Nat.zero_le _
            · exact (ih w2 hw2_bd ht2 m2 n (by omega) hn hM2 hN2).1
          have hbd : m * n ≤ 2 ^ (d + 1) := by
            calc m * n ≤ (m1 + m2) * n := Nat.mul_le_mul_right n hm_le
              _ = m1 * n + m2 * n := Nat.add_mul _ _ _
              _ ≤ 2 ^ d + 2 ^ d := Nat.add_le_add hb1 hb2
              _ = 2 ^ (d + 1) := by rw [pow_succ]; omega
          refine ⟨hbd, fun heq => ?_⟩
          have hpow_pos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
          have hsum_le : m * n ≤ m1 * n + m2 * n := by
            rw [← Nat.add_mul]; exact Nat.mul_le_mul_right n hm_le
          have heq1 : m1 * n = 2 ^ d := by rw [pow_succ] at heq; omega
          have heq2 : m2 * n = 2 ^ d := by rw [pow_succ] at heq; omega
          have hm1_pos : 0 < m1 := by
            by_contra h0; have : m1 = 0 := by omega
            rw [this, Nat.zero_mul] at heq1; omega
          have hm2_pos : 0 < m2 := by
            by_contra h0; have : m2 = 0 := by omega
            rw [this, Nat.zero_mul] at heq2; omega
          have hm_eq : m = m1 + m2 := by
            have hmn : m * n = (m1 + m2) * n := by rw [Nat.add_mul, heq1, heq2, heq, pow_succ]; omega
            exact Nat.eq_of_mul_eq_mul_right hn hmn
          obtain ⟨U1, hU1sub, hU1card, hU1X, hU1Y⟩ :=
            (ih w1 hw1_bd ht1 m1 n hm1_pos hn hM1 hN1).2 heq1
          obtain ⟨U2, hU2sub, hU2card, hU2X, hU2Y⟩ :=
            (ih w2 hw2_bd ht2 m2 n hm2_pos hn hM2 hN2).2 heq2
          have hdisj : Disjoint U1 U2 := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            obtain ⟨A1, hA1sub, hxA1, hA1card, hA1t⟩ := hU1X x hx1
            obtain ⟨A2, hA2sub, hxA2, hA2card, hA2t⟩ := hU2X x hx2
            have hinter : 1 ≤ (A1 ∩ A2).card :=
              Finset.one_le_card.mpr ⟨x, Finset.mem_inter.mpr ⟨hxA1, hxA2⟩⟩
            have hcard : (A1 ∪ A2).card < m := by
              have := Finset.card_union_add_card_inter A1 A2; omega
            have hf := hM (A1 ∪ A2) (Finset.union_subset (hA1sub.trans hU1sub) (hA2sub.trans hU2sub)) hcard
            have ht1' := eval_mono k D hFit hRB hNot (F ∪ A1) (F ∪ (A1 ∪ A2))
              (Finset.union_subset_union_right Finset.subset_union_left) w1 hw1_bd hA1t
            have ht2' := eval_mono k D hFit hRB hNot (F ∪ A2) (F ∪ (A1 ∪ A2))
              (Finset.union_subset_union_right Finset.subset_union_right) w2 hw2_bd hA2t
            rw [heval_and ha, ht1', ht2'] at hf; exact Bool.noConfusion hf
          refine ⟨U1 ∪ U2, Finset.union_subset hU1sub hU2sub, ?_, ?_, ?_⟩
          · rw [Finset.card_union_of_disjoint hdisj, hU1card, hU2card, pow_succ]; omega
          · intro x hx
            obtain ⟨z1, hz1⟩ := Finset.card_pos.mp (by omega : 0 < U1.card)
            obtain ⟨z2, hz2⟩ := Finset.card_pos.mp (by omega : 0 < U2.card)
            rcases Finset.mem_union.mp hx with hx1 | hx2
            · obtain ⟨A1, hA1sub, hxA1, hA1c, hA1t⟩ := hU1X x hx1
              obtain ⟨A2, hA2sub, _, hA2c, hA2t⟩ := hU2X z2 hz2
              refine ⟨A1 ∪ A2, Finset.union_subset (hA1sub.trans Finset.subset_union_left)
                (hA2sub.trans Finset.subset_union_right), Finset.mem_union_left _ hxA1,
                (Finset.card_union_le _ _).trans (by omega), ?_⟩
              rw [heval_and ha]
              have ht1' := eval_mono k D hFit hRB hNot (F ∪ A1) (F ∪ (A1 ∪ A2))
                (Finset.union_subset_union_right Finset.subset_union_left) w1 hw1_bd hA1t
              have ht2' := eval_mono k D hFit hRB hNot (F ∪ A2) (F ∪ (A1 ∪ A2))
                (Finset.union_subset_union_right Finset.subset_union_right) w2 hw2_bd hA2t
              rw [ht1', ht2']; rfl
            · obtain ⟨A1, hA1sub, _, hA1c, hA1t⟩ := hU1X z1 hz1
              obtain ⟨A2, hA2sub, hxA2, hA2c, hA2t⟩ := hU2X x hx2
              refine ⟨A1 ∪ A2, Finset.union_subset (hA1sub.trans Finset.subset_union_left)
                (hA2sub.trans Finset.subset_union_right), Finset.mem_union_right _ hxA2,
                (Finset.card_union_le _ _).trans (by omega), ?_⟩
              rw [heval_and ha]
              have ht1' := eval_mono k D hFit hRB hNot (F ∪ A1) (F ∪ (A1 ∪ A2))
                (Finset.union_subset_union_right Finset.subset_union_left) w1 hw1_bd hA1t
              have ht2' := eval_mono k D hFit hRB hNot (F ∪ A2) (F ∪ (A1 ∪ A2))
                (Finset.union_subset_union_right Finset.subset_union_right) w2 hw2_bd hA2t
              rw [ht1', ht2']; rfl
          · intro x hx
            rcases Finset.mem_union.mp hx with hx1 | hx2
            · obtain ⟨B1, hB1sub, hxB1, hB1c, hB1f⟩ := hU1Y x hx1
              refine ⟨B1, hB1sub.trans Finset.subset_union_left, hxB1, hB1c, ?_⟩
              rw [heval_and ha, hB1f]; rfl
            · obtain ⟨B2, hB2sub, hxB2, hB2c, hB2f⟩ := hU2Y x hx2
              refine ⟨B2, hB2sub.trans Finset.subset_union_right, hxB2, hB2c, ?_⟩
              rw [heval_and ha, hB2f]; simp
        ·
          have hM1 : ∀ X ⊆ T \ F, X.card < m → (D.wires (bitsOf (F ∪ X))).getD w1 false = false := by
            intro X hX hc
            have h := hM X hX hc
            rw [heval_or ho] at h; exact (Bool.or_eq_false_iff.mp h).1
          have hM2 : ∀ X ⊆ T \ F, X.card < m → (D.wires (bitsOf (F ∪ X))).getD w2 false = false := by
            intro X hX hc
            have h := hM X hX hc
            rw [heval_or ho] at h; exact (Bool.or_eq_false_iff.mp h).2
          have hex1 : ∃ s, ∃ Y ⊆ T \ F, Y.card = s ∧ (D.wires (bitsOf ((F ∪ T) \ Y))).getD w1 false = false := by
            refine ⟨(T \ F).card, T \ F, Finset.Subset.refl _, rfl, ?_⟩
            have h := hM1 ∅ (Finset.empty_subset _) hm
            have heq : (F ∪ T) \ (T \ F) = F ∪ ∅ := by rw [Finset.union_empty]; ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
            rw [heq]; exact h
          have hex2 : ∃ s, ∃ Y ⊆ T \ F, Y.card = s ∧ (D.wires (bitsOf ((F ∪ T) \ Y))).getD w2 false = false := by
            refine ⟨(T \ F).card, T \ F, Finset.Subset.refl _, rfl, ?_⟩
            have h := hM2 ∅ (Finset.empty_subset _) hm
            have heq : (F ∪ T) \ (T \ F) = F ∪ ∅ := by rw [Finset.union_empty]; ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
            rw [heq]; exact h
          classical
          obtain ⟨n1, hn1_def⟩ : ∃ n1, n1 = Nat.find hex1 := ⟨_, rfl⟩
          obtain ⟨n2, hn2_def⟩ : ∃ n2, n2 = Nat.find hex2 := ⟨_, rfl⟩
          obtain ⟨Y1, hY1sub, hY1card, hY1false⟩ : ∃ Y ⊆ T \ F, Y.card = n1 ∧ (D.wires (bitsOf ((F ∪ T) \ Y))).getD w1 false = false := by
            rw [hn1_def]; exact Nat.find_spec hex1
          obtain ⟨Y2, hY2sub, hY2card, hY2false⟩ : ∃ Y ⊆ T \ F, Y.card = n2 ∧ (D.wires (bitsOf ((F ∪ T) \ Y))).getD w2 false = false := by
            rw [hn2_def]; exact Nat.find_spec hex2
          have hn_le : n ≤ n1 + n2 := by
            by_contra hlt
            have hcard : (Y1 ∪ Y2).card < n := by
              have := Finset.card_union_le Y1 Y2; omega
            have ht := hN (Y1 ∪ Y2) (Finset.union_subset hY1sub hY2sub) hcard
            have hf1' := eval_mono_false k D hFit hRB hNot ((F ∪ T) \ (Y1 ∪ Y2)) ((F ∪ T) \ Y1)
              (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_left) w1 hw1_bd hY1false
            have hf2' := eval_mono_false k D hFit hRB hNot ((F ∪ T) \ (Y1 ∪ Y2)) ((F ∪ T) \ Y2)
              (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_right) w2 hw2_bd hY2false
            rw [heval_or ho, hf1', hf2'] at ht; exact Bool.noConfusion ht
          have hN1 : ∀ Y ⊆ T \ F, Y.card < n1 → (D.wires (bitsOf ((F ∪ T) \ Y))).getD w1 false = true := by
            intro Y hY hc
            cases h : (D.wires (bitsOf ((F ∪ T) \ Y))).getD w1 false
            · exact absurd ⟨Y, hY, rfl, h⟩ (Nat.find_min hex1 (by omega))
            · rfl
          have hN2 : ∀ Y ⊆ T \ F, Y.card < n2 → (D.wires (bitsOf ((F ∪ T) \ Y))).getD w2 false = true := by
            intro Y hY hc
            cases h : (D.wires (bitsOf ((F ∪ T) \ Y))).getD w2 false
            · exact absurd ⟨Y, hY, rfl, h⟩ (Nat.find_min hex2 (by omega))
            · rfl
          have hb1 : m * n1 ≤ 2 ^ d := by
            by_cases hn10 : n1 = 0
            · rw [hn10, Nat.mul_zero]; exact Nat.zero_le _
            · exact (ih w1 hw1_bd ht1 m n1 hm (by omega) hM1 hN1).1
          have hb2 : m * n2 ≤ 2 ^ d := by
            by_cases hn20 : n2 = 0
            · rw [hn20, Nat.mul_zero]; exact Nat.zero_le _
            · exact (ih w2 hw2_bd ht2 m n2 hm (by omega) hM2 hN2).1
          have hbd : m * n ≤ 2 ^ (d + 1) := by
            calc m * n ≤ m * (n1 + n2) := Nat.mul_le_mul_left m hn_le
              _ = m * n1 + m * n2 := Nat.mul_add _ _ _
              _ ≤ 2 ^ d + 2 ^ d := Nat.add_le_add hb1 hb2
              _ = 2 ^ (d + 1) := by rw [pow_succ]; omega
          refine ⟨hbd, fun heq => ?_⟩
          have hpow_pos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
          have hsum_le : m * n ≤ m * n1 + m * n2 := by
            rw [← Nat.mul_add]; exact Nat.mul_le_mul_left m hn_le
          have heq1 : m * n1 = 2 ^ d := by rw [pow_succ] at heq; omega
          have heq2 : m * n2 = 2 ^ d := by rw [pow_succ] at heq; omega
          have hn1_pos : 0 < n1 := by
            by_contra h0; have : n1 = 0 := by omega
            rw [this, Nat.mul_zero] at heq1; omega
          have hn2_pos : 0 < n2 := by
            by_contra h0; have : n2 = 0 := by omega
            rw [this, Nat.mul_zero] at heq2; omega
          have hn_eq : n = n1 + n2 := by
            have hmn : m * n = m * (n1 + n2) := by rw [Nat.mul_add, heq1, heq2, heq, pow_succ]; omega
            exact Nat.eq_of_mul_eq_mul_left hm hmn
          obtain ⟨U1, hU1sub, hU1card, hU1X, hU1Y⟩ :=
            (ih w1 hw1_bd ht1 m n1 hm hn1_pos hM1 hN1).2 heq1
          obtain ⟨U2, hU2sub, hU2card, hU2X, hU2Y⟩ :=
            (ih w2 hw2_bd ht2 m n2 hm hn2_pos hM2 hN2).2 heq2
          have hdisj : Disjoint U1 U2 := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            obtain ⟨B1, hB1sub, hxB1, hB1card, hB1f⟩ := hU1Y x hx1
            obtain ⟨B2, hB2sub, hxB2, hB2card, hB2f⟩ := hU2Y x hx2
            have hinter : 1 ≤ (B1 ∩ B2).card :=
              Finset.one_le_card.mpr ⟨x, Finset.mem_inter.mpr ⟨hxB1, hxB2⟩⟩
            have hcard : (B1 ∪ B2).card < n := by
              have := Finset.card_union_add_card_inter B1 B2; omega
            have ht := hN (B1 ∪ B2) (Finset.union_subset (hB1sub.trans hU1sub) (hB2sub.trans hU2sub)) hcard
            have hf1' := eval_mono_false k D hFit hRB hNot ((F ∪ T) \ (B1 ∪ B2)) ((F ∪ T) \ B1)
              (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_left) w1 hw1_bd hB1f
            have hf2' := eval_mono_false k D hFit hRB hNot ((F ∪ T) \ (B1 ∪ B2)) ((F ∪ T) \ B2)
              (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_right) w2 hw2_bd hB2f
            rw [heval_or ho, hf1', hf2'] at ht; exact Bool.noConfusion ht
          refine ⟨U1 ∪ U2, Finset.union_subset hU1sub hU2sub, ?_, ?_, ?_⟩
          · rw [Finset.card_union_of_disjoint hdisj, hU1card, hU2card, pow_succ]; omega
          · intro x hx
            rcases Finset.mem_union.mp hx with hx1 | hx2
            · obtain ⟨A1, hA1sub, hxA1, hA1c, hA1t⟩ := hU1X x hx1
              refine ⟨A1, hA1sub.trans Finset.subset_union_left, hxA1, hA1c, ?_⟩
              rw [heval_or ho, hA1t]; rfl
            · obtain ⟨A2, hA2sub, hxA2, hA2c, hA2t⟩ := hU2X x hx2
              refine ⟨A2, hA2sub.trans Finset.subset_union_right, hxA2, hA2c, ?_⟩
              rw [heval_or ho, hA2t]; simp
          · intro x hx
            obtain ⟨z1, hz1⟩ := Finset.card_pos.mp (by omega : 0 < U1.card)
            obtain ⟨z2, hz2⟩ := Finset.card_pos.mp (by omega : 0 < U2.card)
            rcases Finset.mem_union.mp hx with hx1 | hx2
            · obtain ⟨B1, hB1sub, hxB1, hB1c, hB1f⟩ := hU1Y x hx1
              obtain ⟨B2, hB2sub, _, hB2c, hB2f⟩ := hU2Y z2 hz2
              refine ⟨B1 ∪ B2, Finset.union_subset (hB1sub.trans Finset.subset_union_left)
                (hB2sub.trans Finset.subset_union_right), Finset.mem_union_left _ hxB1,
                (Finset.card_union_le _ _).trans (by omega), ?_⟩
              rw [heval_or ho]
              have hf1' := eval_mono_false k D hFit hRB hNot ((F ∪ T) \ (B1 ∪ B2)) ((F ∪ T) \ B1)
                (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_left) w1 hw1_bd hB1f
              have hf2' := eval_mono_false k D hFit hRB hNot ((F ∪ T) \ (B1 ∪ B2)) ((F ∪ T) \ B2)
                (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_right) w2 hw2_bd hB2f
              rw [hf1', hf2']; rfl
            · obtain ⟨B1, hB1sub, _, hB1c, hB1f⟩ := hU1Y z1 hz1
              obtain ⟨B2, hB2sub, hxB2, hB2c, hB2f⟩ := hU2Y x hx2
              refine ⟨B1 ∪ B2, Finset.union_subset (hB1sub.trans Finset.subset_union_left)
                (hB2sub.trans Finset.subset_union_right), Finset.mem_union_right _ hxB2,
                (Finset.card_union_le _ _).trans (by omega), ?_⟩
              rw [heval_or ho]
              have hf1' := eval_mono_false k D hFit hRB hNot ((F ∪ T) \ (B1 ∪ B2)) ((F ∪ T) \ B1)
                (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_left) w1 hw1_bd hB1f
              have hf2' := eval_mono_false k D hFit hRB hNot ((F ∪ T) \ (B1 ∪ B2)) ((F ∪ T) \ B2)
                (Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_right) w2 hw2_bd hB2f
              rw [hf1', hf2']; rfl
      · rw [hinp] at hlen_inp; simp at hlen_inp

def btTree (op : GateOp) (base : ℕ) : ℕ → List ℕ → List Gate × ℕ
  | 0, ws => ([], ws.getD 0 0)
  | d + 1, ws =>
    let l := btTree op base d (ws.take (2 ^ d))
    let r := btTree op (base + l.1.length) d (ws.drop (2 ^ d))
    (l.1 ++ r.1 ++ [(⟨op, [l.2, r.2]⟩ : Gate)], base + l.1.length + r.1.length)

lemma btTree_spec (op : GateOp) (hop : op = .and ∨ op = .or) :
    ∀ d base ws, ws.length = 2 ^ d → (∀ w ∈ ws, w < base) →
      let res := btTree op base d ws
      res.1.length = 2 ^ d - 1 ∧
      (∀ g ∈ res.1, g.op = op ∧ g.inputs.length = 2) ∧
      (∀ j < res.1.length, ∀ i ∈ (res.1.getD j (⟨.or, []⟩ : Gate)).inputs, i < base + j) ∧
      res.2 < base + res.1.length := by
  intro d
  induction d with
  | zero =>
    intro base ws hlen hws
    simp only [btTree, List.length_nil, pow_zero, Nat.sub_self, true_and]
    refine ⟨by simp, by simp, ?_⟩
    rcases ws with _ | ⟨w, _⟩
    · simp at hlen
    · simpa using hws w (by simp)
  | succ d ih =>
    intro base ws hlen hws
    have hpow : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
    have hltake : (ws.take (2 ^ d)).length = 2 ^ d := by
      rw [List.length_take, hlen, pow_succ]; omega
    have hldrop : (ws.drop (2 ^ d)).length = 2 ^ d := by
      rw [List.length_drop, hlen, pow_succ]; omega
    have hlt : ∀ w ∈ ws.take (2 ^ d), w < base := fun w hw => hws w (List.mem_of_mem_take hw)
    have hld : ∀ w ∈ ws.drop (2 ^ d), w < base + (btTree op base d (ws.take (2 ^ d))).1.length :=
      fun w hw => Nat.lt_of_lt_of_le (hws w (List.mem_of_mem_drop hw)) (Nat.le_add_right _ _)
    obtain ⟨hl_len, hl_g, hl_rb, hl_out⟩ := ih base (ws.take (2 ^ d)) hltake hlt
    obtain ⟨hr_len, hr_g, hr_rb, hr_out⟩ := ih (base + (btTree op base d (ws.take (2 ^ d))).1.length) (ws.drop (2 ^ d)) hldrop hld
    dsimp only [btTree]
    set l := btTree op base d (ws.take (2 ^ d))
    set r := btTree op (base + l.1.length) d (ws.drop (2 ^ d))
    have htot_len : (l.1 ++ r.1 ++ [(⟨op, [l.2, r.2]⟩ : Gate)]).length = 2 ^ (d + 1) - 1 := by
      simp only [List.length_append, List.length_singleton, hl_len, hr_len, pow_succ]; omega
    refine ⟨htot_len, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (h | h) | rfl
      · exact hl_g g h
      · exact hr_g g h
      · exact ⟨rfl, rfl⟩
    · intro j hj i hi
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hj1 : j < l.1.length
      · rw [List.append_assoc, List.getD_append _ _ _ _ hj1] at hi
        exact hl_rb j hj1 i hi
      · by_cases hj2 : j < l.1.length + r.1.length
        · have hj' : j - l.1.length < r.1.length := by omega
          rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
            List.getD_append _ _ _ _ hj'] at hi
          have := hr_rb (j - l.1.length) hj' i hi
          omega
        · have hjeq : j = l.1.length + r.1.length := by omega
          rw [hjeq, List.getD_append_right _ _ _ _ (by simp), List.length_append,
            Nat.sub_self, List.getD_cons_zero] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
    · simp only [List.length_append, List.length_singleton]; omega

lemma btTree_eval (op : GateOp) (hop : op = .and ∨ op = .or) :
    ∀ d init ws, ws.length = 2 ^ d → (∀ w ∈ ws, w < init.length) →
      (Circuit.wires ⟨(btTree op init.length d ws).1, 0⟩ init).getD (btTree op init.length d ws).2 false =
        match op with
        | .and => ws.all (fun w => init.getD w false)
        | _ => ws.any (fun w => init.getD w false) := by
  intro d
  induction d with
  | zero =>
    intro init ws hlen _
    rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hlen
    rcases hop with rfl | rfl <;> simp [btTree, Circuit.wires]
  | succ d ih =>
    intro init ws hlen hws
    have hpow : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
    have hltake : (ws.take (2 ^ d)).length = 2 ^ d := by
      rw [List.length_take, hlen, pow_succ]; omega
    have hldrop : (ws.drop (2 ^ d)).length = 2 ^ d := by
      rw [List.length_drop, hlen, pow_succ]; omega
    have hlt : ∀ w ∈ ws.take (2 ^ d), w < init.length := fun w hw => hws w (List.mem_of_mem_take hw)
    have hspL := btTree_spec op hop d init.length (ws.take (2 ^ d)) hltake hlt
    dsimp only [btTree]
    set l := btTree op init.length d (ws.take (2 ^ d))
    set initL := Circuit.wires ⟨l.1, 0⟩ init
    have hinitL_len : initL.length = init.length + l.1.length := wires_length ⟨l.1, 0⟩ init
    have hld : ∀ w ∈ ws.drop (2 ^ d), w < initL.length :=
      fun w hw => by rw [hinitL_len]; exact Nat.lt_of_lt_of_le (hws w (List.mem_of_mem_drop hw)) (Nat.le_add_right _ _)
    set r := btTree op (init.length + l.1.length) d (ws.drop (2 ^ d))
    have hr_eq : r = btTree op initL.length d (ws.drop (2 ^ d)) := by rw [hinitL_len]
    have hihL := ih init (ws.take (2 ^ d)) hltake hlt
    have hihR := ih initL (ws.drop (2 ^ d)) hldrop hld
    have hr_init_eq : ∀ w ∈ ws.drop (2 ^ d), initL.getD w false = init.getD w false := by
      intro w hw
      exact wires_getD_input ⟨l.1, 0⟩ init w (hws w (List.mem_of_mem_drop hw))
    rw [wires_append_gate]
    have hlenLR : (Circuit.wires ⟨l.1 ++ r.1, 0⟩ init).length = init.length + l.1.length + r.1.length := by
      rw [wires_length, List.length_append]; omega
    rw [List.getD_append_right _ _ _ _ (by omega), hlenLR, Nat.sub_self, List.getD_cons_zero]
    have hgetL : (Circuit.wires ⟨l.1 ++ r.1, 0⟩ init).getD l.2 false = initL.getD l.2 false :=
      wires_prefix l.1 r.1 init l.2 hspL.2.2.2
    have hgetR : (Circuit.wires ⟨l.1 ++ r.1, 0⟩ init).getD r.2 false =
        (Circuit.wires ⟨r.1, 0⟩ initL).getD r.2 false := by
      rw [wires_append]
    simp only [List.map_cons, List.map_nil, hgetL, hgetR]
    rw [hihL, hr_eq, hihR]
    have hsplit : ws = ws.take (2 ^ d) ++ ws.drop (2 ^ d) := (List.take_append_drop (2 ^ d) ws).symm
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.foldl_cons, List.foldl_nil, Bool.true_and]
      have hdrop_all : (ws.drop (2 ^ d)).all (fun w => initL.getD w false) =
          (ws.drop (2 ^ d)).all (fun w => init.getD w false) := by
        apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
        constructor <;> intro h w hw <;> [rw [← hr_init_eq w hw]; rw [hr_init_eq w hw]] <;> exact h w hw
      rw [hdrop_all]; conv_rhs => rw [hsplit]; rw [List.all_append]
      simp
    · simp only [GateOp.eval]
      have hdrop_any : (ws.drop (2 ^ d)).any (fun w => initL.getD w false) =
          (ws.drop (2 ^ d)).any (fun w => init.getD w false) := by
        apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true]
        constructor <;> rintro ⟨w, hw, h⟩ <;> refine ⟨w, hw, ?_⟩
        · rwa [← hr_init_eq w hw]
        · rwa [hr_init_eq w hw]
      rw [hdrop_any]; conv_rhs => rw [hsplit]; rw [List.any_append]
      simp

lemma btTree_delay (op : GateOp) (hop : op = .and ∨ op = .or) :
    ∀ d ts ws M, ws.length = 2 ^ d → (∀ w ∈ ws, w < ts.length ∧ ts.getD w 0 ≤ M) →
      ((btTree op ts.length d ws).1.foldl delayStep ts).getD (btTree op ts.length d ws).2 0 ≤ M + d := by
  intro d
  induction d with
  | zero =>
    intro ts ws M hlen hws
    rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hlen
    simpa [btTree] using (hws w (by simp)).2
  | succ d ih =>
    intro ts ws M hlen hws
    have hltake : (ws.take (2 ^ d)).length = 2 ^ d := by
      rw [List.length_take, hlen, pow_succ]; omega
    have hldrop : (ws.drop (2 ^ d)).length = 2 ^ d := by
      rw [List.length_drop, hlen, pow_succ]; omega
    have hlt : ∀ w ∈ ws.take (2 ^ d), w < ts.length ∧ ts.getD w 0 ≤ M :=
      fun w hw => hws w (List.mem_of_mem_take hw)
    have hspL := btTree_spec op hop d ts.length (ws.take (2 ^ d)) hltake (fun w hw => (hlt w hw).1)
    dsimp only [btTree]
    set l := btTree op ts.length d (ws.take (2 ^ d))
    set tsL := l.1.foldl delayStep ts
    have htsL_len : tsL.length = ts.length + l.1.length := foldl_delayStep_length l.1 ts
    have hld : ∀ w ∈ ws.drop (2 ^ d), w < tsL.length ∧ tsL.getD w 0 ≤ M := by
      intro w hw
      have h1 := hws w (List.mem_of_mem_drop hw)
      refine ⟨by omega, ?_⟩
      rw [foldl_delayStep_init l.1 ts w h1.1]; exact h1.2
    set r := btTree op (ts.length + l.1.length) d (ws.drop (2 ^ d))
    have hr_eq : r = btTree op tsL.length d (ws.drop (2 ^ d)) := by rw [htsL_len]
    have hihL := ih ts (ws.take (2 ^ d)) M hltake hlt
    have hihR := ih tsL (ws.drop (2 ^ d)) M hldrop hld
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlenLR : ((l.1 ++ r.1).foldl delayStep ts).length = ts.length + l.1.length + r.1.length := by
      rw [foldl_delayStep_length, List.length_append]; omega
    rw [delayStep_eq, List.getD_append_right _ _ _ _ (by omega), hlenLR, Nat.sub_self, List.getD_cons_zero]
    have hgetL : ((l.1 ++ r.1).foldl delayStep ts).getD l.2 0 = tsL.getD l.2 0 :=
      foldl_delayStep_prefix l.1 r.1 ts l.2 hspL.2.2.2
    have hgetR : ((l.1 ++ r.1).foldl delayStep ts).getD r.2 0 = (r.1.foldl delayStep tsL).getD r.2 0 := by
      rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_max, hgetL, hgetR]
    rw [hr_eq]
    have h1 : tsL.getD l.2 0 ≤ M + d := hihL
    have h2 : ((btTree op tsL.length d (ws.drop (2 ^ d))).1.foldl delayStep tsL).getD
        (btTree op tsL.length d (ws.drop (2 ^ d))).2 0 ≤ M + d := hihR
    rcases hop with rfl | rfl <;> simp only [] <;> omega

def buildBalAndGroups (base off u : ℕ) : ℕ → List Gate × List ℕ
  | 0 => ([], [])
  | p + 1 =>
    let prev := buildBalAndGroups base off u p
    let ws := List.ofFn fun q : Fin (2 ^ u) => off + p * 2 ^ u + q.val
    let cur := btTree .and (base + prev.1.length) u ws
    (prev.1 ++ cur.1, prev.2 ++ [cur.2])

lemma buildBalAndGroups_spec (k off u : ℕ) :
    ∀ p : ℕ, off + p * 2 ^ u ≤ k →
      let res := buildBalAndGroups (k + 2) off u p
      res.2.length = p ∧
      (∀ g ∈ res.1, g.op = .and ∧ g.inputs.length = 2) ∧
      (∀ j < res.1.length, ∀ i ∈ (res.1.getD j (⟨.or, []⟩ : Gate)).inputs, i < k + 2 + j) ∧
      (∀ o ∈ res.2, o < k + 2 + res.1.length) ∧
      (∀ o ∈ res.2, (timesOf k res.1).getD o 0 ≤ u) := by
  intro p
  induction p with
  | zero => intro _; simp [buildBalAndGroups]
  | succ p ih =>
    intro hoff
    have hoff_p : off + p * 2 ^ u ≤ k := by
      have : p * 2 ^ u ≤ (p + 1) * 2 ^ u := Nat.mul_le_mul_right _ (Nat.le_succ p)
      omega
    obtain ⟨houts_len, hgates, hrb, houts_lt, houts_d⟩ := ih hoff_p
    dsimp only [buildBalAndGroups]
    set prev := buildBalAndGroups (k + 2) off u p
    set ws := List.ofFn fun q : Fin (2 ^ u) => off + p * 2 ^ u + q.val
    have hws_len : ws.length = 2 ^ u := by simp [ws]
    have hws_lt : ∀ w ∈ ws, w < k + 2 + prev.1.length := by
      intro w hw
      simp only [ws, List.mem_ofFn] at hw
      obtain ⟨q, rfl⟩ := hw
      have hq := q.isLt
      rw [Nat.succ_mul] at hoff; omega
    have hsp := btTree_spec .and (Or.inl rfl) u (k + 2 + prev.1.length) ws hws_len hws_lt
    set cur := btTree .and (k + 2 + prev.1.length) u ws
    refine ⟨by simp [houts_len], ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hgates g h
      · exact hsp.2.1 g h
    · intro j hj i hi
      rw [List.length_append] at hj
      by_cases hj1 : j < prev.1.length
      · rw [List.getD_append _ _ _ _ hj1] at hi; exact hrb j hj1 i hi
      · have hj' : j - prev.1.length < cur.1.length := by omega
        rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        have := hsp.2.2.1 (j - prev.1.length) hj' i hi; omega
    · intro o ho
      simp only [List.mem_append, List.mem_singleton] at ho
      rcases ho with h | rfl
      · have := houts_lt o h; rw [List.length_append]; omega
      · have := hsp.2.2.2; rw [List.length_append]; omega
    · intro o ho
      simp only [List.mem_append, List.mem_singleton] at ho
      rcases ho with h | rfl
      · unfold timesOf
        rw [foldl_delayStep_prefix prev.1 cur.1 (List.replicate (k + 2) 0) o
          (by rw [List.length_replicate]; exact houts_lt o h)]
        exact houts_d o h
      · set tsP := timesOf k prev.1
        have htsP_len : tsP.length = k + 2 + prev.1.length := timesOf_length k prev.1
        have hws_d : ∀ w ∈ ws, w < tsP.length ∧ tsP.getD w 0 ≤ 0 := by
          intro w hw
          simp only [ws, List.mem_ofFn] at hw
          obtain ⟨q, rfl⟩ := hw
          have hq := q.isLt
          rw [Nat.succ_mul] at hoff
          refine ⟨by omega, ?_⟩
          rw [timesOf_getD_input k prev.1 _ (by omega)]
        have hd := btTree_delay .and (Or.inl rfl) u tsP ws 0 hws_len hws_d
        have hcur_eq : cur = btTree .and tsP.length u ws := by rw [htsP_len]
        unfold timesOf
        rw [List.foldl_append]
        change (cur.1.foldl delayStep tsP).getD cur.2 0 ≤ u
        rw [hcur_eq]; simpa using hd

lemma buildBalAndGroups_eval (k off u : ℕ) (x : List Bool) (hxlen : x.length = k + 2) :
    ∀ p : ℕ, off + p * 2 ^ u ≤ k →
      let res := buildBalAndGroups (k + 2) off u p
      res.2.any (fun o => (Circuit.wires ⟨res.1, 0⟩ x).getD o false) =
        decide (∃ r < p, (List.ofFn fun q : Fin (2 ^ u) => off + r * 2 ^ u + q.val).all
          (fun w => x.getD w false) = true) := by
  intro p
  induction p with
  | zero => intro _; simp [buildBalAndGroups]
  | succ p ih =>
    intro hoff
    have hoff_p : off + p * 2 ^ u ≤ k := by
      have : p * 2 ^ u ≤ (p + 1) * 2 ^ u := Nat.mul_le_mul_right _ (Nat.le_succ p)
      omega
    have hspP := buildBalAndGroups_spec k off u p hoff_p
    dsimp only [buildBalAndGroups]
    set prev := buildBalAndGroups (k + 2) off u p
    set ws := List.ofFn fun q : Fin (2 ^ u) => off + p * 2 ^ u + q.val
    set cur := btTree .and (k + 2 + prev.1.length) u ws
    have hws_len : ws.length = 2 ^ u := by simp [ws]
    have hprev_len : (Circuit.wires ⟨prev.1, 0⟩ x).length = k + 2 + prev.1.length := by
      rw [wires_length, hxlen]
    have hws_lt : ∀ w ∈ ws, w < (Circuit.wires ⟨prev.1, 0⟩ x).length := by
      intro w hw; simp only [ws, List.mem_ofFn] at hw; obtain ⟨q, rfl⟩ := hw
      have hq := q.isLt; rw [Nat.succ_mul] at hoff; omega
    have hcur_eq : cur = btTree .and (Circuit.wires ⟨prev.1, 0⟩ x).length u ws := by rw [hprev_len]
    rw [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    have hprev_any : prev.2.any (fun o => (Circuit.wires ⟨prev.1 ++ cur.1, 0⟩ x).getD o false) =
        prev.2.any (fun o => (Circuit.wires ⟨prev.1, 0⟩ x).getD o false) := by
      apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true]
      constructor <;> rintro ⟨o, ho, h⟩ <;> refine ⟨o, ho, ?_⟩
      · rwa [← wires_prefix prev.1 cur.1 x o (by rw [hxlen]; exact hspP.2.2.2.1 o ho)]
      · rwa [wires_prefix prev.1 cur.1 x o (by rw [hxlen]; exact hspP.2.2.2.1 o ho)]
    rw [hprev_any, ih hoff_p]
    have hcur_ev : (Circuit.wires ⟨prev.1 ++ cur.1, 0⟩ x).getD cur.2 false =
        ws.all (fun w => x.getD w false) := by
      rw [wires_append, hcur_eq, btTree_eval .and (Or.inl rfl) u (Circuit.wires ⟨prev.1, 0⟩ x) ws hws_len hws_lt]
      apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
      constructor <;> intro h w hw
      · have hw' := hw; simp only [ws, List.mem_ofFn] at hw'; obtain ⟨q, rfl⟩ := hw'
        have hq := q.isLt; rw [Nat.succ_mul] at hoff
        have := h _ hw; rwa [wires_getD_input ⟨prev.1, 0⟩ x _ (by omega)] at this
      · have hw' := hw; simp only [ws, List.mem_ofFn] at hw'; obtain ⟨q, rfl⟩ := hw'
        have hq := q.isLt; rw [Nat.succ_mul] at hoff
        rw [wires_getD_input ⟨prev.1, 0⟩ x _ (by omega)]; exact h _ hw
    rw [hcur_ev]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨r, hr, hall⟩ | hall)
      · exact ⟨r, Nat.lt_succ_of_lt hr, hall⟩
      · exact ⟨p, Nat.lt_succ_self p, hall⟩
    · rintro ⟨r, hr, hall⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
      · exact Or.inl ⟨r, hlt, hall⟩
      · exact Or.inr hall

def buildBalDNF (k off u v : ℕ) : Circuit :=
  let ag := buildBalAndGroups (k + 2) off u (2 ^ v)
  let oc := btTree .or (k + 2 + ag.1.length) v ag.2
  ⟨ag.1 ++ oc.1, oc.2⟩

lemma buildBalDNF_spec (k off u v : ℕ) (hoff : off + 2 ^ u * 2 ^ v ≤ k) :
    let D := buildBalDNF k off u v
    FanInTwo D ∧
    ReadsBack (k + 2) D ∧
    D.output < k + 2 + D.size ∧
    notCount D = 0 ∧
    (timesOf k D.gates).getD D.output 0 ≤ u + v ∧
    ∀ Y : Finset (Fin k),
      (D.wires (bitsOf Y)).getD D.output false =
        decide (∃ r < 2 ^ v, ∀ q < 2 ^ u,
          ∃ hlt : off + r * 2 ^ u + q < k, (⟨off + r * 2 ^ u + q, hlt⟩ : Fin k) ∈ Y) := by
  have hoff' : off + 2 ^ v * 2 ^ u ≤ k := by rw [Nat.mul_comm]; exact hoff
  have hAG := buildBalAndGroups_spec k off u (2 ^ v) hoff'
  set ag := buildBalAndGroups (k + 2) off u (2 ^ v)
  have hOC := btTree_spec .or (Or.inr rfl) v (k + 2 + ag.1.length) ag.2 hAG.1 hAG.2.2.2.1
  set oc := btTree .or (k + 2 + ag.1.length) v ag.2
  have hFit : FanInTwo (buildBalDNF k off u v) := by
    intro g hg
    simp only [buildBalDNF, List.mem_append] at hg
    rcases hg with h | h
    · obtain ⟨hop, hlen⟩ := hAG.2.1 g h; simp [hop, hlen]
    · obtain ⟨hop, hlen⟩ := hOC.2.1 g h; simp [hop, hlen]
  have hRB : ReadsBack (k + 2) (buildBalDNF k off u v) := by
    intro j hj i hi
    change j < (ag.1 ++ oc.1).length at hj
    rw [List.length_append] at hj
    have hgate : gateAt (buildBalDNF k off u v) j = (ag.1 ++ oc.1).getD j (⟨.or, []⟩ : Gate) := rfl
    rw [hgate] at hi
    by_cases hj1 : j < ag.1.length
    · rw [List.getD_append _ _ _ _ hj1] at hi; exact hAG.2.2.1 j hj1 i hi
    · have hj' : j - ag.1.length < oc.1.length := by omega
      rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      have := hOC.2.2.1 (j - ag.1.length) hj' i hi; omega
  have hOut : (buildBalDNF k off u v).output < k + 2 + (buildBalDNF k off u v).size := by
    change oc.2 < k + 2 + (ag.1 ++ oc.1).length
    have := hOC.2.2.2
    rw [List.length_append]; omega
  have hNot : notCount (buildBalDNF k off u v) = 0 := by
    unfold notCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro g hg
    simp only [buildBalDNF, List.mem_append] at hg
    rcases hg with h | h
    · simp [(hAG.2.1 g h).1]
    · simp [(hOC.2.1 g h).1]
  have hDelay : (timesOf k (buildBalDNF k off u v).gates).getD (buildBalDNF k off u v).output 0 ≤ u + v := by
    set tsA := timesOf k ag.1
    have htsA_len : tsA.length = k + 2 + ag.1.length := timesOf_length k ag.1
    have hoc_eq : oc = btTree .or tsA.length v ag.2 := by rw [htsA_len]
    have hd := btTree_delay .or (Or.inr rfl) v tsA ag.2 u hAG.1
      (fun o ho => ⟨by rw [htsA_len]; exact hAG.2.2.2.1 o ho, hAG.2.2.2.2 o ho⟩)
    simp only [buildBalDNF]
    unfold timesOf
    rw [List.foldl_append]
    change (oc.1.foldl delayStep tsA).getD oc.2 0 ≤ u + v
    rw [hoc_eq]; exact hd
  refine ⟨hFit, hRB, hOut, hNot, hDelay, ?_⟩
  intro Y
  have hbase_len : (Circuit.wires ⟨ag.1, 0⟩ (bitsOf Y)).length = k + 2 + ag.1.length := by
    rw [wires_length, bitsOf_length]
  have hoc_eq : oc = btTree .or (Circuit.wires ⟨ag.1, 0⟩ (bitsOf Y)).length v ag.2 := by rw [hbase_len]
  change (Circuit.wires ⟨ag.1 ++ oc.1, 0⟩ (bitsOf Y)).getD oc.2 false = _
  rw [wires_append, hoc_eq, btTree_eval .or (Or.inr rfl) v (Circuit.wires ⟨ag.1, 0⟩ (bitsOf Y)) ag.2 hAG.1
    (fun o ho => by rw [hbase_len]; exact hAG.2.2.2.1 o ho)]
  rw [buildBalAndGroups_eval k off u (bitsOf Y) (bitsOf_length Y) (2 ^ v) hoff']
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr, hall⟩
    refine ⟨r, hr, fun q hq => ?_⟩
    have hlt : off + r * 2 ^ u + q < k := by
      have : (r + 1) * 2 ^ u ≤ 2 ^ v * 2 ^ u := Nat.mul_le_mul_right _ hr
      rw [Nat.succ_mul] at this; omega
    refine ⟨hlt, ?_⟩
    have hmem : off + r * 2 ^ u + q ∈ List.ofFn (fun q' : Fin (2 ^ u) => off + r * 2 ^ u + q'.val) := by
      simp only [List.mem_ofFn]; exact ⟨⟨q, hq⟩, rfl⟩
    have hbit := List.all_eq_true.mp hall _ hmem
    rw [bitsOf_getD_lt Y _ hlt] at hbit
    exact of_decide_eq_true hbit
  · rintro ⟨r, hr, hall⟩
    refine ⟨r, hr, List.all_eq_true.mpr ?_⟩
    intro w hw
    simp only [List.mem_ofFn] at hw
    obtain ⟨⟨q, hq⟩, rfl⟩ := hw
    obtain ⟨hlt, hmem⟩ := hall q hq
    rw [bitsOf_getD_lt Y _ hlt]
    exact decide_eq_true hmem

lemma literal_copies_1455 (n k : ℕ) (R : Fin n → Fin n → Prop) (S : Finset (Fin n)) (u v : Fin n → ℕ)
    (hRefl : ∀ i, R i i) (hTrans : ∀ i j l, R i j → R j l → R i l)
    (hAnti : ∀ i j, R i j → R j i → i = j)
    (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → Circuit)
    (hMono : ∀ A B, (∀ i j, j ∈ A → R i j → i ∈ A) → (∀ i j, j ∈ B → R i j → i ∈ B) → A ⊆ B → g A ⊆ g B)
    (hValid : ∀ i, FanInTwo (D i) ∧ ReadsBack (k + 2) (D i) ∧ (D i).output < k + 2 + (D i).size)
    (hRec : ∀ A, (∀ i j, j ∈ A → R i j → i ∈ A) → ∀ Y i,
      (Y \ g A).card < 2 ^ (u i) → (g A \ Y).card < 2 ^ (v i) →
      ((D i).wires (bitsOf Y)).getD (D i).output false = decide (i ∈ A))
    (hFast : ∀ i ∈ S, notCount (D i) = 0 ∧ (timesOf k (D i).gates).getD (D i).output 0 ≤ u i + v i) :
    ∃ W : Fin n → Finset (Fin k),
      (∀ i ∈ S, (W i).card = 2 ^ (u i) * 2 ^ (v i) ∧
        ∀ j ∈ W i, ∀ A, (∀ a b, b ∈ A → R a b → a ∈ A) → (j ∈ g A ↔ i ∈ A)) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (W i) (W j) := by
  classical
  have hex : ∀ i : Fin n, i ∈ S →
      ∃ U : Finset (Fin k), U.card = 2 ^ (u i) * 2 ^ (v i) ∧
        ∀ j ∈ U, ∀ A, (∀ a b, b ∈ A → R a b → a ∈ A) → (j ∈ g A ↔ i ∈ A) := by
    intro i hiS
    let Alo : Finset (Fin n) := Finset.univ.filter (fun x => ¬ R i x)
    let Ahi : Finset (Fin n) := Finset.univ.filter (fun x => R x i)
    have hAlo_id : ∀ a b, b ∈ Alo → R a b → a ∈ Alo := by
      intro a b hb hab
      simp only [Alo, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      intro hia; exact hb (hTrans i a b hia hab)
    have hAhi_id : ∀ a b, b ∈ Ahi → R a b → a ∈ Ahi := by
      intro a b hb hab
      simp only [Ahi, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact hTrans a b i hab hb
    have hi_not_Alo : i ∉ Alo := by simp [Alo, hRefl i]
    have hi_in_Ahi : i ∈ Ahi := by simp [Ahi, hRefl i]
    obtain ⟨hFit, hRB, hOut⟩ := hValid i
    obtain ⟨hNot, hDel⟩ := hFast i hiS
    have hm_pos : 0 < 2 ^ (u i) := Nat.pos_of_ne_zero (by positivity)
    have hn_pos : 0 < 2 ^ (v i) := Nat.pos_of_ne_zero (by positivity)
    have hM : ∀ X ⊆ g Ahi \ g Alo, X.card < 2 ^ (u i) →
        ((D i).wires (bitsOf (g Alo ∪ X))).getD (D i).output false = false := by
      intro X _ hc
      have h1 : ((g Alo ∪ X) \ g Alo).card < 2 ^ (u i) := by
        have hsub : (g Alo ∪ X) \ g Alo ⊆ X := by
          intro x hx; simp only [Finset.mem_sdiff, Finset.mem_union] at hx; tauto
        exact Nat.lt_of_le_of_lt (Finset.card_le_card hsub) hc
      have h2 : (g Alo \ (g Alo ∪ X)).card < 2 ^ (v i) := by
        have : g Alo \ (g Alo ∪ X) = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_left
        simp [this, hn_pos]
      rw [hRec Alo hAlo_id (g Alo ∪ X) i h1 h2]; simp [hi_not_Alo]
    have hN : ∀ Y ⊆ g Ahi \ g Alo, Y.card < 2 ^ (v i) →
        ((D i).wires (bitsOf ((g Alo ∪ g Ahi) \ Y))).getD (D i).output false = true := by
      intro Y _ hc
      have h1 : ((g Ahi \ Y) \ g Ahi).card < 2 ^ (u i) := by
        have : (g Ahi \ Y) \ g Ahi = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr Finset.sdiff_subset
        simp [this, hm_pos]
      have h2 : (g Ahi \ (g Ahi \ Y)).card < 2 ^ (v i) := by
        have hsub : g Ahi \ (g Ahi \ Y) ⊆ Y := by
          intro x hx; simp only [Finset.mem_sdiff] at hx; tauto
        exact Nat.lt_of_le_of_lt (Finset.card_le_card hsub) hc
      have htrue : ((D i).wires (bitsOf (g Ahi \ Y))).getD (D i).output false = true := by
        rw [hRec Ahi hAhi_id (g Ahi \ Y) i h1 h2]; simp [hi_in_Ahi]
      exact eval_mono k (D i) hFit hRB hNot (g Ahi \ Y) ((g Alo ∪ g Ahi) \ Y)
        (Finset.sdiff_subset_sdiff Finset.subset_union_right Finset.Subset.rfl)
        (D i).output hOut htrue
    have hfs := fast_exact_support k (D i) hFit hRB hNot (g Alo) (g Ahi)
      (u i + v i) (D i).output hOut hDel (2 ^ (u i)) (2 ^ (v i)) hm_pos hn_pos hM hN
    have hmul : 2 ^ (u i) * 2 ^ (v i) = 2 ^ (u i + v i) := (pow_add 2 (u i) (v i)).symm
    obtain ⟨U, hUsub, hUcard, _, _⟩ := hfs.2 hmul
    refine ⟨U, by rw [hUcard, hmul], ?_⟩
    intro j hjU A hAid
    have hj_mem := Finset.mem_sdiff.mp (hUsub hjU)
    constructor
    · intro hjgA
      by_contra hniA
      have hAsub : A ⊆ Alo := by
        intro x hxA
        simp only [Alo, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hix; exact hniA (hAid i x hxA hix)
      exact hj_mem.2 (hMono A Alo hAid hAlo_id hAsub hjgA)
    · intro hiA
      have hAhisub : Ahi ⊆ A := by
        intro x hxAhi
        simp only [Ahi, Finset.mem_filter, Finset.mem_univ, true_and] at hxAhi
        exact hAid x i hiA hxAhi
      exact hMono Ahi A hAhi_id hAid hAhisub hj_mem.1
  let W : Fin n → Finset (Fin k) := fun i =>
    if h : i ∈ S then Classical.choose (hex i h) else ∅
  refine ⟨W, ?_, ?_⟩
  · intro i hiS
    simp only [W, dif_pos hiS]
    exact Classical.choose_spec (hex i hiS)
  · intro i hiS j hjS hne
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hpi := (Classical.choose_spec (hex i hiS)).2 x (by simpa [W, dif_pos hiS] using hxi)
    have hpj := (Classical.choose_spec (hex j hjS)).2 x (by simpa [W, dif_pos hjS] using hxj)
    by_cases hRij : R i j
    · have hnotRji : ¬ R j i := fun hji => hne (hAnti i j hRij hji)
      let A : Finset (Fin n) := Finset.univ.filter (fun a => R a i)
      have hAid : ∀ a b, b ∈ A → R a b → a ∈ A := by
        intro a b hb hab
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact hTrans a b i hab hb
      have hiA : i ∈ A := by simp [A, hRefl i]
      have hjnotA : j ∉ A := by simp [A, hnotRji]
      exact hjnotA ((hpj A hAid).mp ((hpi A hAid).mpr hiA))
    · let A : Finset (Fin n) := Finset.univ.filter (fun a => R a j)
      have hAid : ∀ a b, b ∈ A → R a b → a ∈ A := by
        intro a b hb hab
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact hTrans a b j hab hb
      have hjA : j ∈ A := by simp [A, hRefl j]
      have hinotA : i ∉ A := by simp [A, hRij]
      exact hinotA ((hpi A hAid).mp ((hpj A hAid).mpr hjA))

lemma lower_bound_1455 (n k : ℕ) (R : Fin n → Fin n → Prop) (S : Finset (Fin n)) (u v : Fin n → ℕ)
    (hRefl : ∀ i, R i i) (hTrans : ∀ i j l, R i j → R j l → R i l)
    (hAnti : ∀ i j, R i j → R j i → i = j)
    (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → Circuit)
    (hMono : ∀ A B, (∀ i j, j ∈ A → R i j → i ∈ A) → (∀ i j, j ∈ B → R i j → i ∈ B) → A ⊆ B → g A ⊆ g B)
    (hValid : ∀ i, FanInTwo (D i) ∧ ReadsBack (k + 2) (D i) ∧ (D i).output < k + 2 + (D i).size)
    (hRec : ∀ A, (∀ i j, j ∈ A → R i j → i ∈ A) → ∀ Y i,
      (Y \ g A).card < 2 ^ (u i) → (g A \ Y).card < 2 ^ (v i) →
      ((D i).wires (bitsOf Y)).getD (D i).output false = decide (i ∈ A))
    (hFast : ∀ i ∈ S, notCount (D i) = 0 ∧ (timesOf k (D i).gates).getD (D i).output 0 ≤ u i + v i) :
    Finset.univ.sum (fun i => if i ∈ S then 2 ^ (u i) * 2 ^ (v i) else 2 ^ (u i) + 2 ^ (v i) - 1) ≤ k := by
  obtain ⟨W, hW, _⟩ := literal_copies_1455 n k R S u v hRefl hTrans hAnti g D hMono hValid hRec hFast
  let cost := fun i => if i ∈ S then 2 ^ (u i) * 2 ^ (v i) else 2 ^ (u i) + 2 ^ (v i) - 1
  suffices h : ∀ m : ℕ, ∀ A : Finset (Fin n),
      (∀ i j, j ∈ A → R i j → i ∈ A) →
      (Finset.univ \ A).card = m →
      (Finset.univ \ A).sum cost ≤ (g Finset.univ \ g A).card by
    have h0 := h (Finset.univ \ (∅ : Finset (Fin n))).card ∅ (by simp) rfl
    simp only [Finset.sdiff_empty] at h0
    calc Finset.univ.sum cost ≤ (g Finset.univ \ g ∅).card := h0
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = k := by simp
  intro m
  induction m with
  | zero =>
    intro A _ hm
    rw [Finset.card_eq_zero.mp hm]; simp
  | succ m ih =>
    intro A hA hm
    have hne : (Finset.univ \ A).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi_mem, hi_min⟩ := poset_minimal R hTrans hAnti (Finset.univ \ A) hne
    have hi_notA : i ∉ A := (Finset.mem_sdiff.mp hi_mem).2
    let A' := insert i A
    have hA' : ∀ a b, b ∈ A' → R a b → a ∈ A' := by
      intro a b hb hab
      rcases Finset.mem_insert.mp hb with rfl | hbA
      · by_cases haA : a ∈ A
        · exact Finset.mem_insert_of_mem haA
        · have ha_eq : a = b := hi_min a (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haA⟩) hab
          rw [ha_eq]; exact Finset.mem_insert_self b A
      · exact Finset.mem_insert_of_mem (hA a b hbA hab)
    have hrem : Finset.univ \ A = insert i (Finset.univ \ A') := by
      ext x; simp only [A', Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hx : x = i
      · subst hx; simp [hi_notA]
      · simp [hx]
    have hi_not_rem' : i ∉ Finset.univ \ A' := by simp [A']
    have hm' : (Finset.univ \ A').card = m := by
      have := Finset.card_insert_of_notMem hi_not_rem'
      rw [← hrem] at this; omega
    have hih := ih A' hA' hm'
    have hsub1 : g A ⊆ g A' := hMono A A' hA hA' (Finset.subset_insert i A)
    have hsub2 : g A' ⊆ g Finset.univ := hMono A' Finset.univ hA' (fun _ _ _ _ => Finset.mem_univ _) (Finset.subset_univ _)
    have hpart : (g Finset.univ \ g A).card = (g Finset.univ \ g A').card + (g A' \ g A).card := by
      have hunion : g Finset.univ \ g A = (g Finset.univ \ g A') ∪ (g A' \ g A) := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hu, hna⟩
          by_cases ha' : x ∈ g A'
          · exact Or.inr ⟨ha', hna⟩
          · exact Or.inl ⟨hu, ha'⟩
        · rintro (⟨hu, hna'⟩ | ⟨ha', hna⟩)
          · exact ⟨hu, fun ha => hna' (hsub1 ha)⟩
          · exact ⟨hsub2 ha', hna⟩
      have hdisj : Disjoint (g Finset.univ \ g A') (g A' \ g A) := by
        rw [Finset.disjoint_left]; intro x h1 h2
        exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    have hstep : cost i ≤ (g A' \ g A).card := by
      by_cases hiS : i ∈ S
      · simp only [cost, hiS, ite_true]
        obtain ⟨hWcard, hWcopy⟩ := hW i hiS
        have hWsub : W i ⊆ g A' \ g A := by
          intro x hx
          refine Finset.mem_sdiff.mpr ⟨(hWcopy x hx A' hA').mpr (Finset.mem_insert_self i A), ?_⟩
          intro hxin; exact hi_notA ((hWcopy x hx A hA).mp hxin)
        rw [← hWcard]; exact Finset.card_le_card hWsub
      · simp only [cost, hiS, ite_false]
        have hp_pos : 1 ≤ 2 ^ (u i) := Nat.one_le_pow _ _ (by omega)
        have hq_pos : 1 ≤ 2 ^ (v i) := Nat.one_le_pow _ _ (by omega)
        have hrecA : ∀ Y, (g A \ Y).card ≤ 2 ^ (v i) - 1 → (Y \ g A).card ≤ 2 ^ (u i) - 1 →
            ((D i).wires (bitsOf Y)).getD (D i).output false = false := by
          intro Y h1 h2
          rw [hRec A hA Y i (by omega) (by omega)]; simp [hi_notA]
        have hrecA' : ∀ Y, (g A' \ Y).card ≤ 2 ^ (v i) - 1 → (Y \ g A').card ≤ 2 ^ (u i) - 1 →
            ((D i).wires (bitsOf Y)).getD (D i).output false = true := by
          intro Y h1 h2
          rw [hRec A' hA' Y i (by omega) (by omega)]; simp [A']
        have hlg := lower_step_general (D i) (g A) (g A') hsub1 hrecA hrecA'
        omega
    rw [hrem, Finset.sum_insert hi_not_rem', hpart, Nat.add_comm (cost i)]
    exact Nat.add_le_add hih hstep

lemma upper_bound_1455 (n k : ℕ) (S : Finset (Fin n)) (u v : Fin n → ℕ)
    (hk : Finset.univ.sum (fun i => if i ∈ S then 2 ^ (u i) * 2 ^ (v i) else 2 ^ (u i) + 2 ^ (v i) - 1) ≤ k) :
    ∃ (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → Circuit),
      (∀ A B, A ⊆ B → g A ⊆ g B) ∧
      (∀ i, FanInTwo (D i) ∧ ReadsBack (k + 2) (D i) ∧ (D i).output < k + 2 + (D i).size) ∧
      (∀ A Y i, (Y \ g A).card < 2 ^ (u i) → (g A \ Y).card < 2 ^ (v i) →
        ((D i).wires (bitsOf Y)).getD (D i).output false = decide (i ∈ A)) ∧
      (∀ i ∈ S, notCount (D i) = 0 ∧ (timesOf k (D i).gates).getD (D i).output 0 ≤ u i + v i) := by
  classical
  let cost := fun i => if i ∈ S then 2 ^ (u i) * 2 ^ (v i) else 2 ^ (u i) + 2 ^ (v i) - 1
  let off := fun i : Fin n => ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), cost j
  have hoff_le : ∀ i : Fin n, off i + cost i ≤ k := fun i => (prefix_sum_offset cost i).trans hk
  let pin : Fin k → Option (Fin n) := fun j =>
    (Finset.univ.filter fun i : Fin n => off i ≤ j.val ∧ j.val < off i + cost i).toList.head?
  have hpin_eq : ∀ (i : Fin n) (j : Fin k), pin j = some i ↔ off i ≤ j.val ∧ j.val < off i + cost i := by
    intro i j
    have huniq : ∀ i1 i2 : Fin n,
        (off i1 ≤ j.val ∧ j.val < off i1 + cost i1) →
        (off i2 ≤ j.val ∧ j.val < off i2 + cost i2) → i1 = i2 := by
      intro i1 i2 h1 h2
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · have hd : off i1 + cost i1 ≤ off i2 := prefix_sum_disjoint cost i1 i2 hlt; omega
      · have hd : off i2 + cost i2 ≤ off i1 := prefix_sum_disjoint cost i2 i1 hgt; omega
    let F := Finset.univ.filter fun i' : Fin n => off i' ≤ j.val ∧ j.val < off i' + cost i'
    constructor
    · intro hp
      have hmem : i ∈ F.toList := List.mem_of_head? hp
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hmem)).2
    · intro hrange
      have hF : F = {i} := by
        ext i'
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => huniq i' i h hrange, fun h => h ▸ hrange⟩
      show F.toList.head? = some i
      rw [hF]; simp
  let g : Finset (Fin n) → Finset (Fin k) := fun A =>
    Finset.univ.filter fun j : Fin k => ∃ i ∈ A, pin j = some i
  let D : Fin n → Circuit := fun i =>
    if i ∈ S then buildBalDNF k (off i) (u i) (v i)
    else buildThresh k (off i) (2 ^ (u i) + 2 ^ (v i) - 1) (2 ^ (u i) - 1)
  refine ⟨g, D, ?_, ?_, ?_, ?_⟩
  · intro A B hAB j hj
    simp only [g, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨i, hiA, hp⟩ := hj
    exact ⟨i, hAB hiA, hp⟩
  · intro i
    by_cases hiS : i ∈ S
    · have hc : off i + 2 ^ (u i) * 2 ^ (v i) ≤ k := by simpa [cost, hiS] using hoff_le i
      have hsp := buildBalDNF_spec k (off i) (u i) (v i) hc
      simp only [D, hiS, ite_true]
      exact ⟨hsp.1, hsp.2.1, hsp.2.2.1⟩
    · have hp_pos : 1 ≤ 2 ^ (u i) := Nat.one_le_pow _ _ (by omega)
      have hq_pos : 1 ≤ 2 ^ (v i) := Nat.one_le_pow _ _ (by omega)
      have hc : off i + (2 ^ (u i) + 2 ^ (v i) - 1) ≤ k := by simpa [cost, hiS] using hoff_le i
      have hsp := buildThresh_spec k (off i) (2 ^ (u i) + 2 ^ (v i) - 1) (2 ^ (u i) - 1) hc (by omega)
      simp only [D, hiS, ite_false]
      exact ⟨hsp.1, hsp.2.1, hsp.2.2.1⟩
  · intro A Y i hgain hloss
    have hblock_in : ∀ (d : ℕ) (hd : d < cost i) (hlt : off i + d < k),
        (⟨off i + d, hlt⟩ : Fin k) ∈ g A ↔ i ∈ A := by
      intro d hd hlt
      simp only [g, Finset.mem_filter, Finset.mem_univ, true_and]
      have hp : pin ⟨off i + d, hlt⟩ = some i :=
        (hpin_eq i ⟨off i + d, hlt⟩).mpr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hd _⟩
      constructor
      · rintro ⟨i', hi'A, hp'⟩
        rw [hp] at hp'; cases hp'; exact hi'A
      · intro hiA; exact ⟨i, hiA, hp⟩
    by_cases hiS : i ∈ S
    · have hcost : cost i = 2 ^ (u i) * 2 ^ (v i) := by simp [cost, hiS]
      have hc : off i + 2 ^ (u i) * 2 ^ (v i) ≤ k := by simpa [hcost] using hoff_le i
      have hsp := buildBalDNF_spec k (off i) (u i) (v i) hc
      simp only [D, hiS, ite_true]
      rw [hsp.2.2.2.2.2 Y]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨r, hr, hall⟩
        by_contra hniA
        let grp : Finset (Fin k) := (Finset.range (2 ^ (u i))).attach.image fun ⟨q, hq⟩ =>
          ⟨off i + r * 2 ^ (u i) + q, by
            have hq' := Finset.mem_range.mp hq
            have : (r + 1) * 2 ^ (u i) ≤ 2 ^ (v i) * 2 ^ (u i) := Nat.mul_le_mul_right _ hr
            rw [Nat.succ_mul] at this
            rw [Nat.mul_comm] at hc; omega⟩
        have hgrp_card : grp.card = 2 ^ (u i) := by
          rw [Finset.card_image_of_injective]
          · simp
          · intro ⟨q1, _⟩ ⟨q2, _⟩ h
            have := congrArg Fin.val h; simp at this; ext; omega
        have hgrp_sub : grp ⊆ Y \ g A := by
          intro x hx
          simp only [grp, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx
          obtain ⟨q, hq, rfl⟩ := hx
          have hq' := Finset.mem_range.mp hq
          obtain ⟨hlt, hmemY⟩ := hall q hq'
          refine Finset.mem_sdiff.mpr ⟨hmemY, ?_⟩
          have hd : r * 2 ^ (u i) + q < cost i := by
            have hmulc : 2 ^ (v i) * 2 ^ (u i) = 2 ^ (u i) * 2 ^ (v i) := Nat.mul_comm _ _
            have : (r + 1) * 2 ^ (u i) ≤ 2 ^ (v i) * 2 ^ (u i) := Nat.mul_le_mul_right _ hr
            rw [Nat.succ_mul] at this; omega
          have hmemA := hblock_in (r * 2 ^ (u i) + q) hd (by omega)
          have heq : (⟨off i + r * 2 ^ (u i) + q, hlt⟩ : Fin k) = ⟨off i + (r * 2 ^ (u i) + q), by omega⟩ := by
            ext; simp [Nat.add_assoc]
          rw [heq, hmemA]; exact hniA
        have := Finset.card_le_card hgrp_sub
        omega
      · intro hiA
        by_contra hno
        push Not at hno
        have hpick : ∀ r ∈ Finset.range (2 ^ (v i)),
            ∃ q < 2 ^ (u i), ∃ hlt : off i + r * 2 ^ (u i) + q < k,
              (⟨off i + r * 2 ^ (u i) + q, hlt⟩ : Fin k) ∈ g A \ Y := by
          intro r hr
          have hr' := Finset.mem_range.mp hr
          obtain ⟨q, hq, hnotY⟩ := hno r hr'
          have hd : r * 2 ^ (u i) + q < cost i := by
            have hmulc : 2 ^ (v i) * 2 ^ (u i) = 2 ^ (u i) * 2 ^ (v i) := Nat.mul_comm _ _
            have : (r + 1) * 2 ^ (u i) ≤ 2 ^ (v i) * 2 ^ (u i) := Nat.mul_le_mul_right _ hr'
            rw [Nat.succ_mul] at this; omega
          have hlt : off i + r * 2 ^ (u i) + q < k := by omega
          refine ⟨q, hq, hlt, Finset.mem_sdiff.mpr ⟨?_, fun h => hnotY hlt h⟩⟩
          have hmemA := (hblock_in (r * 2 ^ (u i) + q) hd (by omega)).mpr hiA
          have heq : (⟨off i + r * 2 ^ (u i) + q, hlt⟩ : Fin k) = ⟨off i + (r * 2 ^ (u i) + q), by omega⟩ := by
            ext; simp [Nat.add_assoc]
          rwa [heq]
        choose qf hqf hltf hmemf using hpick
        let lostS : Finset (Fin k) := (Finset.range (2 ^ (v i))).attach.image fun ⟨r, hr⟩ =>
          ⟨off i + r * 2 ^ (u i) + qf r hr, hltf r hr⟩
        have hcardL : lostS.card = 2 ^ (v i) := by
          rw [Finset.card_image_of_injective]
          · simp
          · intro ⟨r1, hr1⟩ ⟨r2, hr2⟩ heq
            have hval := congrArg Fin.val heq
            simp only at hval
            have hq1 := hqf r1 hr1
            have hq2 := hqf r2 hr2
            have hreq : r1 = r2 := by
              by_contra hne
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · have : (r1 + 1) * 2 ^ (u i) ≤ r2 * 2 ^ (u i) := Nat.mul_le_mul_right _ hlt
                rw [Nat.succ_mul] at this; omega
              · have : (r2 + 1) * 2 ^ (u i) ≤ r1 * 2 ^ (u i) := Nat.mul_le_mul_right _ hgt
                rw [Nat.succ_mul] at this; omega
            ext; exact hreq
        have hsubL : lostS ⊆ g A \ Y := by
          intro x hx
          simp only [lostS, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx
          obtain ⟨r, hr, rfl⟩ := hx
          exact hmemf r hr
        have := Finset.card_le_card hsubL
        omega
    · have hp_pos : 1 ≤ 2 ^ (u i) := Nat.one_le_pow _ _ (by omega)
      have hq_pos : 1 ≤ 2 ^ (v i) := Nat.one_le_pow _ _ (by omega)
      let t := 2 ^ (u i) + 2 ^ (v i) - 1
      have hcost : cost i = t := by simp [cost, t, hiS]
      have hc : off i + t ≤ k := by simpa [hcost] using hoff_le i
      have hsp := buildThresh_spec k (off i) t (2 ^ (u i) - 1) hc (by omega)
      simp only [D, hiS, ite_false]
      rw [hsp.2.2.2.2.2 Y]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      let hit := (Finset.range t).filter fun j =>
        ∃ hlt : off i + j < k, (⟨off i + j, hlt⟩ : Fin k) ∈ Y
      change (2 ^ (u i) - 1 + 1 ≤ hit.card) ↔ i ∈ A
      constructor
      · intro hhit
        by_contra hniA
        let hitPins : Finset (Fin k) := hit.attach.image fun ⟨j, hj⟩ =>
          ⟨off i + j, by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega⟩
        have hcard : hitPins.card = hit.card := by
          rw [Finset.card_image_of_injective]
          · simp
          · intro ⟨j1, _⟩ ⟨j2, _⟩ h; have := congrArg Fin.val h; simp at this; ext; omega
        have hsub : hitPins ⊆ Y \ g A := by
          intro x hx
          simp only [hitPins, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          have hjf := Finset.mem_filter.mp hj
          obtain ⟨hlt, hmemY⟩ := hjf.2
          refine Finset.mem_sdiff.mpr ⟨hmemY, ?_⟩
          rw [hblock_in j (by rw [hcost]; exact Finset.mem_range.mp hjf.1) hlt]; exact hniA
        have := Finset.card_le_card hsub
        omega
      · intro hiA
        let miss := (Finset.range t) \ hit
        have hpart : hit.card + miss.card = t := by
          have := Finset.card_sdiff_add_card_eq_card
            (Finset.filter_subset (fun j => ∃ hlt : off i + j < k, (⟨off i + j, hlt⟩ : Fin k) ∈ Y) (Finset.range t))
          simp only [Finset.card_range] at this
          change miss.card + hit.card = t at this
          omega
        let missPins : Finset (Fin k) := miss.attach.image fun ⟨j, hj⟩ =>
          ⟨off i + j, by have := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1; omega⟩
        have hcard : missPins.card = miss.card := by
          rw [Finset.card_image_of_injective]
          · simp
          · intro ⟨j1, _⟩ ⟨j2, _⟩ h; have := congrArg Fin.val h; simp at this; ext; omega
        have hsub : missPins ⊆ g A \ Y := by
          intro x hx
          simp only [missPins, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          have hjm := Finset.mem_sdiff.mp hj
          have hjt := Finset.mem_range.mp hjm.1
          have hlt : off i + j < k := by omega
          refine Finset.mem_sdiff.mpr ⟨(hblock_in j (by rw [hcost]; exact hjt) hlt).mpr hiA, ?_⟩
          intro hmemY
          exact hjm.2 (Finset.mem_filter.mpr ⟨hjm.1, hlt, hmemY⟩)
        have := Finset.card_le_card hsub
        omega
  · intro i hiS
    have hc : off i + 2 ^ (u i) * 2 ^ (v i) ≤ k := by simpa [cost, hiS] using hoff_le i
    have hsp := buildBalDNF_spec k (off i) (u i) (v i) hc
    simp only [D, hiS, ite_true]
    exact ⟨hsp.2.2.2.1, hsp.2.2.2.2.1⟩

end PEqualNP.Outside.L_lib_1455_aux

theorem PEqualNP.Outside.L_lib_1455 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) D ∧ D.output < k+2+D.size
let run := fun {k : Nat} (D : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin k)) =>
  ((D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true])).getD D.output false)
let delay := fun (k c e : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let times := D.gates.foldl (fun (ts : List Nat) g =>
    let mx := g.inputs.foldl (fun v j => max v (ts.getD j 0)) 0
    ts ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then ((g.inputs.head?.map (fun j => ts.getD j 0)).getD 0)
      else mx+(if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then c else e)]) (List.replicate (k+2) 0)
  times.getD D.output 0
∀ (n k : Nat) (R : Fin n → Fin n → Prop) (S : Finset (Fin n)) (u v : Fin n → Nat),
  (∀ i, R i i) → (∀ i j l, R i j → R j l → R i l) → (∀ i j, R i j → R j i → i=j) →
  let ideal := fun (A : Finset (Fin n)) => ∀ i j, j ∈ A → R i j → i ∈ A
  let p := fun i => 2^(u i)
  let q := fun i => 2^(v i)
  let mono := fun (g : Finset (Fin n) → Finset (Fin k)) => ∀ A B, ideal A → ideal B → A ⊆ B → g A ⊆ g B
  let recovers := fun (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ i, valid k (D i)) ∧ ∀ A, ideal A → ∀ Y i, (Y \ g A).card < p i → (g A \ Y).card < q i →
      run (D i) Y=decide (i ∈ A)
  let fast := fun (D : Fin n → PEqualNP.CircuitLowerBounds.Circuit) => ∀ i ∈ S, PEqualNP.NotBracket.notCount (D i)=0 ∧ delay k 1 1 (D i) ≤ u i+v i
  let cost := fun i => if i ∈ S then p i*q i else p i+q i-1
  (∀ g D, mono g → recovers g D → fast D →
    ∃ W : Fin n → Finset (Fin k), (∀ i ∈ S, (W i).card=p i*q i ∧
      ∀ j ∈ W i, ∀ A, ideal A → (j ∈ g A ↔ i ∈ A)) ∧
      ∀ i ∈ S, ∀ j ∈ S, i≠j → Disjoint (W i) (W j)) ∧
  ((∃ g D, mono g ∧ recovers g D ∧ fast D) ↔ Finset.univ.sum cost ≤ k)) := by
  dsimp only
  intro n k R S u v hRefl hTrans hAnti
  have hbits : ∀ (Y : Finset (Fin k)),
      List.ofFn (fun j : Fin k => @decide (j ∈ Y) (Classical.propDecidable _)) ++ [false, true] =
      PEqualNP.Outside.L_lib_1455_aux.bitsOf Y := by
    intro Y
    unfold PEqualNP.Outside.L_lib_1455_aux.bitsOf
    congr 1; apply List.ext_getElem <;> simp
  have hdec : ∀ (P : Prop) [Decidable P], @decide P (Classical.propDecidable P) = decide P := by
    intro P _; by_cases h : P <;> simp [h]
  have hsdiff : ∀ (A B : Finset (Fin k)),
      @SDiff.sdiff (Finset (Fin k)) (@Finset.instSDiff (Fin k) (fun a b => Classical.propDecidable (a = b))) A B = A \ B := by
    intro A B; ext x
    simp only [Finset.mem_sdiff]
  have hsum :
      Finset.univ.sum (fun i => @ite ℕ (i ∈ S) (Classical.propDecidable _) (2 ^ (u i) * 2 ^ (v i)) (2 ^ (u i) + 2 ^ (v i) - 1)) =
      Finset.univ.sum (fun i => if i ∈ S then 2 ^ (u i) * 2 ^ (v i) else 2 ^ (u i) + 2 ^ (v i) - 1) := by
    apply Finset.sum_congr rfl; intro i _; by_cases h : i ∈ S <;> simp [h]
  have hdelay : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      (D.gates.foldl (fun (ts : List ℕ) g =>
        let mx := g.inputs.foldl (fun v j => max v (ts.getD j 0)) 0
        ts ++ [@ite ℕ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _)
          ((g.inputs.head?.map (fun j => ts.getD j 0)).getD 0)
          (mx + @ite ℕ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and) (Classical.propDecidable _) 1 1)])
        (List.replicate (k + 2) 0)).getD D.output 0 =
      (PEqualNP.Outside.L_lib_1455_aux.timesOf k D.gates).getD D.output 0 := by
    intro D
    congr 1
    unfold PEqualNP.Outside.L_lib_1455_aux.timesOf
    congr 1
    funext ts g
    unfold PEqualNP.Outside.L_lib_1455_aux.delayStep
    cases g.op <;> simp
  constructor
  · intro g D hMono hRec hFast
    have hRec' : ∀ A, (∀ i j, j ∈ A → R i j → i ∈ A) → ∀ Y i,
        (Y \ g A).card < 2 ^ (u i) → (g A \ Y).card < 2 ^ (v i) →
        ((D i).wires (PEqualNP.Outside.L_lib_1455_aux.bitsOf Y)).getD (D i).output false = decide (i ∈ A) := by
      intro A hA Y i h1 h2
      have h := hRec.2 A hA Y i (by simpa only [hsdiff] using h1) (by simpa only [hsdiff] using h2)
      rw [hbits, hdec] at h; exact h
    have hFast' : ∀ i ∈ S, PEqualNP.NotBracket.notCount (D i) = 0 ∧
        (PEqualNP.Outside.L_lib_1455_aux.timesOf k (D i).gates).getD (D i).output 0 ≤ u i + v i := by
      intro i hiS
      obtain ⟨hn, hd⟩ := hFast i hiS
      exact ⟨hn, by simpa only [hdelay] using hd⟩
    exact PEqualNP.Outside.L_lib_1455_aux.literal_copies_1455 n k R S u v hRefl hTrans hAnti g D hMono hRec.1 hRec' hFast'
  · constructor
    · rintro ⟨g, D, hMono, hRec, hFast⟩
      have hRec' : ∀ A, (∀ i j, j ∈ A → R i j → i ∈ A) → ∀ Y i,
          (Y \ g A).card < 2 ^ (u i) → (g A \ Y).card < 2 ^ (v i) →
          ((D i).wires (PEqualNP.Outside.L_lib_1455_aux.bitsOf Y)).getD (D i).output false = decide (i ∈ A) := by
        intro A hA Y i h1 h2
        have h := hRec.2 A hA Y i (by simpa only [hsdiff] using h1) (by simpa only [hsdiff] using h2)
        rw [hbits, hdec] at h; exact h
      have hFast' : ∀ i ∈ S, PEqualNP.NotBracket.notCount (D i) = 0 ∧
          (PEqualNP.Outside.L_lib_1455_aux.timesOf k (D i).gates).getD (D i).output 0 ≤ u i + v i := by
        intro i hiS
        obtain ⟨hn, hd⟩ := hFast i hiS
        exact ⟨hn, by simpa only [hdelay] using hd⟩
      have hlb := PEqualNP.Outside.L_lib_1455_aux.lower_bound_1455 n k R S u v hRefl hTrans hAnti g D hMono hRec.1 hRec' hFast'
      simpa only [hsum] using hlb
    · intro hk
      have hk' : Finset.univ.sum (fun i => if i ∈ S then 2 ^ (u i) * 2 ^ (v i) else 2 ^ (u i) + 2 ^ (v i) - 1) ≤ k := by
        simpa only [hsum] using hk
      obtain ⟨g, D, hMono, hValid, hRec, hFast⟩ := PEqualNP.Outside.L_lib_1455_aux.upper_bound_1455 n k S u v hk'
      refine ⟨g, D, fun A B _ _ hAB => hMono A B hAB, ⟨hValid, ?_⟩, ?_⟩
      · intro A _ Y i h1 h2
        have h := hRec A Y i (by simpa only [hsdiff] using h1) (by simpa only [hsdiff] using h2)
        rw [hbits, hdec]; exact h
      · intro i hiS
        obtain ⟨hn, hd⟩ := hFast i hiS
        exact ⟨hn, by simpa only [hdelay] using hd⟩
