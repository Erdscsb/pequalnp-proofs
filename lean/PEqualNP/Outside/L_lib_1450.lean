import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1450_aux

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

section ReadOnceLower

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

def supp (k : ℕ) (D : Circuit) (w : ℕ) : Finset (Fin k) :=
  if hw : w < k then {⟨w, hw⟩}
  else if w < k + 2 + D.gates.length ∧ k + 2 ≤ w then
    ((gateAt D (w - (k + 2))).inputs.attach.map fun ⟨i, _⟩ =>
      if i < w then supp k D i else ∅).foldr (· ∪ ·) ∅
  else ∅
termination_by w

def gcone (k : ℕ) (D : Circuit) (w : ℕ) : Finset ℕ :=
  if w < k + 2 + D.gates.length ∧ k + 2 ≤ w then
    let j := w - (k + 2)
    insert j (((gateAt D j).inputs.attach.map fun ⟨i, _⟩ =>
      if i < w then gcone k D i else ∅).foldr (· ∪ ·) ∅)
  else ∅
termination_by w

lemma supp_lt_k (k : ℕ) (D : Circuit) (w : ℕ) (hw : w < k) : supp k D w = {⟨w, hw⟩} := by
  rw [supp]; simp [hw]

lemma supp_gate (k : ℕ) (D : Circuit) (hRB : ReadsBack (k + 2) D) (j : ℕ) (hj : j < D.gates.length) :
    supp k D (k + 2 + j) = ((gateAt D j).inputs.map (supp k D)).foldr (· ∪ ·) ∅ := by
  rw [supp]
  have h1 : ¬ (k + 2 + j < k) := by omega
  have h2 : k + 2 + j < k + 2 + D.gates.length ∧ k + 2 ≤ k + 2 + j := by omega
  simp only [h1, dite_false, h2, and_self, ite_true, Nat.add_sub_cancel_left]
  congr 1
  apply List.ext_getElem
  · simp
  · intro idx h1' h2'
    have hidx : idx < (gateAt D j).inputs.length := by simpa using h2'
    simp only [List.getElem_map, List.getElem_attach]
    have hmem : (gateAt D j).inputs[idx]'hidx ∈ (gateAt D j).inputs := List.getElem_mem hidx
    have hilt : (gateAt D j).inputs[idx]'hidx < k + 2 + j := hRB j hj _ hmem
    simp [hilt]

lemma gcone_gate (k : ℕ) (D : Circuit) (hRB : ReadsBack (k + 2) D) (j : ℕ) (hj : j < D.gates.length) :
    gcone k D (k + 2 + j) = insert j (((gateAt D j).inputs.map (gcone k D)).foldr (· ∪ ·) ∅) := by
  rw [gcone]
  have h2 : k + 2 + j < k + 2 + D.gates.length ∧ k + 2 ≤ k + 2 + j := by omega
  simp only [h2, and_self, ite_true, Nat.add_sub_cancel_left]
  congr 2
  apply List.ext_getElem
  · simp
  · intro idx h1' h2'
    have hidx : idx < (gateAt D j).inputs.length := by simpa using h2'
    simp only [List.getElem_map, List.getElem_attach]
    have hmem : (gateAt D j).inputs[idx]'hidx ∈ (gateAt D j).inputs := List.getElem_mem hidx
    have hilt : (gateAt D j).inputs[idx]'hidx < k + 2 + j := hRB j hj _ hmem
    simp [hilt]

lemma foldr_union_mem {α : Type*} [DecidableEq α] (l : List (Finset α)) (x : α) :
    x ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ l, x ∈ s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Finset.mem_union, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨s, hs, hx⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨s, Or.inr hs, hx⟩
    · rintro ⟨s, rfl | hs, hx⟩
      · exact Or.inl hx
      · exact Or.inr ⟨s, hs, hx⟩

lemma gcone_subset_range (k : ℕ) (D : Circuit) (hRB : ReadsBack (k + 2) D) :
    ∀ w, gcone k D w ⊆ Finset.range D.gates.length := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    by_cases hlt : w < k + 2 + D.gates.length ∧ k + 2 ≤ w
    · obtain ⟨h1, h2⟩ := hlt
      set j := w - (k + 2)
      have hj : j < D.gates.length := by omega
      have hw : w = k + 2 + j := by omega
      rw [hw, gcone_gate k D hRB j hj]
      intro g hg
      simp only [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · exact Finset.mem_range.mpr hj
      · rw [foldr_union_mem] at hg
        obtain ⟨s, hs, hgs⟩ := hg
        rw [List.mem_map] at hs
        obtain ⟨i, hi, rfl⟩ := hs
        have hilt : i < w := by rw [hw]; exact hRB j hj i hi
        exact ih i hilt hgs
    · rw [gcone]; simp [hlt]

lemma gcone_lt (k : ℕ) (D : Circuit) (hRB : ReadsBack (k + 2) D) :
    ∀ w g, g ∈ gcone k D w → k + 2 + g ≤ w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro g hg
    by_cases hlt : w < k + 2 + D.gates.length ∧ k + 2 ≤ w
    · obtain ⟨h1, h2⟩ := hlt
      set j := w - (k + 2)
      have hj : j < D.gates.length := by omega
      have hw : w = k + 2 + j := by omega
      rw [hw, gcone_gate k D hRB j hj] at hg
      simp only [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · omega
      · rw [foldr_union_mem] at hg
        obtain ⟨s, hs, hgs⟩ := hg
        rw [List.mem_map] at hs
        obtain ⟨i, hi, rfl⟩ := hs
        have hilt : i < w := by rw [hw]; exact hRB j hj i hi
        have := ih i hilt g hgs
        omega
    · rw [gcone] at hg; simp [hlt] at hg

lemma supp_read_in_gcone (k : ℕ) (D : Circuit) (hRB : ReadsBack (k + 2) D) :
    ∀ w (x : Fin k), x ∈ supp k D w → x.val = w ∨ 1 ≤ readsIn D (gcone k D w) x.val := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro x hx
    by_cases hwk : w < k
    · rw [supp_lt_k k D w hwk] at hx
      simp only [Finset.mem_singleton] at hx
      left; rw [hx]
    · by_cases hlt : w < k + 2 + D.gates.length ∧ k + 2 ≤ w
      · obtain ⟨h1, h2⟩ := hlt
        set j := w - (k + 2)
        have hj : j < D.gates.length := by omega
        have hw : w = k + 2 + j := by omega
        rw [hw, supp_gate k D hRB j hj, foldr_union_mem] at hx
        obtain ⟨s, hs, hxs⟩ := hx
        rw [List.mem_map] at hs
        obtain ⟨i, hi, rfl⟩ := hs
        have hilt : i < w := by rw [hw]; exact hRB j hj i hi
        rcases ih i hilt x hxs with hxi | hread
        · right
          have hjmem : j ∈ gcone k D w := by
            rw [hw, gcone_gate k D hRB j hj]; exact Finset.mem_insert_self _ _
          have hcnt : 1 ≤ (gateAt D j).inputs.count x.val := by
            rw [hxi]; exact List.count_pos_iff.mpr hi
          calc 1 ≤ (gateAt D j).inputs.count x.val := hcnt
            _ ≤ ∑ g ∈ gcone k D w, (gateAt D g).inputs.count x.val :=
              Finset.single_le_sum (f := fun g => (gateAt D g).inputs.count x.val)
                (fun _ _ => Nat.zero_le _) hjmem
        · right
          have hsub : gcone k D i ⊆ gcone k D w := by
            intro g hg
            rw [hw, gcone_gate k D hRB j hj]
            apply Finset.mem_insert_of_mem
            rw [foldr_union_mem]
            exact ⟨gcone k D i, List.mem_map.mpr ⟨i, hi, rfl⟩, hg⟩
          calc 1 ≤ readsIn D (gcone k D i) x.val := hread
            _ ≤ readsIn D (gcone k D w) x.val :=
              Finset.sum_le_sum_of_subset hsub
      · rw [supp] at hx; simp [hwk, hlt] at hx

lemma gcone_read_in_gcone (k : ℕ) (D : Circuit) (hRB : ReadsBack (k + 2) D) :
    ∀ w g, g ∈ gcone k D w → k + 2 + g = w ∨ 1 ≤ readsIn D (gcone k D w) (k + 2 + g) := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro g hg
    by_cases hlt : w < k + 2 + D.gates.length ∧ k + 2 ≤ w
    · obtain ⟨h1, h2⟩ := hlt
      set j := w - (k + 2)
      have hj : j < D.gates.length := by omega
      have hw : w = k + 2 + j := by omega
      rw [hw, gcone_gate k D hRB j hj] at hg
      simp only [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · left; exact hw.symm
      · rw [foldr_union_mem] at hg
        obtain ⟨s, hs, hgs⟩ := hg
        rw [List.mem_map] at hs
        obtain ⟨i, hi, rfl⟩ := hs
        have hilt : i < w := by rw [hw]; exact hRB j hj i hi
        rcases ih i hilt g hgs with hgi | hread
        · right
          have hjmem : j ∈ gcone k D w := by
            rw [hw, gcone_gate k D hRB j hj]; exact Finset.mem_insert_self _ _
          have hcnt : 1 ≤ (gateAt D j).inputs.count (k + 2 + g) := by
            rw [hgi]; exact List.count_pos_iff.mpr hi
          calc 1 ≤ (gateAt D j).inputs.count (k + 2 + g) := hcnt
            _ ≤ ∑ g' ∈ gcone k D w, (gateAt D g').inputs.count (k + 2 + g) :=
              Finset.single_le_sum (f := fun g' => (gateAt D g').inputs.count (k + 2 + g))
                (fun _ _ => Nat.zero_le _) hjmem
        · right
          have hsub : gcone k D i ⊆ gcone k D w := by
            intro g' hg'
            rw [hw, gcone_gate k D hRB j hj]
            apply Finset.mem_insert_of_mem
            rw [foldr_union_mem]
            exact ⟨gcone k D i, List.mem_map.mpr ⟨i, hi, rfl⟩, hg'⟩
          calc 1 ≤ readsIn D (gcone k D i) (k + 2 + g) := hread
            _ ≤ readsIn D (gcone k D w) (k + 2 + g) :=
              Finset.sum_le_sum_of_subset hsub
    · rw [gcone] at hg; simp [hlt] at hg

lemma tree_disjoint_gcone (k : ℕ) (D : Circuit) (hRB : ReadsBack (k + 2) D)
    (hTree : ∀ w < k + 2 + D.gates.length, readsIn D (Finset.range D.gates.length) w +
      (if D.output = w then 1 else 0) ≤ 1)
    {j : ℕ} (hj : j < D.gates.length) {u v : ℕ}
    (hinp : (gateAt D j).inputs = [u, v]) :
    Disjoint (gcone k D u) (gcone k D v) := by
  rw [Finset.disjoint_left]
  intro g hgu hgv
  have hu_lt : u < k + 2 + j := hRB j hj u (by simp [hinp])
  have hv_lt : v < k + 2 + j := hRB j hj v (by simp [hinp])
  have hne : (gcone k D u ∩ gcone k D v).Nonempty := ⟨g, Finset.mem_inter.mpr ⟨hgu, hgv⟩⟩
  let m := (gcone k D u ∩ gcone k D v).max' hne
  have hm : m ∈ gcone k D u ∩ gcone k D v := Finset.max'_mem _ hne
  have hmu : m ∈ gcone k D u := (Finset.mem_inter.mp hm).1
  have hmv : m ∈ gcone k D v := (Finset.mem_inter.mp hm).2
  have hm_lt : m < D.gates.length := Finset.mem_range.mp (gcone_subset_range k D hRB u hmu)
  have hbound : readsIn D (Finset.range D.gates.length) (k + 2 + m) ≤ 1 := by
    have := hTree (k + 2 + m) (by omega); omega
  have hru := gcone_read_in_gcone k D hRB u m hmu
  have hrv := gcone_read_in_gcone k D hRB v m hmv
  have hj_not_u : j ∉ gcone k D u := fun h => by have := gcone_lt k D hRB u j h; omega
  have hj_not_v : j ∉ gcone k D v := fun h => by have := gcone_lt k D hRB v j h; omega
  rcases hru with hmu_eq | hru_pos
  · rcases hrv with hmv_eq | hrv_pos
    · have hcnt : (gateAt D j).inputs.count (k + 2 + m) = 2 := by
        simp [hinp, ← hmu_eq, ← hmv_eq]
      have : 2 ≤ readsIn D (Finset.range D.gates.length) (k + 2 + m) := by
        calc 2 = (gateAt D j).inputs.count (k + 2 + m) := hcnt.symm
          _ ≤ readsIn D (Finset.range D.gates.length) (k + 2 + m) :=
            Finset.single_le_sum (f := fun g' => (gateAt D g').inputs.count (k + 2 + m))
              (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
      omega
    · have hsub : insert j (gcone k D v) ⊆ Finset.range D.gates.length := by
        intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_range.mpr hj
        · exact gcone_subset_range k D hRB v hx
      have hcnt : 1 ≤ (gateAt D j).inputs.count (k + 2 + m) := by
        rw [hmu_eq]; exact List.count_pos_iff.mpr (by simp [hinp])
      have : 2 ≤ readsIn D (Finset.range D.gates.length) (k + 2 + m) := by
        calc 2 ≤ (gateAt D j).inputs.count (k + 2 + m) + readsIn D (gcone k D v) (k + 2 + m) := by omega
          _ = readsIn D (insert j (gcone k D v)) (k + 2 + m) := by
            unfold readsIn; rw [Finset.sum_insert hj_not_v]
          _ ≤ readsIn D (Finset.range D.gates.length) (k + 2 + m) :=
            Finset.sum_le_sum_of_subset hsub
      omega
  · rcases hrv with hmv_eq | hrv_pos
    · have hsub : insert j (gcone k D u) ⊆ Finset.range D.gates.length := by
        intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_range.mpr hj
        · exact gcone_subset_range k D hRB u hx
      have hcnt : 1 ≤ (gateAt D j).inputs.count (k + 2 + m) := by
        rw [hmv_eq]; exact List.count_pos_iff.mpr (by simp [hinp])
      have : 2 ≤ readsIn D (Finset.range D.gates.length) (k + 2 + m) := by
        calc 2 ≤ (gateAt D j).inputs.count (k + 2 + m) + readsIn D (gcone k D u) (k + 2 + m) := by omega
          _ = readsIn D (insert j (gcone k D u)) (k + 2 + m) := by
            unfold readsIn; rw [Finset.sum_insert hj_not_u]
          _ ≤ readsIn D (Finset.range D.gates.length) (k + 2 + m) :=
            Finset.sum_le_sum_of_subset hsub
      omega
    · have hne_u : ∃ g1 ∈ gcone k D u, 1 ≤ (gateAt D g1).inputs.count (k + 2 + m) := by
        by_contra hall
        push_neg at hall
        have hzero : readsIn D (gcone k D u) (k + 2 + m) = 0 :=
          Finset.sum_eq_zero fun x hx => Nat.lt_one_iff.mp (hall x hx)
        omega
      have hne_v : ∃ g2 ∈ gcone k D v, 1 ≤ (gateAt D g2).inputs.count (k + 2 + m) := by
        by_contra hall
        push_neg at hall
        have hzero : readsIn D (gcone k D v) (k + 2 + m) = 0 :=
          Finset.sum_eq_zero fun x hx => Nat.lt_one_iff.mp (hall x hx)
        omega
      obtain ⟨g1, hg1u, hc1⟩ := hne_u
      obtain ⟨g2, hg2v, hc2⟩ := hne_v
      have hg1_lt : g1 < D.gates.length := Finset.mem_range.mp (gcone_subset_range k D hRB u hg1u)
      have hg1_gt : m < g1 := by
        have hmem : k + 2 + m ∈ (gateAt D g1).inputs := List.count_pos_iff.mp hc1
        have := hRB g1 hg1_lt (k + 2 + m) hmem
        omega
      have hne12 : g1 ≠ g2 := by
        rintro rfl
        have hmem : g1 ∈ gcone k D u ∩ gcone k D v := Finset.mem_inter.mpr ⟨hg1u, hg2v⟩
        have hle := Finset.le_max' (gcone k D u ∩ gcone k D v) g1 hmem
        omega
      have hsub : ({g1, g2} : Finset ℕ) ⊆ Finset.range D.gates.length := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_range.mpr hg1_lt
        · exact gcone_subset_range k D hRB v hg2v
      have : 2 ≤ readsIn D (Finset.range D.gates.length) (k + 2 + m) := by
        calc 2 ≤ (gateAt D g1).inputs.count (k + 2 + m) + (gateAt D g2).inputs.count (k + 2 + m) := by omega
          _ = readsIn D {g1, g2} (k + 2 + m) := by
            unfold readsIn; rw [Finset.sum_pair hne12]
          _ ≤ readsIn D (Finset.range D.gates.length) (k + 2 + m) :=
            Finset.sum_le_sum_of_subset hsub
      omega

lemma tree_disjoint_supp (k : ℕ) (D : Circuit) (hRB : ReadsBack (k + 2) D)
    (hTree : ∀ w < k + 2 + D.gates.length, readsIn D (Finset.range D.gates.length) w +
      (if D.output = w then 1 else 0) ≤ 1)
    {j : ℕ} (hj : j < D.gates.length) {u v : ℕ}
    (hinp : (gateAt D j).inputs = [u, v]) :
    Disjoint (supp k D u) (supp k D v) := by
  have hdisjG := tree_disjoint_gcone k D hRB hTree hj hinp
  rw [Finset.disjoint_left]
  intro x hxu hxv
  have hu_lt : u < k + 2 + j := hRB j hj u (by simp [hinp])
  have hv_lt : v < k + 2 + j := hRB j hj v (by simp [hinp])
  have hbound : readsIn D (Finset.range D.gates.length) x.val ≤ 1 := by
    have := hTree x.val (by omega); omega
  have hj_not_u : j ∉ gcone k D u := fun h => by have := gcone_lt k D hRB u j h; omega
  have hj_not_v : j ∉ gcone k D v := fun h => by have := gcone_lt k D hRB v j h; omega
  rcases supp_read_in_gcone k D hRB u x hxu with hxu_eq | hru_pos
  · rcases supp_read_in_gcone k D hRB v x hxv with hxv_eq | hrv_pos
    · have hcnt : (gateAt D j).inputs.count x.val = 2 := by
        simp [hinp, ← hxu_eq, ← hxv_eq]
      have : 2 ≤ readsIn D (Finset.range D.gates.length) x.val := by
        calc 2 = (gateAt D j).inputs.count x.val := hcnt.symm
          _ ≤ readsIn D (Finset.range D.gates.length) x.val :=
            Finset.single_le_sum (f := fun g' => (gateAt D g').inputs.count x.val)
              (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
      omega
    · have hsub : insert j (gcone k D v) ⊆ Finset.range D.gates.length := by
        intro g hg
        simp only [Finset.mem_insert] at hg
        rcases hg with rfl | hg
        · exact Finset.mem_range.mpr hj
        · exact gcone_subset_range k D hRB v hg
      have hcnt : 1 ≤ (gateAt D j).inputs.count x.val := by
        rw [hxu_eq]; exact List.count_pos_iff.mpr (by simp [hinp])
      have : 2 ≤ readsIn D (Finset.range D.gates.length) x.val := by
        calc 2 ≤ (gateAt D j).inputs.count x.val + readsIn D (gcone k D v) x.val := by omega
          _ = readsIn D (insert j (gcone k D v)) x.val := by
            unfold readsIn; rw [Finset.sum_insert hj_not_v]
          _ ≤ readsIn D (Finset.range D.gates.length) x.val :=
            Finset.sum_le_sum_of_subset hsub
      omega
  · rcases supp_read_in_gcone k D hRB v x hxv with hxv_eq | hrv_pos
    · have hsub : insert j (gcone k D u) ⊆ Finset.range D.gates.length := by
        intro g hg
        simp only [Finset.mem_insert] at hg
        rcases hg with rfl | hg
        · exact Finset.mem_range.mpr hj
        · exact gcone_subset_range k D hRB u hg
      have hcnt : 1 ≤ (gateAt D j).inputs.count x.val := by
        rw [hxv_eq]; exact List.count_pos_iff.mpr (by simp [hinp])
      have : 2 ≤ readsIn D (Finset.range D.gates.length) x.val := by
        calc 2 ≤ (gateAt D j).inputs.count x.val + readsIn D (gcone k D u) x.val := by omega
          _ = readsIn D (insert j (gcone k D u)) x.val := by
            unfold readsIn; rw [Finset.sum_insert hj_not_u]
          _ ≤ readsIn D (Finset.range D.gates.length) x.val :=
            Finset.sum_le_sum_of_subset hsub
      omega
    · have hsub : gcone k D u ∪ gcone k D v ⊆ Finset.range D.gates.length :=
        Finset.union_subset (gcone_subset_range k D hRB u) (gcone_subset_range k D hRB v)
      have : 2 ≤ readsIn D (Finset.range D.gates.length) x.val := by
        calc 2 ≤ readsIn D (gcone k D u) x.val + readsIn D (gcone k D v) x.val := by omega
          _ = readsIn D (gcone k D u ∪ gcone k D v) x.val := by
            unfold readsIn; rw [Finset.sum_union hdisjG]
          _ ≤ readsIn D (Finset.range D.gates.length) x.val :=
            Finset.sum_le_sum_of_subset hsub
      omega

lemma wire_depends_on_supp (k : ℕ) (D : Circuit) (hRB : ReadsBack (k + 2) D) :
    ∀ w < k + 2 + D.gates.length, ∀ Y1 Y2 : Finset (Fin k),
      (∀ x ∈ supp k D w, x ∈ Y1 ↔ x ∈ Y2) →
      (D.wires (bitsOf Y1)).getD w false = (D.wires (bitsOf Y2)).getD w false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw Y1 Y2 heq
    by_cases hwk : w < k
    · rw [wires_getD_input D _ w (by rw [bitsOf_length]; omega),
          wires_getD_input D _ w (by rw [bitsOf_length]; omega),
          bitsOf_getD_lt Y1 w hwk, bitsOf_getD_lt Y2 w hwk]
      have hmem : (⟨w, hwk⟩ : Fin k) ∈ supp k D w := by rw [supp_lt_k k D w hwk]; simp
      simp [heq ⟨w, hwk⟩ hmem]
    · by_cases hwk2 : w < k + 2
      · rw [wires_getD_input D _ w (by rw [bitsOf_length]; omega),
            wires_getD_input D _ w (by rw [bitsOf_length]; omega)]
        have : w = k ∨ w = k + 1 := by omega
        rcases this with rfl | rfl
        · rw [bitsOf_getD_k, bitsOf_getD_k]
        · rw [bitsOf_getD_k1, bitsOf_getD_k1]
      · set j := w - (k + 2)
        have hj : j < D.gates.length := by omega
        have hw_eq : w = k + 2 + j := by omega
        have h1 := wires_getD_gate_rb D (bitsOf Y1) (by rw [bitsOf_length]; exact hRB) j hj
        have h2 := wires_getD_gate_rb D (bitsOf Y2) (by rw [bitsOf_length]; exact hRB) j hj
        rw [bitsOf_length] at h1 h2
        rw [hw_eq, h1, h2]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hilt : i < w := by rw [hw_eq]; exact hRB j hj i hi
        apply ih i hilt (by omega) Y1 Y2
        intro x hx
        apply heq x
        rw [hw_eq, supp_gate k D hRB j hj, foldr_union_mem]
        exact ⟨supp k D i, List.mem_map.mpr ⟨i, hi, rfl⟩, hx⟩

lemma sep_and_step {α : Type*} [DecidableEq α] {V1 V2 : Finset α}
    (hdisj : Disjoint V1 V2)
    (f1 f2 : Finset α → Bool)
    (hdep1 : ∀ Y1 Y2, (∀ x ∈ V1, x ∈ Y1 ↔ x ∈ Y2) → f1 Y1 = f1 Y2)
    (hdep2 : ∀ Y1 Y2, (∀ x ∈ V2, x ∈ Y1 ↔ x ∈ Y2) → f2 Y1 = f2 Y2)
    (ih1 : ∀ b p q, (∀ Y ⊆ V1, Y.card < p → f1 Y = !b) →
      (∀ Y ⊆ V1, (V1 \ Y).card < q → f1 Y = b) → p * q ≤ V1.card)
    (ih2 : ∀ b p q, (∀ Y ⊆ V2, Y.card < p → f2 Y = !b) →
      (∀ Y ⊆ V2, (V2 \ Y).card < q → f2 Y = b) → p * q ≤ V2.card)
    (b : Bool) (p q : ℕ)
    (hlo : ∀ Y ⊆ V1 ∪ V2, Y.card < p → (f1 Y && f2 Y) = !b)
    (hhi : ∀ Y ⊆ V1 ∪ V2, ((V1 ∪ V2) \ Y).card < q → (f1 Y && f2 Y) = b) :
    p * q ≤ (V1 ∪ V2).card := by
  rw [Finset.card_union_of_disjoint hdisj]
  cases b with
  | true =>
    by_cases hq0 : q = 0
    · subst hq0; simp
    have hhi1 : ∀ Y1 ⊆ V1, (V1 \ Y1).card < q → f1 Y1 = true := by
      intro Y1 hY1 hcard
      have hsub : Y1 ∪ V2 ⊆ V1 ∪ V2 := Finset.union_subset_union_left hY1
      have hdiff : (V1 ∪ V2) \ (Y1 ∪ V2) = V1 \ Y1 := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h2, hn⟩
          · exact ⟨h1, fun h => hn (Or.inl h)⟩
          · exact absurd (Or.inr h2) hn
        · rintro ⟨h1, hn⟩
          refine ⟨Or.inl h1, ?_⟩
          rintro (h | h)
          · exact hn h
          · exact Finset.disjoint_left.mp hdisj h1 h
      have h := hhi (Y1 ∪ V2) hsub (by rw [hdiff]; exact hcard)
      have hf1 : f1 (Y1 ∪ V2) = f1 Y1 := hdep1 _ _ fun x hx => by
        simp only [Finset.mem_union, or_iff_left_iff_imp]
        intro hx2; exact absurd hx2 (Finset.disjoint_left.mp hdisj hx)
      rw [hf1] at h
      exact (Bool.and_eq_true _ _).mp h |>.1
    have hhi2 : ∀ Y2 ⊆ V2, (V2 \ Y2).card < q → f2 Y2 = true := by
      intro Y2 hY2 hcard
      have hsub : V1 ∪ Y2 ⊆ V1 ∪ V2 := Finset.union_subset_union_right hY2
      have hdiff : (V1 ∪ V2) \ (V1 ∪ Y2) = V2 \ Y2 := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h2, hn⟩
          · exact absurd (Or.inl h1) hn
          · exact ⟨h2, fun h => hn (Or.inr h)⟩
        · rintro ⟨h2, hn⟩
          refine ⟨Or.inr h2, ?_⟩
          rintro (h | h)
          · exact Finset.disjoint_right.mp hdisj h2 h
          · exact hn h
      have h := hhi (V1 ∪ Y2) hsub (by rw [hdiff]; exact hcard)
      have hf2 : f2 (V1 ∪ Y2) = f2 Y2 := hdep2 _ _ fun x hx => by
        simp only [Finset.mem_union, or_iff_right_iff_imp]
        intro hx1; exact absurd hx (Finset.disjoint_left.mp hdisj hx1)
      rw [hf2] at h
      exact (Bool.and_eq_true _ _).mp h |>.2
    have hex1 : ∃ r, ∃ Y1 ⊆ V1, Y1.card = r ∧ f1 Y1 = true :=
      ⟨V1.card, V1, Finset.Subset.refl _, rfl, hhi1 V1 (Finset.Subset.refl _) (by simp; omega)⟩
    have hex2 : ∃ r, ∃ Y2 ⊆ V2, Y2.card = r ∧ f2 Y2 = true :=
      ⟨V2.card, V2, Finset.Subset.refl _, rfl, hhi2 V2 (Finset.Subset.refl _) (by simp; omega)⟩
    classical
    let p1 := Nat.find hex1
    let p2 := Nat.find hex2
    obtain ⟨Y1, hY1sub, hY1card, hY1true⟩ := Nat.find_spec hex1
    obtain ⟨Y2, hY2sub, hY2card, hY2true⟩ := Nat.find_spec hex2
    have hlo1 : ∀ Y ⊆ V1, Y.card < p1 → f1 Y = false := by
      intro Y hY hc
      cases hf : f1 Y with
      | false => rfl
      | true => exact absurd ⟨Y, hY, rfl, hf⟩ (Nat.find_min hex1 hc)
    have hlo2 : ∀ Y ⊆ V2, Y.card < p2 → f2 Y = false := by
      intro Y hY hc
      cases hf : f2 Y with
      | false => rfl
      | true => exact absurd ⟨Y, hY, rfl, hf⟩ (Nat.find_min hex2 hc)
    have hp_le : p ≤ p1 + p2 := by
      by_contra hlt
      push_neg at hlt
      have hYsub : Y1 ∪ Y2 ⊆ V1 ∪ V2 := Finset.union_subset_union hY1sub hY2sub
      have hYcard : (Y1 ∪ Y2).card < p := by
        calc (Y1 ∪ Y2).card ≤ Y1.card + Y2.card := Finset.card_union_le _ _
          _ = p1 + p2 := by rw [hY1card, hY2card]
          _ < p := hlt
      have h1 := hlo (Y1 ∪ Y2) hYsub hYcard
      have hf1 : f1 (Y1 ∪ Y2) = true := by
        rw [← hY1true]; apply hdep1; intro x hx
        simp only [Finset.mem_union, or_iff_left_iff_imp]
        intro hx2; exact absurd (hY2sub hx2) (Finset.disjoint_left.mp hdisj hx)
      have hf2 : f2 (Y1 ∪ Y2) = true := by
        rw [← hY2true]; apply hdep2; intro x hx
        simp only [Finset.mem_union, or_iff_right_iff_imp]
        intro hx1; exact absurd hx (Finset.disjoint_left.mp hdisj (hY1sub hx1))
      simp [hf1, hf2] at h1
    have hb1 := ih1 true p1 q hlo1 hhi1
    have hb2 := ih2 true p2 q hlo2 hhi2
    calc p * q ≤ (p1 + p2) * q := Nat.mul_le_mul_right q hp_le
      _ = p1 * q + p2 * q := Nat.add_mul p1 p2 q
      _ ≤ V1.card + V2.card := Nat.add_le_add hb1 hb2
  | false =>
    by_cases hp0 : p = 0
    · subst hp0; simp
    have hlo1 : ∀ Y1 ⊆ V1, Y1.card < p → f1 Y1 = true := by
      intro Y1 hY1 hcard
      have h := hlo Y1 (hY1.trans Finset.subset_union_left) hcard
      exact (Bool.and_eq_true _ _).mp h |>.1
    have hlo2 : ∀ Y2 ⊆ V2, Y2.card < p → f2 Y2 = true := by
      intro Y2 hY2 hcard
      have h := hlo Y2 (hY2.trans Finset.subset_union_right) hcard
      exact (Bool.and_eq_true _ _).mp h |>.2
    have hex1 : ∃ r, ∃ Y1 ⊆ V1, (V1 \ Y1).card = r ∧ f1 Y1 = true :=
      ⟨V1.card, ∅, Finset.empty_subset _, by simp, hlo1 ∅ (Finset.empty_subset _) (by simp; omega)⟩
    have hex2 : ∃ r, ∃ Y2 ⊆ V2, (V2 \ Y2).card = r ∧ f2 Y2 = true :=
      ⟨V2.card, ∅, Finset.empty_subset _, by simp, hlo2 ∅ (Finset.empty_subset _) (by simp; omega)⟩
    classical
    let q1 := Nat.find hex1
    let q2 := Nat.find hex2
    obtain ⟨Y1, hY1sub, hY1card, hY1true⟩ := Nat.find_spec hex1
    obtain ⟨Y2, hY2sub, hY2card, hY2true⟩ := Nat.find_spec hex2
    have hhi1 : ∀ Y ⊆ V1, (V1 \ Y).card < q1 → f1 Y = false := by
      intro Y hY hc
      cases hf : f1 Y with
      | false => rfl
      | true => exact absurd ⟨Y, hY, rfl, hf⟩ (Nat.find_min hex1 hc)
    have hhi2 : ∀ Y ⊆ V2, (V2 \ Y).card < q2 → f2 Y = false := by
      intro Y hY hc
      cases hf : f2 Y with
      | false => rfl
      | true => exact absurd ⟨Y, hY, rfl, hf⟩ (Nat.find_min hex2 hc)
    have hq_le : q ≤ q1 + q2 := by
      by_contra hlt
      push_neg at hlt
      have hYsub : Y1 ∪ Y2 ⊆ V1 ∪ V2 := Finset.union_subset_union hY1sub hY2sub
      have hdiff_sub : (V1 ∪ V2) \ (Y1 ∪ Y2) ⊆ (V1 \ Y1) ∪ (V2 \ Y2) := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
        rcases hx with ⟨h1 | h2, hn⟩
        · exact Or.inl ⟨h1, fun h => hn (Or.inl h)⟩
        · exact Or.inr ⟨h2, fun h => hn (Or.inr h)⟩
      have hYcard : ((V1 ∪ V2) \ (Y1 ∪ Y2)).card < q := by
        calc ((V1 ∪ V2) \ (Y1 ∪ Y2)).card
            ≤ ((V1 \ Y1) ∪ (V2 \ Y2)).card := Finset.card_le_card hdiff_sub
          _ ≤ (V1 \ Y1).card + (V2 \ Y2).card := Finset.card_union_le _ _
          _ = q1 + q2 := by rw [hY1card, hY2card]
          _ < q := hlt
      have h1 := hhi (Y1 ∪ Y2) hYsub hYcard
      have hf1 : f1 (Y1 ∪ Y2) = true := by
        rw [← hY1true]; apply hdep1; intro x hx
        simp only [Finset.mem_union, or_iff_left_iff_imp]
        intro hx2; exact absurd (hY2sub hx2) (Finset.disjoint_left.mp hdisj hx)
      have hf2 : f2 (Y1 ∪ Y2) = true := by
        rw [← hY2true]; apply hdep2; intro x hx
        simp only [Finset.mem_union, or_iff_right_iff_imp]
        intro hx1; exact absurd hx (Finset.disjoint_left.mp hdisj (hY1sub hx1))
      simp [hf1, hf2] at h1
    have hb1 := ih1 false p q1 hlo1 hhi1
    have hb2 := ih2 false p q2 hlo2 hhi2
    calc p * q ≤ p * (q1 + q2) := Nat.mul_le_mul_left p hq_le
      _ = p * q1 + p * q2 := Nat.mul_add p q1 q2
      _ ≤ V1.card + V2.card := Nat.add_le_add hb1 hb2

lemma read_once_sep_bound (k : ℕ) (D : Circuit) (hFit : FanInTwo D) (hRB : ReadsBack (k + 2) D)
    (hTree : ∀ w < k + 2 + D.gates.length, readsIn D (Finset.range D.gates.length) w +
      (if D.output = w then 1 else 0) ≤ 1)
    (base Δ : Finset (Fin k)) (hdisjB : Disjoint base Δ) :
    ∀ w < k + 2 + D.gates.length, ∀ (b : Bool) (p q : ℕ),
      (∀ Y ⊆ supp k D w ∩ Δ, Y.card < p →
        (D.wires (bitsOf (base ∪ Y))).getD w false = !b) →
      (∀ Y ⊆ supp k D w ∩ Δ, ((supp k D w ∩ Δ) \ Y).card < q →
        (D.wires (bitsOf (base ∪ Y))).getD w false = b) →
      p * q ≤ (supp k D w ∩ Δ).card := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw b p q hlo hhi
    have hconst : ∀ c : Bool,
        (∀ Y ⊆ supp k D w ∩ Δ, (D.wires (bitsOf (base ∪ Y))).getD w false = c) →
        p * q ≤ (supp k D w ∩ Δ).card := by
      intro c hc
      by_cases hp0 : p = 0
      · subst hp0; simp
      · by_cases hq0 : q = 0
        · subst hq0; simp
        · have h1 := hlo ∅ (Finset.empty_subset _) (by simp; omega)
          have h2 := hhi (supp k D w ∩ Δ) (Finset.Subset.refl _) (by simp; omega)
          rw [hc ∅ (Finset.empty_subset _)] at h1
          rw [hc (supp k D w ∩ Δ) (Finset.Subset.refl _)] at h2
          rw [h2] at h1
          cases b <;> simp at h1
    by_cases hwk : w < k
    · by_cases hmemΔ : (⟨w, hwk⟩ : Fin k) ∈ Δ
      · have hV : supp k D w ∩ Δ = {⟨w, hwk⟩} := by
          rw [supp_lt_k k D w hwk]
          ext x; simp only [Finset.mem_inter, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl, _⟩; rfl
          · rintro rfl; exact ⟨rfl, hmemΔ⟩
        have hnotB : (⟨w, hwk⟩ : Fin k) ∉ base := Finset.disjoint_right.mp hdisjB hmemΔ
        rw [hV, Finset.card_singleton]
        have hval : ∀ Y : Finset (Fin k),
            (D.wires (bitsOf (base ∪ Y))).getD w false = decide (⟨w, hwk⟩ ∈ Y) := by
          intro Y
          rw [wires_getD_input D _ w (by rw [bitsOf_length]; omega), bitsOf_getD_lt _ w hwk]
          simp [hnotB]
        cases b with
        | true =>
          have hp1 : p ≤ 1 := by
            by_contra h; push_neg at h
            have := hlo {⟨w, hwk⟩} (by rw [hV]) (by simp; omega)
            rw [hval] at this; simp at this
          have hq1 : q ≤ 1 := by
            by_contra h; push_neg at h
            have := hhi ∅ (Finset.empty_subset _) (by rw [hV]; simp; omega)
            rw [hval] at this; simp at this
          exact Nat.mul_le_mul hp1 hq1
        | false =>
          have hp0 : p = 0 := by
            by_contra h
            have := hlo ∅ (Finset.empty_subset _) (by simp; omega)
            rw [hval] at this; simp at this
          subst hp0; simp
      · apply hconst (decide (⟨w, hwk⟩ ∈ base))
        intro Y hY
        rw [wires_getD_input D _ w (by rw [bitsOf_length]; omega), bitsOf_getD_lt _ w hwk]
        have hnotY : (⟨w, hwk⟩ : Fin k) ∉ Y := fun h => hmemΔ (Finset.mem_inter.mp (hY h)).2
        simp [hnotY]
    · by_cases hwk2 : w < k + 2
      · have : w = k ∨ w = k + 1 := by omega
        rcases this with hw_eq | hw_eq
        · apply hconst false
          intro Y _
          rw [hw_eq, wires_getD_input D _ k (by rw [bitsOf_length]; omega), bitsOf_getD_k]
        · apply hconst true
          intro Y _
          rw [hw_eq, wires_getD_input D _ (k + 1) (by rw [bitsOf_length]; omega), bitsOf_getD_k1]
      · set j := w - (k + 2)
        have hj : j < D.gates.length := by omega
        have hw_eq : w = k + 2 + j := by omega
        have hgj_mem : gateAt D j ∈ D.gates := by
          have : gateAt D j = D.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
          rw [this]; exact List.getElem_mem hj
        obtain ⟨hop, hlen_in⟩ := hFit (gateAt D j) hgj_mem
        have heval : ∀ Y : Finset (Fin k),
            (D.wires (bitsOf (base ∪ Y))).getD w false =
              (gateAt D j).op.eval
                ((gateAt D j).inputs.map fun i => (D.wires (bitsOf (base ∪ Y))).getD i false) := by
          intro Y
          have h := wires_getD_gate_rb D (bitsOf (base ∪ Y)) (by rw [bitsOf_length]; exact hRB) j hj
          rw [bitsOf_length] at h
          rw [hw_eq, h]
        rcases h_in : (gateAt D j).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
        · apply hconst ((gateAt D j).op.eval [])
          intro Y _
          rw [heval Y, h_in]; rfl
        · have hu_lt : u < w := by rw [hw_eq]; exact hRB j hj u (by simp [h_in])
          have hsupp : supp k D w = supp k D u := by
            rw [hw_eq, supp_gate k D hRB j hj, h_in]; simp
          rw [hsupp] at hlo hhi ⊢
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop | hop | hop
          · apply ih u hu_lt (by omega) b p q
            · intro Y hY hc; have := hlo Y hY hc; rw [heval, h_in, hop] at this; simpa [GateOp.eval] using this
            · intro Y hY hc; have := hhi Y hY hc; rw [heval, h_in, hop] at this; simpa [GateOp.eval] using this
          · apply ih u hu_lt (by omega) b p q
            · intro Y hY hc; have := hlo Y hY hc; rw [heval, h_in, hop] at this; simpa [GateOp.eval] using this
            · intro Y hY hc; have := hhi Y hY hc; rw [heval, h_in, hop] at this; simpa [GateOp.eval] using this
          · apply ih u hu_lt (by omega) (!b) p q
            · intro Y hY hc
              have := hlo Y hY hc; rw [heval, h_in, hop] at this
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] at this
              cases b <;> cases hvu : (D.wires (bitsOf (base ∪ Y))).getD u false <;>
                simp only [hvu, Bool.not_true, Bool.not_false] at this ⊢ <;> first | exact this | exact this.symm | rfl
            · intro Y hY hc
              have := hhi Y hY hc; rw [heval, h_in, hop] at this
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] at this
              cases b <;> cases hvu : (D.wires (bitsOf (base ∪ Y))).getD u false <;>
                simp only [hvu, Bool.not_true, Bool.not_false] at this ⊢ <;> first | exact this | exact this.symm | rfl
        · have hu_lt : u < w := by rw [hw_eq]; exact hRB j hj u (by simp [h_in])
          have hv_lt : v < w := by rw [hw_eq]; exact hRB j hj v (by simp [h_in])
          have hsupp : supp k D w = supp k D u ∪ supp k D v := by
            rw [hw_eq, supp_gate k D hRB j hj, h_in]; simp
          have hV : supp k D w ∩ Δ = (supp k D u ∩ Δ) ∪ (supp k D v ∩ Δ) := by
            rw [hsupp, Finset.union_inter_distrib_right]
          have hdisjUV : Disjoint (supp k D u ∩ Δ) (supp k D v ∩ Δ) :=
            (tree_disjoint_supp k D hRB hTree hj h_in).mono Finset.inter_subset_left Finset.inter_subset_left
          let fU : Finset (Fin k) → Bool := fun Y => (D.wires (bitsOf (base ∪ (Y ∩ Δ)))).getD u false
          let fV : Finset (Fin k) → Bool := fun Y => (D.wires (bitsOf (base ∪ (Y ∩ Δ)))).getD v false
          have hdepU : ∀ Y1 Y2, (∀ x ∈ supp k D u ∩ Δ, x ∈ Y1 ↔ x ∈ Y2) → fU Y1 = fU Y2 := by
            intro Y1 Y2 heqY
            apply wire_depends_on_supp k D hRB u (by omega)
            intro x hxu
            simp only [Finset.mem_union, Finset.mem_inter]
            by_cases hxΔ : x ∈ Δ
            · simp [hxΔ, heqY x (Finset.mem_inter.mpr ⟨hxu, hxΔ⟩)]
            · simp [hxΔ]
          have hdepV : ∀ Y1 Y2, (∀ x ∈ supp k D v ∩ Δ, x ∈ Y1 ↔ x ∈ Y2) → fV Y1 = fV Y2 := by
            intro Y1 Y2 heqY
            apply wire_depends_on_supp k D hRB v (by omega)
            intro x hxv
            simp only [Finset.mem_union, Finset.mem_inter]
            by_cases hxΔ : x ∈ Δ
            · simp [hxΔ, heqY x (Finset.mem_inter.mpr ⟨hxv, hxΔ⟩)]
            · simp [hxΔ]
          have hfU_sub : ∀ Y ⊆ supp k D u ∩ Δ, fU Y = (D.wires (bitsOf (base ∪ Y))).getD u false := by
            intro Y hY
            have hYΔ : Y ∩ Δ = Y := Finset.inter_eq_left.mpr (hY.trans Finset.inter_subset_right)
            simp [fU, hYΔ]
          have hfV_sub : ∀ Y ⊆ supp k D v ∩ Δ, fV Y = (D.wires (bitsOf (base ∪ Y))).getD v false := by
            intro Y hY
            have hYΔ : Y ∩ Δ = Y := Finset.inter_eq_left.mpr (hY.trans Finset.inter_subset_right)
            simp [fV, hYΔ]
          have ihU : ∀ b' p' q', (∀ Y ⊆ supp k D u ∩ Δ, Y.card < p' → fU Y = !b') →
              (∀ Y ⊆ supp k D u ∩ Δ, ((supp k D u ∩ Δ) \ Y).card < q' → fU Y = b') →
              p' * q' ≤ (supp k D u ∩ Δ).card := by
            intro b' p' q' h1 h2
            apply ih u hu_lt (by omega) b' p' q'
            · intro Y hY hc; rw [← hfU_sub Y hY]; exact h1 Y hY hc
            · intro Y hY hc; rw [← hfU_sub Y hY]; exact h2 Y hY hc
          have ihV : ∀ b' p' q', (∀ Y ⊆ supp k D v ∩ Δ, Y.card < p' → fV Y = !b') →
              (∀ Y ⊆ supp k D v ∩ Δ, ((supp k D v ∩ Δ) \ Y).card < q' → fV Y = b') →
              p' * q' ≤ (supp k D v ∩ Δ).card := by
            intro b' p' q' h1 h2
            apply ih v hv_lt (by omega) b' p' q'
            · intro Y hY hc; rw [← hfV_sub Y hY]; exact h1 Y hY hc
            · intro Y hY hc; rw [← hfV_sub Y hY]; exact h2 Y hY hc
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop | hop | hop
          · rw [hV]
            apply sep_and_step hdisjUV fU fV hdepU hdepV ihU ihV b p q
            · intro Y hY hc
              have hYΔ : Y ∩ Δ = Y := Finset.inter_eq_left.mpr ((hV ▸ hY).trans Finset.inter_subset_right)
              have := hlo Y (hV.symm ▸ hY) hc
              rw [heval, h_in, hop] at this
              simpa [fU, fV, hYΔ, GateOp.eval] using this
            · intro Y hY hc
              have hYΔ : Y ∩ Δ = Y := Finset.inter_eq_left.mpr ((hV ▸ hY).trans Finset.inter_subset_right)
              have := hhi Y (hV.symm ▸ hY) (by rwa [← hV] at hc)
              rw [heval, h_in, hop] at this
              simpa [fU, fV, hYΔ, GateOp.eval] using this
          · rw [hV]
            have hdepU' : ∀ Y1 Y2, (∀ x ∈ supp k D u ∩ Δ, x ∈ Y1 ↔ x ∈ Y2) → (!fU Y1) = (!fU Y2) :=
              fun Y1 Y2 h => congrArg (!·) (hdepU Y1 Y2 h)
            have hdepV' : ∀ Y1 Y2, (∀ x ∈ supp k D v ∩ Δ, x ∈ Y1 ↔ x ∈ Y2) → (!fV Y1) = (!fV Y2) :=
              fun Y1 Y2 h => congrArg (!·) (hdepV Y1 Y2 h)
            have ihU' : ∀ b' p' q', (∀ Y ⊆ supp k D u ∩ Δ, Y.card < p' → (!fU Y) = !b') →
                (∀ Y ⊆ supp k D u ∩ Δ, ((supp k D u ∩ Δ) \ Y).card < q' → (!fU Y) = b') →
                p' * q' ≤ (supp k D u ∩ Δ).card := by
              intro b' p' q' h1 h2
              apply ihU (!b') p' q'
              · intro Y hY hc; have := h1 Y hY hc; cases b' <;> cases h : fU Y <;> simp only [h, Bool.not_true, Bool.not_false] at this ⊢ <;> first | exact this | exact this.symm | rfl
              · intro Y hY hc; have := h2 Y hY hc; cases b' <;> cases h : fU Y <;> simp only [h, Bool.not_true, Bool.not_false] at this ⊢ <;> first | exact this | exact this.symm | rfl
            have ihV' : ∀ b' p' q', (∀ Y ⊆ supp k D v ∩ Δ, Y.card < p' → (!fV Y) = !b') →
                (∀ Y ⊆ supp k D v ∩ Δ, ((supp k D v ∩ Δ) \ Y).card < q' → (!fV Y) = b') →
                p' * q' ≤ (supp k D v ∩ Δ).card := by
              intro b' p' q' h1 h2
              apply ihV (!b') p' q'
              · intro Y hY hc; have := h1 Y hY hc; cases b' <;> cases h : fV Y <;> simp only [h, Bool.not_true, Bool.not_false] at this ⊢ <;> first | exact this | exact this.symm | rfl
              · intro Y hY hc; have := h2 Y hY hc; cases b' <;> cases h : fV Y <;> simp only [h, Bool.not_true, Bool.not_false] at this ⊢ <;> first | exact this | exact this.symm | rfl
            apply sep_and_step hdisjUV (fun Y => !fU Y) (fun Y => !fV Y) hdepU' hdepV' ihU' ihV' (!b) p q
            · intro Y hY hc
              have hYΔ : Y ∩ Δ = Y := Finset.inter_eq_left.mpr ((hV ▸ hY).trans Finset.inter_subset_right)
              have := hlo Y (hV.symm ▸ hY) hc
              rw [heval, h_in, hop] at this
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false] at this
              simp only [fU, fV, hYΔ]
              cases b <;> cases hu : (D.wires (bitsOf (base ∪ Y))).getD u false <;>
                cases hv : (D.wires (bitsOf (base ∪ Y))).getD v false <;>
                simp only [hu, hv, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or, Bool.true_and, Bool.false_and] at this ⊢ <;> first | exact this | exact this.symm | rfl
            · intro Y hY hc
              have hYΔ : Y ∩ Δ = Y := Finset.inter_eq_left.mpr ((hV ▸ hY).trans Finset.inter_subset_right)
              have := hhi Y (hV.symm ▸ hY) (by rwa [← hV] at hc)
              rw [heval, h_in, hop] at this
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false] at this
              simp only [fU, fV, hYΔ]
              cases b <;> cases hu : (D.wires (bitsOf (base ∪ Y))).getD u false <;>
                cases hv : (D.wires (bitsOf (base ∪ Y))).getD v false <;>
                simp only [hu, hv, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or, Bool.true_and, Bool.false_and] at this ⊢ <;> first | exact this | exact this.symm | rfl
          · have hle : (supp k D u ∩ Δ).card ≤ (supp k D w ∩ Δ).card := by
              rw [hV]; exact Finset.card_le_card Finset.subset_union_left
            refine (ih u hu_lt (by omega) (!b) p q ?_ ?_).trans hle
            · intro Y hY hc
              have hY' : Y ⊆ supp k D w ∩ Δ := hY.trans (by rw [hV]; exact Finset.subset_union_left)
              have := hlo Y hY' hc
              rw [heval, h_in, hop] at this
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] at this
              cases b <;> cases hu : (D.wires (bitsOf (base ∪ Y))).getD u false <;>
                simp only [hu, Bool.not_true, Bool.not_false] at this ⊢ <;> first | exact this | exact this.symm | rfl
            · intro Y hY hc
              let Y' := Y ∪ (supp k D v ∩ Δ)
              have hY'sub : Y' ⊆ supp k D w ∩ Δ := by
                rw [hV]; exact Finset.union_subset_union_left hY
              have hdiff : (supp k D w ∩ Δ) \ Y' = (supp k D u ∩ Δ) \ Y := by
                rw [hV]
                ext x; simp only [Y', Finset.mem_sdiff, Finset.mem_union]
                constructor
                · rintro ⟨h1 | h2, hn⟩
                  · exact ⟨h1, fun h => hn (Or.inl h)⟩
                  · exact absurd (Or.inr h2) hn
                · rintro ⟨h1, hn⟩
                  refine ⟨Or.inl h1, ?_⟩
                  rintro (h | h)
                  · exact hn h
                  · exact Finset.disjoint_left.mp hdisjUV h1 h
              have := hhi Y' hY'sub (by rw [hdiff]; exact hc)
              rw [heval, h_in, hop] at this
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] at this
              have heqU : (D.wires (bitsOf (base ∪ Y'))).getD u false =
                  (D.wires (bitsOf (base ∪ Y))).getD u false := by
                apply wire_depends_on_supp k D hRB u (by omega)
                intro x hxu
                simp only [Y', Finset.mem_union]
                constructor
                · rintro (hb | hy | hxv)
                  · exact Or.inl hb
                  · exact Or.inr hy
                  · exact absurd hxv (Finset.disjoint_left.mp hdisjUV (Finset.mem_inter.mpr ⟨hxu, (Finset.mem_inter.mp hxv).2⟩))
                · rintro (hb | hy)
                  · exact Or.inl hb
                  · exact Or.inr (Or.inl hy)
              rw [heqU] at this
              cases b <;> cases hu : (D.wires (bitsOf (base ∪ Y))).getD u false <;>
                simp only [hu, Bool.not_true, Bool.not_false] at this ⊢ <;> first | exact this | exact this.symm | rfl
        · rw [h_in] at hlen_in; simp at hlen_in

end ReadOnceLower

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

lemma lower_step_tree {k a f : ℕ} (D : Circuit)
    (hFit : FanInTwo D) (hRB : ReadsBack (k + 2) D) (hOut : D.output < k + 2 + D.gates.length)
    (hTree : ∀ w < k + 2 + D.gates.length, readsIn D (Finset.range D.gates.length) w +
      (if D.output = w then 1 else 0) ≤ 1)
    (gA gA' : Finset (Fin k)) (hsub : gA ⊆ gA')
    (hrecA : ∀ Y : Finset (Fin k), (gA \ Y).card ≤ a → (Y \ gA).card ≤ f →
      (D.wires (bitsOf Y)).getD D.output false = false)
    (hrecA' : ∀ Y : Finset (Fin k), (gA' \ Y).card ≤ a → (Y \ gA').card ≤ f →
      (D.wires (bitsOf Y)).getD D.output false = true) :
    (a + 1) * (f + 1) ≤ (gA' \ gA).card := by
  let Δ := gA' \ gA
  have hdisj : Disjoint gA Δ := Finset.disjoint_sdiff
  have hbound := read_once_sep_bound k D hFit hRB hTree gA Δ hdisj D.output hOut true (f + 1) (a + 1)
    (by
      intro Y hY hcard
      have h1 : (gA \ (gA ∪ Y)).card ≤ a := by
        have : gA \ (gA ∪ Y) = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_left
        simp [this]
      have h2 : ((gA ∪ Y) \ gA).card ≤ f := by
        have : (gA ∪ Y) \ gA ⊆ Y := by
          intro x hx; simp only [Finset.mem_sdiff, Finset.mem_union] at hx; tauto
        exact (Finset.card_le_card this).trans (Nat.le_of_lt_succ hcard)
      exact hrecA (gA ∪ Y) h1 h2)
    (by
      intro Y hY hcard
      let miss := (supp k D D.output ∩ Δ) \ Y
      let Y'' := gA' \ miss
      have h1 : (gA' \ Y'').card ≤ a := by
        have : gA' \ Y'' ⊆ miss := by
          intro x hx; simp only [Y'', Finset.mem_sdiff] at hx; tauto
        exact (Finset.card_le_card this).trans (Nat.le_of_lt_succ hcard)
      have h2 : (Y'' \ gA').card ≤ f := by
        have : Y'' \ gA' = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr Finset.sdiff_subset
        simp [this]
      have heq : (D.wires (bitsOf (gA ∪ Y))).getD D.output false =
          (D.wires (bitsOf Y'')).getD D.output false := by
        apply wire_depends_on_supp k D hRB D.output hOut
        intro x hxs
        simp only [Y'', miss, Δ, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
        constructor
        · rintro (hxA | hxY)
          · exact ⟨hsub hxA, fun h => h.1.2.2 hxA⟩
          · have hxΔ := (Finset.mem_inter.mp (hY hxY)).2
            exact ⟨(Finset.mem_sdiff.mp hxΔ).1, fun h => h.2 hxY⟩
        · rintro ⟨hxA', hnm⟩
          by_cases hxA : x ∈ gA
          · exact Or.inl hxA
          · right
            by_contra hny
            exact hnm ⟨⟨hxs, hxA', hxA⟩, hny⟩
      rw [heq]
      exact hrecA' Y'' h1 h2)
  calc (a + 1) * (f + 1) = (f + 1) * (a + 1) := Nat.mul_comm _ _
    _ ≤ (supp k D D.output ∩ Δ).card := hbound
    _ ≤ Δ.card := Finset.card_le_card Finset.inter_subset_right

def rchain (op : GateOp) (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], 0)
  | [w] => ([], w)
  | w :: w2 :: rest =>
    let sub := rchain op base (w2 :: rest)
    (sub.1 ++ [⟨op, [w, sub.2]⟩], base + sub.1.length)

lemma rchain_length (op : GateOp) (base : ℕ) :
    ∀ ws : List ℕ, ws ≠ [] → (rchain op base ws).1.length = ws.length - 1
  | [], h => absurd rfl h
  | [_], _ => rfl
  | _ :: w2 :: rest, _ => by
    have ih := rchain_length op base (w2 :: rest) (by simp)
    simp only [rchain, List.length_append, List.length_singleton, List.length_cons, List.length_nil] at ih ⊢
    omega

lemma rchain_out_lt (op : GateOp) (base : ℕ) :
    ∀ ws : List ℕ, ws ≠ [] → (∀ w ∈ ws, w < base) →
      (rchain op base ws).2 < base + (rchain op base ws).1.length
  | [], h, _ => absurd rfl h
  | [w], _, hw => by
    simp only [rchain, List.length_nil, Nat.add_zero]
    exact hw w List.mem_cons_self
  | _ :: w2 :: rest, _, _ => by
    simp only [rchain, List.length_append, List.length_singleton]
    omega

lemma rchain_gates_prop (op : GateOp) (base : ℕ) :
    ∀ ws : List ℕ, ∀ g ∈ (rchain op base ws).1, g.op = op ∧ g.inputs.length = 2
  | [] => by simp [rchain]
  | [_] => by simp [rchain]
  | w :: w2 :: rest => by
    intro g hg
    simp only [rchain, List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact rchain_gates_prop op base (w2 :: rest) g h
    · exact ⟨rfl, rfl⟩

lemma rchain_rb (op : GateOp) (base : ℕ) :
    ∀ ws : List ℕ, (∀ w ∈ ws, w < base) →
      ∀ j < (rchain op base ws).1.length,
        ∀ i ∈ ((rchain op base ws).1.getD j ⟨.or, []⟩).inputs, i < base + j
  | [], _ => by simp [rchain]
  | [_], _ => by simp [rchain]
  | w :: w2 :: rest, hws => by
    have ih := rchain_rb op base (w2 :: rest) (fun x hx => hws x (List.mem_cons_of_mem _ hx))
    have hout := rchain_out_lt op base (w2 :: rest) (by simp)
      (fun x hx => hws x (List.mem_cons_of_mem _ hx))
    intro j hj i hi
    simp only [rchain, List.length_append, List.length_singleton] at hj
    by_cases hlt : j < (rchain op base (w2 :: rest)).1.length
    · simp only [rchain] at hi
      rw [List.getD_append _ _ _ _ hlt] at hi
      exact ih j hlt i hi
    · have hjeq : j = (rchain op base (w2 :: rest)).1.length := by omega
      subst hjeq
      simp only [rchain] at hi
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h
      · rw [h]; have := hws w List.mem_cons_self; omega
      · rw [h]; exact hout

lemma rchain_reads (op : GateOp) (base : ℕ) :
    ∀ ws : List ℕ, ws ≠ [] → ∀ x : ℕ,
      (∑ j ∈ Finset.range (rchain op base ws).1.length,
        ((rchain op base ws).1.getD j ⟨.or, []⟩).inputs.count x) +
        (if (rchain op base ws).2 = x then 1 else 0) =
      ws.count x + (if base ≤ x ∧ x < base + (rchain op base ws).1.length then 1 else 0)
  | [], h, _ => absurd rfl h
  | [w], _, x => by
    have hno : ¬ (base ≤ x ∧ x < base) := by omega
    simp only [rchain, List.length_nil, Finset.range_zero, Finset.sum_empty, zero_add,
      List.count_cons, List.count_nil, beq_iff_eq, Nat.add_zero, hno, ite_false]
    by_cases h : w = x
    · subst h; simp
    · have h' : x ≠ w := Ne.symm h; simp [h, h']
  | w :: w2 :: rest, _, x => by
    have ih := rchain_reads op base (w2 :: rest) (by simp) x
    set sub := rchain op base (w2 :: rest)
    rw [show (rchain op base (w :: w2 :: rest)).1 = sub.1 ++ [(⟨op, [w, sub.2]⟩ : Gate)] from rfl,
        show (rchain op base (w :: w2 :: rest)).2 = base + sub.1.length from rfl]
    simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
    have hpre : ∑ j ∈ Finset.range sub.1.length,
        ((sub.1 ++ [(⟨op, [w, sub.2]⟩ : Gate)]).getD j ⟨.or, []⟩).inputs.count x =
        ∑ j ∈ Finset.range sub.1.length, (sub.1.getD j ⟨.or, []⟩).inputs.count x := by
      apply Finset.sum_congr rfl; intro j hj
      rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hj)]
    rw [hpre, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    change (∑ j ∈ Finset.range sub.1.length, (sub.1.getD j ⟨.or, []⟩).inputs.count x) +
      (if sub.2 = x then 1 else 0) =
      (w2 :: rest).count x + (if base ≤ x ∧ x < base + sub.1.length then 1 else 0) at ih
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at ih ⊢
    by_cases hx : base + sub.1.length = x
    · subst hx
      have h1 : ¬ (base ≤ base + sub.1.length ∧ base + sub.1.length < base + sub.1.length) := by omega
      have h2 : base ≤ base + sub.1.length ∧ base + sub.1.length < base + (sub.1.length + 1) := by omega
      simp only [h1, h2, ite_true, ite_false] at ih ⊢
      by_cases hsub : sub.2 = base + sub.1.length <;> simp [hsub] at ih ⊢ <;> omega
    · have hiff : (base ≤ x ∧ x < base + (sub.1.length + 1)) ↔ (base ≤ x ∧ x < base + sub.1.length) := by omega
      simp only [hx, ite_false, hiff] at ih ⊢
      by_cases hsub : sub.2 = x <;> simp [hsub] at ih ⊢ <;> omega

lemma rchain_eval (op : GateOp) (hop : op = .and ∨ op = .or) (init : List Bool) :
    ∀ ws : List ℕ, ws ≠ [] → (∀ w ∈ ws, w < init.length) →
      (Circuit.wires ⟨(rchain op init.length ws).1, 0⟩ init).getD (rchain op init.length ws).2 false =
        match op with
        | .and => ws.all (fun w => init.getD w false)
        | _ => ws.any (fun w => init.getD w false)
  | [], h, _ => absurd rfl h
  | [w], _, _ => by
    rcases hop with rfl | rfl <;> simp [rchain, Circuit.wires]
  | w :: w2 :: rest, _, hws => by
    have ih := rchain_eval op hop init (w2 :: rest) (by simp)
      (fun x hx => hws x (List.mem_cons_of_mem _ hx))
    simp only [rchain]
    set sub := rchain op init.length (w2 :: rest)
    rw [wires_append_gate]
    have hlen : (Circuit.wires ⟨sub.1, 0⟩ init).length = init.length + sub.1.length :=
      wires_length ⟨sub.1, 0⟩ init
    rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
    have hw_in : (Circuit.wires ⟨sub.1, 0⟩ init).getD w false = init.getD w false :=
      wires_getD_input ⟨sub.1, 0⟩ init w (hws w List.mem_cons_self)
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hw_in]
      simpa using congrArg (init.getD w false && ·) ih
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hw_in]
      simpa using congrArg (init.getD w false || ·) ih

def buildAndGroups (base off f : ℕ) : ℕ → List Gate × List ℕ
  | 0 => ([], [])
  | p + 1 =>
    let prev := buildAndGroups base off f p
    let ws := List.ofFn fun q : Fin (f + 1) => off + p * (f + 1) + q.val
    let cur := rchain .and (base + prev.1.length) ws
    (prev.1 ++ cur.1, cur.2 :: prev.2)

lemma list_ofFn_count_range (off len x : ℕ) :
    (List.ofFn fun q : Fin len => off + q.val).count x =
      if off ≤ x ∧ x < off + len then 1 else 0 := by
  have hnodup : (List.ofFn fun q : Fin len => off + q.val).Nodup := by
    rw [List.nodup_ofFn]; intro a b h; dsimp only at h; ext; omega
  by_cases hmem : x ∈ List.ofFn fun q : Fin len => off + q.val
  · have hle : (List.ofFn fun q : Fin len => off + q.val).count x ≤ 1 :=
      List.nodup_iff_count_le_one.mp hnodup x
    have hge : 1 ≤ (List.ofFn fun q : Fin len => off + q.val).count x :=
      List.count_pos_iff.mpr hmem
    rw [List.mem_ofFn] at hmem
    obtain ⟨q, rfl⟩ := hmem
    have hq := q.isLt
    have hrange : off ≤ off + q.val ∧ off + q.val < off + len := ⟨Nat.le_add_right _ _, by omega⟩
    simp only [hrange, and_self, ite_true]
    omega
  · have h0 : (List.ofFn fun q : Fin len => off + q.val).count x = 0 :=
      List.count_eq_zero.mpr hmem
    have hnr : ¬ (off ≤ x ∧ x < off + len) := by
      rintro ⟨h1, h2⟩
      apply hmem
      rw [List.mem_ofFn]
      exact ⟨⟨x - off, by omega⟩, by dsimp only; omega⟩
    simp only [hnr, ite_false]
    exact h0

lemma buildAndGroups_spec (k off f : ℕ) :
    ∀ p : ℕ, off + p * (f + 1) ≤ k →
      let res := buildAndGroups (k + 2) off f p
      res.1.length = p * f ∧
      res.2.length = p ∧
      (∀ g ∈ res.1, g.op = .and ∧ g.inputs.length = 2) ∧
      (∀ j < res.1.length, ∀ i ∈ (res.1.getD j ⟨.or, []⟩).inputs, i < k + 2 + j) ∧
      (∀ o ∈ res.2, o < k + 2 + res.1.length) ∧
      (∀ x,
        (∑ j ∈ Finset.range res.1.length, (res.1.getD j ⟨.or, []⟩).inputs.count x) + res.2.count x =
        (if off ≤ x ∧ x < off + p * (f + 1) then 1 else 0) +
        (if k + 2 ≤ x ∧ x < k + 2 + p * f then 1 else 0)) := by
  intro p
  induction p with
  | zero =>
    intro _
    simp only [buildAndGroups]
    refine ⟨by simp, by simp, by simp, by simp, by simp, fun x => ?_⟩
    have h1 : ¬ (off ≤ x ∧ x < off) := by omega
    have h2 : ¬ (k + 2 ≤ x ∧ x < k + 2) := by omega
    simp [h1, h2]
  | succ p ih =>
    intro hoff
    have hoff_p : off + p * (f + 1) ≤ k := by
      have : p * (f + 1) ≤ (p + 1) * (f + 1) := Nat.mul_le_mul_right _ (Nat.le_succ p)
      omega
    obtain ⟨hlenG, hlenO, hgG, hrbG, hoG, hreads⟩ := ih hoff_p
    simp only [buildAndGroups]
    set prev := buildAndGroups (k + 2) off f p
    set ws := List.ofFn fun q : Fin (f + 1) => off + p * (f + 1) + q.val
    set cur := rchain .and (k + 2 + prev.1.length) ws
    have hws_ne : ws ≠ [] := by simp [ws]
    have hcur_len : cur.1.length = f := by
      rw [rchain_length .and _ ws hws_ne]; simp [ws]
    have hws_lt : ∀ w ∈ ws, w < k + 2 + prev.1.length := by
      intro w hw
      simp only [ws, List.mem_ofFn] at hw
      obtain ⟨q, rfl⟩ := hw
      have hq := q.isLt
      have : off + p * (f + 1) + (f + 1) ≤ k := by rw [Nat.succ_mul] at hoff; omega
      omega
    have hcur_out : cur.2 < k + 2 + prev.1.length + cur.1.length :=
      rchain_out_lt .and (k + 2 + prev.1.length) ws hws_ne hws_lt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, hlenG, hcur_len, Nat.succ_mul]
    · simp only [List.length_cons, hlenO]
    · intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact hgG g h1
      · exact rchain_gates_prop .and _ ws g h2
    · intro j hj i hi
      simp only [List.length_append] at hj
      by_cases hlt : j < prev.1.length
      · rw [List.getD_append _ _ _ _ hlt] at hi
        exact hrbG j hlt i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        have hlt2 : j - prev.1.length < cur.1.length := by omega
        have h := rchain_rb .and (k + 2 + prev.1.length) ws hws_lt (j - prev.1.length) hlt2 i hi
        omega
    · intro o ho
      simp only [List.length_append]
      rcases List.mem_cons.mp ho with rfl | h2
      · omega
      · have := hoG o h2; omega
    · intro x
      have hsum_app : ∑ j ∈ Finset.range (prev.1 ++ cur.1).length,
          ((prev.1 ++ cur.1).getD j ⟨.or, []⟩).inputs.count x =
          (∑ j ∈ Finset.range prev.1.length, (prev.1.getD j ⟨.or, []⟩).inputs.count x) +
          (∑ j ∈ Finset.range cur.1.length, (cur.1.getD j ⟨.or, []⟩).inputs.count x) := by
        rw [List.length_append, Finset.sum_range_add]
        congr 1
        · apply Finset.sum_congr rfl; intro j hj
          rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hj)]
        · apply Finset.sum_congr rfl; intro j _
          rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      rw [hsum_app, List.count_cons]
      have hcr := rchain_reads .and (k + 2 + prev.1.length) ws hws_ne x
      change (∑ j ∈ Finset.range cur.1.length, (cur.1.getD j ⟨.or, []⟩).inputs.count x) +
        (if cur.2 = x then 1 else 0) =
        ws.count x + (if k + 2 + prev.1.length ≤ x ∧ x < k + 2 + prev.1.length + cur.1.length then 1 else 0) at hcr
      rw [hcur_len, list_ofFn_count_range (off + p * (f + 1)) (f + 1) x, hlenG] at hcr
      have hpr := hreads x
      change (∑ j ∈ Finset.range prev.1.length, (prev.1.getD j ⟨.or, []⟩).inputs.count x) + prev.2.count x =
        (if off ≤ x ∧ x < off + p * (f + 1) then 1 else 0) +
        (if k + 2 ≤ x ∧ x < k + 2 + p * f then 1 else 0) at hpr
      simp only [beq_iff_eq]
      rw [Nat.succ_mul, Nat.succ_mul]
      have hA : (if off ≤ x ∧ x < off + p * (f + 1) then 1 else 0) +
          (if off + p * (f + 1) ≤ x ∧ x < off + p * (f + 1) + (f + 1) then 1 else 0) =
          (if off ≤ x ∧ x < off + (p * (f + 1) + (f + 1)) then 1 else 0) := by
        split_ifs <;> omega
      have hB : (if k + 2 ≤ x ∧ x < k + 2 + p * f then 1 else 0) +
          (if k + 2 + p * f ≤ x ∧ x < k + 2 + p * f + f then 1 else 0) =
          (if k + 2 ≤ x ∧ x < k + 2 + (p * f + f) then 1 else 0) := by
        split_ifs <;> omega
      rw [hcur_len]
      omega

lemma buildAndGroups_eval (k off f : ℕ) (x : List Bool) (hxlen : x.length = k + 2) :
    ∀ p : ℕ, off + p * (f + 1) ≤ k →
      let res := buildAndGroups (k + 2) off f p
      res.2.any (fun o => (Circuit.wires ⟨res.1, 0⟩ x).getD o false) =
        decide (∃ r < p, (List.ofFn fun q : Fin (f + 1) => off + r * (f + 1) + q.val).all
          (fun w => x.getD w false) = true) := by
  intro p
  induction p with
  | zero => intro _; simp [buildAndGroups]
  | succ p ih =>
    intro hoff
    have hoff_p : off + p * (f + 1) ≤ k := by
      have : p * (f + 1) ≤ (p + 1) * (f + 1) := Nat.mul_le_mul_right _ (Nat.le_succ p)
      omega
    have hprev_spec := buildAndGroups_spec k off f p hoff_p
    simp only [buildAndGroups]
    set prev := buildAndGroups (k + 2) off f p
    set ws := List.ofFn fun q : Fin (f + 1) => off + p * (f + 1) + q.val
    set cur := rchain .and (k + 2 + prev.1.length) ws
    have hws_ne : ws ≠ [] := by simp [ws]
    have hws_lt_x : ∀ w ∈ ws, w < x.length := by
      intro w hw
      simp only [ws, List.mem_ofFn] at hw
      obtain ⟨q, rfl⟩ := hw
      have hq := q.isLt
      have : off + p * (f + 1) + (f + 1) ≤ k := by rw [Nat.succ_mul] at hoff; omega
      omega
    have hbase_len : (Circuit.wires ⟨prev.1, 0⟩ x).length = k + 2 + prev.1.length := by
      rw [wires_length, hxlen]
    have hcur_eval : (Circuit.wires ⟨prev.1 ++ cur.1, 0⟩ x).getD cur.2 false =
        ws.all (fun w => x.getD w false) := by
      rw [wires_append]
      have h1 := rchain_eval .and (Or.inl rfl) (Circuit.wires ⟨prev.1, 0⟩ x) ws hws_ne
        (fun w hw => by rw [hbase_len]; have := hws_lt_x w hw; omega)
      rw [hbase_len] at h1
      rw [h1]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor
      · intro hall w hw
        have h := hall w hw
        rwa [wires_getD_input ⟨prev.1, 0⟩ x w (hws_lt_x w hw)] at h
      · intro hall w hw
        rw [wires_getD_input ⟨prev.1, 0⟩ x w (hws_lt_x w hw)]
        exact hall w hw
    have hprev_any : prev.2.any (fun o => (Circuit.wires ⟨prev.1 ++ cur.1, 0⟩ x).getD o false) =
        prev.2.any (fun o => (Circuit.wires ⟨prev.1, 0⟩ x).getD o false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor <;> rintro ⟨o, ho, h⟩ <;> refine ⟨o, ho, ?_⟩
      · rwa [wires_prefix prev.1 cur.1 x o (by rw [hxlen]; exact hprev_spec.2.2.2.2.1 o ho)] at h
      · rwa [wires_prefix prev.1 cur.1 x o (by rw [hxlen]; exact hprev_spec.2.2.2.2.1 o ho)]
    simp only [List.any_cons]
    rw [hcur_eval, hprev_any, ih hoff_p]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨r, hr, h⟩)
      · exact ⟨p, Nat.lt_succ_self p, h⟩
      · exact ⟨r, Nat.lt_succ_of_lt hr, h⟩
    · rintro ⟨r, hr, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
      · exact Or.inr ⟨r, hlt, h⟩
      · exact Or.inl h

def buildTreeDNF (k off a f : ℕ) : Circuit :=
  let ag := buildAndGroups (k + 2) off f (a + 1)
  let oc := rchain .or (k + 2 + ag.1.length) ag.2
  ⟨ag.1 ++ oc.1, oc.2⟩

lemma buildTreeDNF_spec (k off a f : ℕ) (hoff : off + (a + 1) * (f + 1) ≤ k) :
    let D := buildTreeDNF k off a f
    FanInTwo D ∧
    ReadsBack (k + 2) D ∧
    D.output < k + 2 + D.size ∧
    (∀ w < k + 2 + D.size, readsIn D (Finset.range D.size) w +
      (if D.output = w then 1 else 0) ≤ 1) ∧
    notCount D = 0 ∧
    D.size = (a + 1) * (f + 1) - 1 ∧
    ∀ Y : Finset (Fin k),
      (D.wires (bitsOf Y)).getD D.output false =
        decide (∃ r < a + 1, ∀ q < f + 1,
          ∃ hlt : off + r * (f + 1) + q < k, (⟨off + r * (f + 1) + q, hlt⟩ : Fin k) ∈ Y) := by
  have hAG := buildAndGroups_spec k off f (a + 1) hoff
  set ag := buildAndGroups (k + 2) off f (a + 1)
  set oc := rchain .or (k + 2 + ag.1.length) ag.2
  have houts_ne : ag.2 ≠ [] := by intro h; have := hAG.2.1; simp [h] at this
  have hoc_len : oc.1.length = a := by
    rw [rchain_length .or _ ag.2 houts_ne, hAG.2.1]; omega
  have hD_len : (buildTreeDNF k off a f).size = (a + 1) * (f + 1) - 1 := by
    simp only [buildTreeDNF, Circuit.size, List.length_append]
    change ag.1.length + oc.1.length = (a + 1) * (f + 1) - 1
    rw [hAG.1, hoc_len, Nat.mul_succ]; omega
  have hFit : FanInTwo (buildTreeDNF k off a f) := by
    intro g hg
    simp only [buildTreeDNF, List.mem_append] at hg
    rcases hg with h1 | h2
    · obtain ⟨hop, hlen⟩ := hAG.2.2.1 g h1
      exact ⟨by simp [hop], by omega⟩
    · obtain ⟨hop, hlen⟩ := rchain_gates_prop .or _ ag.2 g h2
      exact ⟨by simp [hop], by omega⟩
  have hRB : ReadsBack (k + 2) (buildTreeDNF k off a f) := by
    intro j hj i hi
    simp only [buildTreeDNF, gateAt, List.length_append] at hj hi
    change j < ag.1.length + oc.1.length at hj
    change i ∈ ((ag.1 ++ oc.1).getD j ⟨.or, []⟩).inputs at hi
    by_cases hlt : j < ag.1.length
    · rw [List.getD_append _ _ _ _ hlt] at hi
      exact hAG.2.2.2.1 j hlt i hi
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      have h := rchain_rb .or (k + 2 + ag.1.length) ag.2 hAG.2.2.2.2.1 (j - ag.1.length) (by change j - ag.1.length < oc.1.length; omega) i hi
      omega
  have hOut : (buildTreeDNF k off a f).output < k + 2 + (buildTreeDNF k off a f).size := by
    simp only [buildTreeDNF, Circuit.size, List.length_append]
    change oc.2 < k + 2 + (ag.1.length + oc.1.length)
    have h : oc.2 < k + 2 + ag.1.length + oc.1.length :=
      rchain_out_lt .or (k + 2 + ag.1.length) ag.2 houts_ne hAG.2.2.2.2.1
    omega
  have hTree : ∀ w < k + 2 + (buildTreeDNF k off a f).size,
      readsIn (buildTreeDNF k off a f) (Finset.range (buildTreeDNF k off a f).size) w +
      (if (buildTreeDNF k off a f).output = w then 1 else 0) ≤ 1 := by
    intro w _
    simp only [buildTreeDNF, readsIn, gateAt, Circuit.size, List.length_append]
    change (∑ j ∈ Finset.range (ag.1.length + oc.1.length),
      ((ag.1 ++ oc.1).getD j ⟨.or, []⟩).inputs.count w) + (if oc.2 = w then 1 else 0) ≤ 1
    rw [Finset.sum_range_add]
    have h1 : ∑ j ∈ Finset.range ag.1.length,
        ((ag.1 ++ oc.1).getD j ⟨.or, []⟩).inputs.count w =
        ∑ j ∈ Finset.range ag.1.length, (ag.1.getD j ⟨.or, []⟩).inputs.count w := by
      apply Finset.sum_congr rfl; intro j hj
      rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hj)]
    have h2 : ∑ j ∈ Finset.range oc.1.length,
        ((ag.1 ++ oc.1).getD (ag.1.length + j) ⟨.or, []⟩).inputs.count w =
        ∑ j ∈ Finset.range oc.1.length, (oc.1.getD j ⟨.or, []⟩).inputs.count w := by
      apply Finset.sum_congr rfl; intro j _
      rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    rw [h1, h2]
    have hr1 := hAG.2.2.2.2.2 w
    change (∑ j ∈ Finset.range ag.1.length, (ag.1.getD j ⟨.or, []⟩).inputs.count w) + ag.2.count w =
      (if off ≤ w ∧ w < off + (a + 1) * (f + 1) then 1 else 0) +
      (if k + 2 ≤ w ∧ w < k + 2 + (a + 1) * f then 1 else 0) at hr1
    have hr2 := rchain_reads .or (k + 2 + ag.1.length) ag.2 houts_ne w
    change (∑ j ∈ Finset.range oc.1.length, (oc.1.getD j ⟨.or, []⟩).inputs.count w) +
      (if oc.2 = w then 1 else 0) =
      ag.2.count w + (if k + 2 + ag.1.length ≤ w ∧ w < k + 2 + ag.1.length + oc.1.length then 1 else 0) at hr2
    rw [hAG.1, hoc_len] at hr2
    have htot : (∑ j ∈ Finset.range ag.1.length, (ag.1.getD j ⟨.or, []⟩).inputs.count w) +
        (∑ j ∈ Finset.range oc.1.length, (oc.1.getD j ⟨.or, []⟩).inputs.count w) +
        (if oc.2 = w then 1 else 0) =
        (if off ≤ w ∧ w < off + (a + 1) * (f + 1) then 1 else 0) +
        (if k + 2 ≤ w ∧ w < k + 2 + (a + 1) * f then 1 else 0) +
        (if k + 2 + (a + 1) * f ≤ w ∧ w < k + 2 + (a + 1) * f + a then 1 else 0) := by
      rw [hoc_len]
      omega
    rw [htot]
    split_ifs <;> omega
  have hNot : notCount (buildTreeDNF k off a f) = 0 := by
    unfold notCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro g hg
    simp only [buildTreeDNF, List.mem_append] at hg
    rcases hg with h1 | h2
    · have := (hAG.2.2.1 g h1).1; simp [this]
    · have := (rchain_gates_prop .or _ ag.2 g h2).1; simp [this]
  refine ⟨hFit, hRB, hOut, hTree, hNot, hD_len, ?_⟩
  intro Y
  simp only [buildTreeDNF]
  rw [wires_append]
  have hbase_len : (Circuit.wires ⟨ag.1, 0⟩ (bitsOf Y)).length = k + 2 + ag.1.length := by
    rw [wires_length, bitsOf_length]
  have hev := rchain_eval .or (Or.inr rfl) (Circuit.wires ⟨ag.1, 0⟩ (bitsOf Y)) ag.2 houts_ne
    (fun o ho => by rw [hbase_len]; exact hAG.2.2.2.2.1 o ho)
  rw [hbase_len] at hev
  rw [hev]
  rw [buildAndGroups_eval k off f (bitsOf Y) (bitsOf_length Y) (a + 1) hoff]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨r, hr, hall⟩
    refine ⟨r, hr, fun q hq => ?_⟩
    have hlt : off + r * (f + 1) + q < k := by
      have : r * (f + 1) + (f + 1) ≤ (a + 1) * (f + 1) := by
        calc r * (f + 1) + (f + 1) = (r + 1) * (f + 1) := (Nat.succ_mul r (f + 1)).symm
          _ ≤ (a + 1) * (f + 1) := Nat.mul_le_mul_right _ hr
      omega
    refine ⟨hlt, ?_⟩
    have hmem : off + r * (f + 1) + q ∈ List.ofFn fun q' : Fin (f + 1) => off + r * (f + 1) + q'.val := by
      rw [List.mem_ofFn]; exact ⟨⟨q, hq⟩, rfl⟩
    have htrue := hall _ hmem
    rw [bitsOf_getD_lt Y _ hlt] at htrue
    exact of_decide_eq_true htrue
  · rintro ⟨r, hr, hall⟩
    refine ⟨r, hr, fun w hw => ?_⟩
    rw [List.mem_ofFn] at hw
    obtain ⟨q, rfl⟩ := hw
    obtain ⟨hlt, hmemY⟩ := hall q.val q.isLt
    rw [bitsOf_getD_lt Y _ hlt]
    exact decide_eq_true hmemY

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

lemma lower_bound_main (n k : ℕ) (R : Fin n → Fin n → Prop) (S : Finset (Fin n)) (a f : Fin n → ℕ)
    (hTrans : ∀ i j h, R i j → R j h → R i h)
    (hAnti : ∀ i j, R i j → R j i → i = j)
    (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → Circuit)
    (hMono : ∀ A B, (∀ i j, j ∈ A → R i j → i ∈ A) → (∀ i j, j ∈ B → R i j → i ∈ B) →
      A ⊆ B → g A ⊆ g B)
    (hValid : ∀ i, FanInTwo (D i) ∧ ReadsBack (k + 2) (D i) ∧ (D i).output < k + 2 + (D i).size ∧
      (i ∈ S → ∀ w < k + 2 + (D i).size, readsIn (D i) (Finset.range (D i).size) w +
        (if (D i).output = w then 1 else 0) ≤ 1))
    (hRec : ∀ A, (∀ i j, j ∈ A → R i j → i ∈ A) → ∀ Y i, (g A \ Y).card ≤ a i → (Y \ g A).card ≤ f i →
      ((D i).wires (bitsOf Y)).getD (D i).output false = decide (i ∈ A)) :
    Finset.univ.sum (fun i => if i ∈ S then (a i + 1) * (f i + 1) else a i + f i + 1) ≤ k := by
  let ideal := fun (A : Finset (Fin n)) => ∀ i j, j ∈ A → R i j → i ∈ A
  let cost := fun i => if i ∈ S then (a i + 1) * (f i + 1) else a i + f i + 1
  suffices hA : ∀ m : ℕ, ∀ A : Finset (Fin n), ideal A → (Finset.univ \ A).card = m →
      ∑ i ∈ Finset.univ \ A, cost i ≤ (g Finset.univ \ g A).card by
    have h0 := hA (Finset.univ \ (∅ : Finset (Fin n))).card ∅ (by intro _ _ h; simp at h) rfl
    simp only [Finset.sdiff_empty] at h0
    calc ∑ i : Fin n, cost i ≤ (g Finset.univ \ g ∅).card := h0
      _ ≤ (g Finset.univ).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = k := by simp
  intro m
  induction m with
  | zero =>
    intro A _ hcard
    rw [Finset.card_eq_zero.mp hcard]; simp
  | succ m ih =>
    intro A hA hcard
    have hne : (Finset.univ \ A).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi_mem, hi_min⟩ := poset_minimal R hTrans hAnti (Finset.univ \ A) hne
    have hi_notA : i ∉ A := (Finset.mem_sdiff.mp hi_mem).2
    let A' := insert i A
    have hA' : ideal A' := by
      intro x y hy Rxy
      simp only [A', Finset.mem_insert] at hy ⊢
      rcases hy with rfl | hyA
      · by_cases hxA : x ∈ A
        · exact Or.inr hxA
        · left; exact hi_min x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxA⟩) Rxy
      · exact Or.inr (hA x y hyA Rxy)
    have hrem : Finset.univ \ A = insert i (Finset.univ \ A') := by
      ext x; simp only [A', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_univ, true_and]
      by_cases hx : x = i
      · subst hx; simp [hi_notA]
      · simp [hx]
    have hi_not_rem' : i ∉ Finset.univ \ A' := by simp [A']
    have hcard' : (Finset.univ \ A').card = m := by
      rw [hrem, Finset.card_insert_of_notMem hi_not_rem'] at hcard; omega
    have hIH := ih A' hA' hcard'
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
      have hrecA : ∀ Y, (g A \ Y).card ≤ a i → (Y \ g A).card ≤ f i →
          ((D i).wires (bitsOf Y)).getD (D i).output false = false := by
        intro Y h1 h2; rw [hRec A hA Y i h1 h2]; simp [hi_notA]
      have hrecA' : ∀ Y, (g A' \ Y).card ≤ a i → (Y \ g A').card ≤ f i →
          ((D i).wires (bitsOf Y)).getD (D i).output false = true := by
        intro Y h1 h2; rw [hRec A' hA' Y i h1 h2]; simp [A']
      by_cases hiS : i ∈ S
      · simp only [cost, hiS, ite_true]
        obtain ⟨hF, hR, hO, hT⟩ := hValid i
        exact lower_step_tree (D i) hF hR hO (hT hiS) (g A) (g A') hsub1 hrecA hrecA'
      · simp only [cost, hiS, ite_false]
        exact lower_step_general (D i) (g A) (g A') hsub1 hrecA hrecA'
    rw [hrem, Finset.sum_insert hi_not_rem', hpart]
    omega

lemma upper_bound_main (n k : ℕ) (S : Finset (Fin n)) (a f : Fin n → ℕ)
    (hk : Finset.univ.sum (fun i => if i ∈ S then (a i + 1) * (f i + 1) else a i + f i + 1) ≤ k) :
    let cost := fun i => if i ∈ S then (a i + 1) * (f i + 1) else a i + f i + 1
    let t := fun i => a i + f i + 1
    ∃ (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → Circuit),
      (∀ A B, A ⊆ B → g A ⊆ g B) ∧
      (∀ i, FanInTwo (D i) ∧ ReadsBack (k + 2) (D i) ∧ (D i).output < k + 2 + (D i).size ∧
        (i ∈ S → ∀ w < k + 2 + (D i).size, readsIn (D i) (Finset.range (D i).size) w +
          (if (D i).output = w then 1 else 0) ≤ 1)) ∧
      (∀ A Y i, (g A \ Y).card ≤ a i → (Y \ g A).card ≤ f i →
        ((D i).wires (bitsOf Y)).getD (D i).output false = decide (i ∈ A)) ∧
      (∃ pin : Fin k → Option (Fin n), ∀ A j, j ∈ g A ↔ ∃ i ∈ A, pin j = some i) ∧
      (∀ i, notCount (D i) = 0 ∧ (D i).size ≤ if i ∈ S then cost i - 1 else 2 * (t i + 1) ^ 2) := by
  classical
  let cost := fun i => if i ∈ S then (a i + 1) * (f i + 1) else a i + f i + 1
  let t := fun i => a i + f i + 1
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
    if i ∈ S then buildTreeDNF k (off i) (a i) (f i)
    else buildThresh k (off i) (t i) (f i)
  refine ⟨g, D, ?_, ?_, ?_, ⟨pin, fun A j => by simp [g]⟩, ?_⟩
  · intro A B hAB j hj
    simp only [g, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨i, hiA, hp⟩ := hj
    exact ⟨i, hAB hiA, hp⟩
  · intro i
    by_cases hiS : i ∈ S
    · have hc : off i + (a i + 1) * (f i + 1) ≤ k := by simpa [cost, hiS] using hoff_le i
      have hsp := buildTreeDNF_spec k (off i) (a i) (f i) hc
      simp only [D, hiS, ite_true]
      exact ⟨hsp.1, hsp.2.1, hsp.2.2.1, fun _ => hsp.2.2.2.1⟩
    · have hc : off i + t i ≤ k := by simpa [cost, t, hiS] using hoff_le i
      have hsp := buildThresh_spec k (off i) (t i) (f i) hc (by dsimp [t]; omega)
      simp only [D, hiS, ite_false]
      exact ⟨hsp.1, hsp.2.1, hsp.2.2.1, fun h => False.elim h⟩
  · intro A Y i hloss hgain
    have hblock_in : ∀ (d : ℕ) (hd : d < cost i) (hlt : off i + d < k),
        (⟨off i + d, hlt⟩ : Fin k) ∈ g A ↔ i ∈ A := by
      intro d hd hlt
      simp only [g, Finset.mem_filter, Finset.mem_univ, true_and]
      have hp : pin ⟨off i + d, hlt⟩ = some i := (hpin_eq i ⟨off i + d, hlt⟩).mpr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hd _⟩
      constructor
      · rintro ⟨i', hi'A, hp'⟩
        rw [hp] at hp'; cases hp'; exact hi'A
      · intro hiA; exact ⟨i, hiA, hp⟩
    by_cases hiS : i ∈ S
    · have hcost : cost i = (a i + 1) * (f i + 1) := by simp [cost, hiS]
      have hc : off i + (a i + 1) * (f i + 1) ≤ k := by simpa [hcost] using hoff_le i
      have hsp := buildTreeDNF_spec k (off i) (a i) (f i) hc
      simp only [D, hiS, ite_true]
      rw [hsp.2.2.2.2.2.2 Y]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨r, hr, hall⟩
        by_contra hniA
        let grp : Finset (Fin k) := (Finset.range (f i + 1)).attach.image fun ⟨q, hq⟩ =>
          ⟨off i + r * (f i + 1) + q, by
            have hq' := Finset.mem_range.mp hq
            have : r * (f i + 1) + (f i + 1) ≤ (a i + 1) * (f i + 1) := by
              calc r * (f i + 1) + (f i + 1) = (r + 1) * (f i + 1) := (Nat.succ_mul _ _).symm
                _ ≤ (a i + 1) * (f i + 1) := Nat.mul_le_mul_right _ hr
            omega⟩
        have hgrp_card : grp.card = f i + 1 := by
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
          have hd : r * (f i + 1) + q < cost i := by
            rw [hcost]
            have : r * (f i + 1) + (f i + 1) ≤ (a i + 1) * (f i + 1) := by
              calc r * (f i + 1) + (f i + 1) = (r + 1) * (f i + 1) := (Nat.succ_mul _ _).symm
                _ ≤ (a i + 1) * (f i + 1) := Nat.mul_le_mul_right _ hr
            omega
          have hmemA := hblock_in (r * (f i + 1) + q) hd (by omega)
          have heq : (⟨off i + r * (f i + 1) + q, hlt⟩ : Fin k) = ⟨off i + (r * (f i + 1) + q), by omega⟩ := by
            ext; simp [Nat.add_assoc]
          rw [heq, hmemA]; exact hniA
        have := Finset.card_le_card hgrp_sub
        omega
      · intro hiA
        by_contra hno
        push_neg at hno
        have hpick : ∀ r ∈ Finset.range (a i + 1),
            ∃ q < f i + 1, ∃ hlt : off i + r * (f i + 1) + q < k,
              (⟨off i + r * (f i + 1) + q, hlt⟩ : Fin k) ∈ g A \ Y := by
          intro r hr
          have hr' := Finset.mem_range.mp hr
          obtain ⟨q, hq, hnotY⟩ := hno r hr'
          have hd : r * (f i + 1) + q < cost i := by
            rw [hcost]
            have : r * (f i + 1) + (f i + 1) ≤ (a i + 1) * (f i + 1) := by
              calc r * (f i + 1) + (f i + 1) = (r + 1) * (f i + 1) := (Nat.succ_mul _ _).symm
                _ ≤ (a i + 1) * (f i + 1) := Nat.mul_le_mul_right _ hr'
            omega
          have hlt : off i + r * (f i + 1) + q < k := by omega
          refine ⟨q, hq, hlt, Finset.mem_sdiff.mpr ⟨?_, fun h => hnotY hlt h⟩⟩
          have hmemA := (hblock_in (r * (f i + 1) + q) hd (by omega)).mpr hiA
          have heq : (⟨off i + r * (f i + 1) + q, hlt⟩ : Fin k) = ⟨off i + (r * (f i + 1) + q), by omega⟩ := by
            ext; simp [Nat.add_assoc]
          rwa [heq]
        choose qf hqf hltf hmemf using hpick
        let lostS : Finset (Fin k) := (Finset.range (a i + 1)).attach.image fun ⟨r, hr⟩ =>
          ⟨off i + r * (f i + 1) + qf r hr, hltf r hr⟩
        have hcardL : lostS.card = a i + 1 := by
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
              · have : (r1 + 1) * (f i + 1) ≤ r2 * (f i + 1) := Nat.mul_le_mul_right _ hlt
                rw [Nat.succ_mul] at this; omega
              · have : (r2 + 1) * (f i + 1) ≤ r1 * (f i + 1) := Nat.mul_le_mul_right _ hgt
                rw [Nat.succ_mul] at this; omega
            ext; exact hreq
        have hsubL : lostS ⊆ g A \ Y := by
          intro x hx
          simp only [lostS, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx
          obtain ⟨r, hr, rfl⟩ := hx
          exact hmemf r hr
        have := Finset.card_le_card hsubL
        omega
    · have hcost : cost i = t i := by simp [cost, t, hiS]
      have hc : off i + t i ≤ k := by simpa [hcost] using hoff_le i
      have hsp := buildThresh_spec k (off i) (t i) (f i) hc (by dsimp [t]; omega)
      simp only [D, hiS, ite_false]
      rw [hsp.2.2.2.2.2 Y]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      let hit := (Finset.range (t i)).filter fun j =>
        ∃ hlt : off i + j < k, (⟨off i + j, hlt⟩ : Fin k) ∈ Y
      constructor
      · intro hhit
        by_contra hniA
        let hitPins : Finset (Fin k) := hit.attach.image fun ⟨j, hj⟩ =>
          ⟨off i + j, by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega⟩
        have hcardH : hitPins.card = hit.card := by
          rw [Finset.card_image_of_injective]
          · simp
          · intro ⟨j1, _⟩ ⟨j2, _⟩ heq
            have := congrArg Fin.val heq; simp at this; ext; omega
        have hsubH : hitPins ⊆ Y \ g A := by
          intro x hx
          simp only [hitPins, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          obtain ⟨hjR, _, hjY⟩ := Finset.mem_filter.mp hj
          have hjlt := Finset.mem_range.mp hjR
          refine Finset.mem_sdiff.mpr ⟨hjY, ?_⟩
          rw [hblock_in j (by rw [hcost]; exact hjlt) (by omega)]
          exact hniA
        have hle := Finset.card_le_card hsubH
        rw [hcardH] at hle
        change f i + 1 ≤ hit.card at hhit
        omega
      · intro hiA
        by_contra hlt
        push_neg at hlt
        let miss := (Finset.range (t i)) \ hit
        have hmiss_card : miss.card = t i - hit.card := by
          rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_range]
        let missPins : Finset (Fin k) := miss.attach.image fun ⟨j, hj⟩ =>
          ⟨off i + j, by have := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1; omega⟩
        have hcardM : missPins.card = miss.card := by
          rw [Finset.card_image_of_injective]
          · simp
          · intro ⟨j1, _⟩ ⟨j2, _⟩ heq
            have := congrArg Fin.val heq; simp at this; ext; omega
        have hsubM : missPins ⊆ g A \ Y := by
          intro x hx
          simp only [missPins, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          obtain ⟨hjR, hjnhit⟩ := Finset.mem_sdiff.mp hj
          have hjlt := Finset.mem_range.mp hjR
          refine Finset.mem_sdiff.mpr ⟨(hblock_in j (by rw [hcost]; exact hjlt) (by omega)).mpr hiA, ?_⟩
          intro hjY
          exact hjnhit (Finset.mem_filter.mpr ⟨hjR, by omega, hjY⟩)
        have hle := Finset.card_le_card hsubM
        rw [hcardM, hmiss_card] at hle
        change hit.card < f i + 1 at hlt
        have ht : t i = a i + f i + 1 := rfl
        omega
  · intro i
    by_cases hiS : i ∈ S
    · have hc : off i + (a i + 1) * (f i + 1) ≤ k := by simpa [cost, hiS] using hoff_le i
      have hsp := buildTreeDNF_spec k (off i) (a i) (f i) hc
      simp only [D, hiS, ite_true]
      exact ⟨hsp.2.2.2.2.1, le_of_eq hsp.2.2.2.2.2.1⟩
    · have hc : off i + t i ≤ k := by simpa [cost, t, hiS] using hoff_le i
      have hsp := buildThresh_spec k (off i) (t i) (f i) hc (by dsimp [t]; omega)
      simp only [D, hiS, ite_false]
      exact ⟨hsp.2.2.2.1, hsp.2.2.2.2.1⟩

end PEqualNP.Outside.L_lib_1450_aux

theorem PEqualNP.Outside.L_lib_1450 :
letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (n k : Nat) (R : Fin n → Fin n → Prop) (S : Finset (Fin n)) (a f : Fin n → Nat),
  (∀ i, R i i) → (∀ i j h, R i j → R j h → R i h) → (∀ i j, R i j → R j i → i = j) →
  let ideal := fun (A : Finset (Fin n)) => ∀ i j, j ∈ A → R i j → i ∈ A
  let bits := fun (Y : Finset (Fin k)) => List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true]
  let t := fun i => a i+f i+1
  let cost := fun i => if i ∈ S then (a i+1)*(f i+1) else t i
  let tree := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∀ j < k+2+D.size, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) j +
      (if D.output=j then 1 else 0) ≤ 1
  let fit := fun (bounded : Prop) =>
    ∃ (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → PEqualNP.CircuitLowerBounds.Circuit),
      (∀ A B, ideal A → ideal B → A ⊆ B → g A ⊆ g B) ∧
      (∀ i, PEqualNP.MetaComplexity.FanInTwo (D i) ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) (D i) ∧ (D i).output < k+2+(D i).size ∧
        (i ∈ S → tree (D i))) ∧
      (∀ A, ideal A → ∀ Y i, (g A \ Y).card ≤ a i → (Y \ g A).card ≤ f i →
        ((D i).wires (bits Y)).getD (D i).output false = decide (i ∈ A)) ∧
      (bounded → (∃ pin : Fin k → Option (Fin n), ∀ A j, j ∈ g A ↔ ∃ i ∈ A, pin j=some i) ∧
        ∀ i, PEqualNP.NotBracket.notCount (D i)=0 ∧
          (D i).size ≤ if i ∈ S then cost i-1 else 2*(t i+1)^2)
  (fit False ↔ (Finset.univ.sum cost ≤ k)) ∧ ((Finset.univ.sum cost ≤ k) → fit True) := by
  intro n k R S a f _ hTrans hAnti
  have hbits : ∀ Y : Finset (Fin k),
      (List.ofFn (fun j : Fin k => @decide (j ∈ Y) (Classical.propDecidable _)) ++ [false, true]) =
      PEqualNP.Outside.L_lib_1450_aux.bitsOf Y := by
    intro Y
    unfold PEqualNP.Outside.L_lib_1450_aux.bitsOf
    congr 1; congr 1; funext j; congr 1
  have hdec : ∀ (i : Fin n) (A : Finset (Fin n)),
      @decide (i ∈ A) (Classical.propDecidable _) = decide (i ∈ A) := fun _ _ => by congr 1
  have hite : ∀ (i : Fin n) (x y : ℕ),
      @ite ℕ (i ∈ S) (Classical.propDecidable _) x y = if i ∈ S then x else y := fun _ _ _ => by congr 1
  have hiteNat : ∀ (p q : ℕ) (x y : ℕ),
      @ite ℕ (p = q) (Classical.propDecidable _) x y = if p = q then x else y := fun _ _ _ _ => by congr 1
  have hsdiff : ∀ (X Y : Finset (Fin k)),
      @sdiff (Finset (Fin k)) (@Finset.instSDiff (Fin k) fun x y => Classical.propDecidable (x = y)) X Y = X \ Y := by
    intro X Y; ext x; simp
  have hsum : (∑ i : Fin n, @ite ℕ (i ∈ S) (Classical.propDecidable _) ((a i + 1) * (f i + 1)) (a i + f i + 1)) =
      ∑ i : Fin n, if i ∈ S then (a i + 1) * (f i + 1) else a i + f i + 1 := by
    apply Finset.sum_congr rfl; intro i _; exact hite i _ _
  have hup_core : (∑ i : Fin n, if i ∈ S then (a i + 1) * (f i + 1) else a i + f i + 1) ≤ k →
      ∃ (g : Finset (Fin n) → Finset (Fin k)) (D : Fin n → PEqualNP.CircuitLowerBounds.Circuit),
        (∀ A B, (∀ i j, j ∈ A → R i j → i ∈ A) → (∀ i j, j ∈ B → R i j → i ∈ B) → A ⊆ B → g A ⊆ g B) ∧
        (∀ i, PEqualNP.MetaComplexity.FanInTwo (D i) ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + 2) (D i) ∧ (D i).output < k + 2 + (D i).size ∧
          (i ∈ S → ∀ j < k + 2 + (D i).size,
            PEqualNP.MetaComplexity.NestedCover.readsIn (D i) (Finset.range (D i).size) j +
            @ite ℕ ((D i).output = j) (Classical.propDecidable _) 1 0 ≤ 1)) ∧
        (∀ A, (∀ i j, j ∈ A → R i j → i ∈ A) → ∀ Y i,
          (@sdiff (Finset (Fin k)) (@Finset.instSDiff (Fin k) fun x y => Classical.propDecidable (x = y)) (g A) Y).card ≤ a i →
          (@sdiff (Finset (Fin k)) (@Finset.instSDiff (Fin k) fun x y => Classical.propDecidable (x = y)) Y (g A)).card ≤ f i →
          ((D i).wires (List.ofFn (fun j : Fin k => @decide (j ∈ Y) (Classical.propDecidable _)) ++ [false, true])).getD (D i).output false =
          @decide (i ∈ A) (Classical.propDecidable _)) ∧
        (True → (∃ pin : Fin k → Option (Fin n), ∀ A j, j ∈ g A ↔ ∃ i ∈ A, pin j = some i) ∧
          ∀ i, PEqualNP.NotBracket.notCount (D i) = 0 ∧
            (D i).size ≤ @ite ℕ (i ∈ S) (Classical.propDecidable _)
              (@ite ℕ (i ∈ S) (Classical.propDecidable _) ((a i + 1) * (f i + 1)) (a i + f i + 1) - 1)
              (2 * (a i + f i + 1 + 1) ^ 2)) := by
    intro hk
    obtain ⟨g, D, hM, hV, hR, hP, hS⟩ := PEqualNP.Outside.L_lib_1450_aux.upper_bound_main n k S a f hk
    refine ⟨g, D, fun A B _ _ hAB => hM A B hAB, ?_, ?_, fun _ => ⟨hP, ?_⟩⟩
    · intro i
      obtain ⟨h1, h2, h3, h4⟩ := hV i
      refine ⟨h1, h2, h3, fun hiS j hj => ?_⟩
      rw [hiteNat]; exact h4 hiS j hj
    · intro A _ Y i h1 h2
      rw [hsdiff] at h1 h2
      rw [hbits Y, hdec i A]
      exact hR A Y i h1 h2
    · intro i
      obtain ⟨hn, hs⟩ := hS i
      refine ⟨hn, ?_⟩
      rw [hite i, hite i]
      exact hs
  refine ⟨⟨?_, ?_⟩, fun hk => hup_core (hsum ▸ hk)⟩
  · rintro ⟨g, D, hM, hV, hR, _⟩
    rw [hsum]
    apply PEqualNP.Outside.L_lib_1450_aux.lower_bound_main n k R S a f hTrans hAnti g D hM
    · intro i
      obtain ⟨h1, h2, h3, h4⟩ := hV i
      refine ⟨h1, h2, h3, fun hiS j hj => ?_⟩
      have := h4 hiS j hj
      rwa [hiteNat] at this
    · intro A hA Y i h1 h2
      have h := hR A hA Y i (by rwa [hsdiff]) (by rwa [hsdiff])
      dsimp only at h
      rw [hbits Y, hdec i A] at h
      exact h
  · intro hk
    obtain ⟨g, D, hM, hV, hR, _⟩ := hup_core (hsum ▸ hk)
    exact ⟨g, D, hM, hV, hR, fun hf => False.elim hf⟩
