import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4504

set_option maxHeartbeats 4000000 in
def C13 : Circuit :=
  { gates :=
      [ ⟨.and, [1, 2]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [4, 6]⟩,
        ⟨.and, [5, 7]⟩, ⟨.and, [7, 4]⟩,
        ⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩,
        ⟨.or, [14, 15]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [19, 0]⟩ ],
    output := 20 }

set_option maxHeartbeats 4000000 in
theorem fanInTwo_C13 : FanInTwo C13 := by
  intro g hg
  simp only [C13, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by simp, by decide⟩

theorem size_C13 : C13.size ≤ 13 := by
  simp [C13, Circuit.size]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem eval_C13 : ∀ x : Fin 8 → Bool,
    C13.eval (List.ofFn x) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4 || x 0 || x 3) := by
  decide

theorem refuted : HasCircuitSize (8 : ℕ)
    (fun (x1 : Fin (8 : ℕ) → Bool) =>
      x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) ||
      x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) ||
      x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) ||
      x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) ||
      x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) ||
      x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
      x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) ||
      x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
      x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) ||
      x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) ||
      x1 (0 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)))
    (13 : ℕ) :=
  ⟨C13, fanInTwo_C13, size_C13, eval_C13⟩

end PEqualNP.Outside.L_meta_4504

theorem PEqualNP.Outside.L_meta_4504 :
    ¬ (¬ PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ)
      (fun (x1 : Fin (8 : ℕ) → Bool) =>
        x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) ||
        x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) ||
        x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) ||
        x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) ||
        x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) ||
        x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
        x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) ||
        x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) ||
        x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) ||
        x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) ||
        x1 (0 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)))
      (13 : ℕ)) := by
  intro h
  exact h PEqualNP.Outside.L_meta_4504.refuted
