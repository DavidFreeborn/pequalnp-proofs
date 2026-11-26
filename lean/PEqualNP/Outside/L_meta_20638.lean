import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20638 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (5341184 : ℕ).testBit (5 * u.val + v.val)) 5) := by
  try unfold PEqualNP.Represents.RepSizeAtMost
  try unfold PEqualNP.MetaComplexity.HasCircuitSize
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  all_goals first
    | (intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp)
    | decide
    | (unfold PEqualNP.Represents.Represents; decide)
