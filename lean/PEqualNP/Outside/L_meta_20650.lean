import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_20650.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
def witness : Circuit := ⟨[⟨.or, [5, 6]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.and, [4, 13]⟩,
    ⟨.or, [11, 14]⟩], 15⟩
theorem mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem correct : Represents (fun u v : Fin 5 => (15826944 : ℕ).testBit (5*u.val+v.val)) witness := by
  decide +kernel
end PEqualNP.Outside.L_meta_20650.Helpers


theorem PEqualNP.Outside.L_meta_20650 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15826944 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  exact ⟨PEqualNP.Outside.L_meta_20650.Helpers.witness, PEqualNP.Outside.L_meta_20650.Helpers.mono, by decide, PEqualNP.Outside.L_meta_20650.Helpers.correct⟩
