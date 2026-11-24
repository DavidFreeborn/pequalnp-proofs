import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3064

def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

lemma factor_support {ι : Type} [DecidableEq ι]
    (F f g : (ι → Bool) → Bool)
    (hfg : ∀ x, F x = true ↔ f x = true ∧ g x = true)
    (hp : ∀ u v : ι, ∃ x, F x = false ∧
      F (Function.update x u true) = true ∧
      F (Function.update x v true) = true) :
    (∀ i : ι, ∃ x, f (Function.update x i true) ≠ f x) ∨
    (∀ i : ι, ∃ x, g (Function.update x i true) ≠ g x) := by
  classical
  by_cases hf : ∀ i : ι, ∃ x, f (Function.update x i true) ≠ f x
  · exact Or.inl hf
  · right
    push_neg at hf
    obtain ⟨u, hu⟩ := hf
    intro v
    by_contra hv
    push_neg at hv
    obtain ⟨x, hx, hxu, hxv⟩ := hp u v
    have hfx : f x = true := by
      have h := ((hfg _).mp hxu).1
      rwa [hu x] at h
    have hgx : g x = true := by
      have h := ((hfg _).mp hxv).2
      rwa [hv x] at h
    have h := (hfg x).mpr ⟨hfx, hgx⟩
    rw [hx] at h
    contradiction

set_option maxHeartbeats 2000000 in
lemma pair_witness : ∀ u v : Fin 9, ∃ x : Fin 9 → Bool,
    edgeF x = false ∧ edgeF (Function.update x u true) = true ∧
    edgeF (Function.update x v true) = true := by
  decide +kernel

lemma final_and_support (f g : (Fin 9 → Bool) → Bool)
    (h : ∀ x, edgeF x = true ↔ f x = true ∧ g x = true) :
    (∀ i : Fin 9, ∃ x, f (Function.update x i true) ≠ f x) ∨
    (∀ i : Fin 9, ∃ x, g (Function.update x i true) ≠ g x) := by
  exact factor_support edgeF f g h pair_witness

end PEqualNP.Outside.L_meta_3064
