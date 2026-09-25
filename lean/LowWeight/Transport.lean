import LowWeight.Bridge
import LowWeight.Normalize

/-! Transporting span membership along a linear automorphism of `Pauli n`. -/

namespace LowWeight

variable {m n : ℕ}

theorem mem_span_map_iff (T : Pauli n ≃ₗ[F] Pauli n) (g : Fin m → Pauli n) (v : Pauli n) :
    v ∈ Submodule.span F (Set.range fun i => T (g i)) ↔
      T.symm v ∈ Submodule.span F (Set.range g) := by
  have hr : (Set.range fun i => T (g i)) = (T.toLinearMap : Pauli n → Pauli n) '' Set.range g := by
    ext v; simp
  rw [hr, Submodule.span_image]
  constructor
  · rintro ⟨u, hu, rfl⟩; simpa using hu
  · intro h; exact ⟨T.symm v, h, by simp⟩

end LowWeight
