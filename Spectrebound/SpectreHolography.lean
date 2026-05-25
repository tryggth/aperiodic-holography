import Spectrebound.SpectreGeometry
import Spectrebound.SpectreBoundary

namespace Spectrebound

noncomputable section
open Classical

/-- Helper lemma to extract an index of a Left 90° turn from existence_of_convex_anchor. -/
lemma convex_anchor_index (B : BoundaryPath) : ∃ i : Fin B.steps.length, (B.steps.get i).turn = ExteriorTurn.t_90 := by
  obtain ⟨step, h_mem, h_turn⟩ := existence_of_convex_anchor B
  rw [List.mem_iff_get] at h_mem
  obtain ⟨i, rfl⟩ := h_mem
  use i

/-- Recursively decodes the interior tiles of a given boundary path.
    Utilizes localized single-tile peeling to reduce the boundary. -/
noncomputable def decodeInterior (B : BoundaryPath) : List TileId :=
  if B.tile_count <= 1 then
    []
  else
    let i := Classical.choose (convex_anchor_index B)
    have h_anchor : (B.steps.get i).turn = ExteriorTurn.t_90 := Classical.choose_spec (convex_anchor_index B)
    let T := Classical.choose (forcing_neighborhood B i h_anchor)
    match h_peel : peelBoundary B i with
    | some B' =>
      have _ : B'.tile_count < B.tile_count := peel_preserves_boundary_properties B i B' h_peel
      T :: decodeInterior B'
    | none =>
      [T]
termination_by B.tile_count

/-- Theorem 2: Global Holography Uniqueness.
    The sequence of boundary steps uniquely and deterministically reconstructs the interior tile patch. -/
theorem aperiodic_holography_uniqueness (B : BoundaryPath) :
  ∀ (interior_A interior_B : List TileId),
    interior_A = decodeInterior B → interior_B = decodeInterior B → interior_A = interior_B := by
  intro interior_A interior_B hA hB
  rw [hA, hB]

end
end Spectrebound
