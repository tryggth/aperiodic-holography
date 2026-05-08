import Mathlib.Logic.Equiv.Basic
import Spectrebound.SpectrePatch

namespace Spectrebound

def peel (p : Patch) : Patch :=
  let ring := outerRing p
  let newTiles := p.tiles.filter (fun id => !(ring.contains id))
  let newAdj (e : TileEdge) : Option TileEdge :=
    if newTiles.contains e.1 then
      match p.adj e with
      | some e' => if newTiles.contains e'.1 then some e' else none
      | none => none
    else none
  ⟨newTiles, newAdj⟩

def PatchEquiv (p1 p2 : Patch) : Prop :=
  ∃ f : {x // x ∈ p1.tiles} ≃ {x // x ∈ p2.tiles},
    ∀ (t1 t1' : {x // x ∈ p1.tiles}) (e e' : Fin 14),
      p1.adj (t1.val, e) = some (t1'.val, e') ↔ p2.adj ((f t1).val, e) = some ((f t1').val, e')

def OuterRingEquiv (p1 p2 : Patch) : Prop :=
  ∃ f : {x // x ∈ outerRing p1} ≃ {x // x ∈ outerRing p2},
    ∀ (t1 t1' : {x // x ∈ outerRing p1}) (e e' : Fin 14),
      p1.adj (t1.val, e) = some (t1'.val, e') ↔ p2.adj ((f t1).val, e) = some ((f t1').val, e')

lemma outer_ring_determinism (p1 p2 : Patch) (e1 e2 : TileEdge) 
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) : OuterRingEquiv p1 p2 := by
  sorry

def IsPlanarPatch (p : Patch) : Prop := p.tiles ≠ [] → outerRing p ≠ []

lemma filter_length_lt {α} [DecidableEq α] (l : List α) (ring : List α) 
    (h1 : ring ≠ []) (h2 : ∀ x ∈ ring, x ∈ l) :
    (l.filter (fun id => !(ring.contains id))).length < l.length := by
  sorry

lemma peel_length_lt (p : Patch) (h_planar : IsPlanarPatch p) (h : p.tiles ≠ []) : (peel p).tiles.length < p.tiles.length := by
  dsimp [peel]
  have hr : outerRing p ≠ [] := h_planar h
  have hs : ∀ x ∈ outerRing p, x ∈ p.tiles := by
    intro x hx
    unfold outerRing at hx
    have h1 := List.mem_eraseDups.mp hx
    have ⟨e, he1, he2⟩ := List.mem_map.mp h1
    unfold patchBoundary at he1
    have h2 := List.mem_filter.mp he1
    have h3 := h2.1
    have ⟨id, hid1, hid2⟩ := List.mem_flatMap.mp h3
    have h4 := List.mem_map.mp hid2
    rcases h4 with ⟨e', _, he'⟩
    have h_fst : e.fst = id := by rw [← he']
    rw [h_fst] at he2
    rw [← he2]
    exact hid1
  exact filter_length_lt p.tiles (outerRing p) hr hs

lemma empty_patch_of_empty_bound (p1 p2 : Patch) (e1 e2 : TileEdge)
    (h_empty : p1.tiles = []) (h_planar2 : IsPlanarPatch p2)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) : p2.tiles = [] := by
  sorry

lemma patch_glue (p1 p2 : Patch) (h_out : OuterRingEquiv p1 p2) (h_in : PatchEquiv (peel p1) (peel p2)) : PatchEquiv p1 p2 := by
  sorry

lemma peel_is_planar (p : Patch) : IsPlanarPatch (peel p) := by sorry
lemma get_inner_e1 (p : Patch) (e : TileEdge) : TileEdge := sorry
lemma inner_boundary_eq (p1 p2 : Patch) (e1 e2 : TileEdge) (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) : 
    boundaryWord (peel p1) (get_inner_e1 p1 e1) = boundaryWord (peel p2) (get_inner_e1 p2 e2) := by sorry

theorem aperiodic_holography (p1 p2 : Patch) (e1 e2 : TileEdge) 
    (h_planar1 : IsPlanarPatch p1) (h_planar2 : IsPlanarPatch p2)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) : PatchEquiv p1 p2 := by
  let n := p1.tiles.length
  have hn : p1.tiles.length = n := rfl
  induction n using Nat.strong_induction_on generalizing p1 p2 e1 e2 with
  | h n ih =>
    by_cases h_empty : p1.tiles = []
    · have hp2_empty : p2.tiles = [] := empty_patch_of_empty_bound p1 p2 e1 e2 h_empty h_planar2 h_bound
      have h1 : IsEmpty {x // x ∈ p1.tiles} := ⟨fun x => by 
        have h := x.property; rw [h_empty] at h; exact List.not_mem_nil _ h⟩
      have h2 : IsEmpty {x // x ∈ p2.tiles} := ⟨fun x => by 
        have h := x.property; rw [hp2_empty] at h; exact List.not_mem_nil _ h⟩
      have hf : {x // x ∈ p1.tiles} ≃ {x // x ∈ p2.tiles} := Equiv.equivOfIsEmpty _ _
      exact ⟨hf, fun t1 _ _ _ => IsEmpty.elim h1 t1⟩
    · have h_lt : (peel p1).tiles.length < n := by
        rw [← hn]
        exact peel_length_lt p1 h_planar1 h_empty
      have h_outer := outer_ring_determinism p1 p2 e1 e2 h_bound
      have h_planar_peel1 := peel_is_planar p1
      have h_planar_peel2 := peel_is_planar p2
      let inner_e1 := get_inner_e1 p1 e1
      let inner_e2 := get_inner_e1 p2 e2
      have h_inner_bound := inner_boundary_eq p1 p2 e1 e2 h_bound
      have h_in := ih ((peel p1).tiles.length) h_lt (peel p1) (peel p2) inner_e1 inner_e2 h_planar_peel1 h_planar_peel2 h_inner_bound rfl
      exact patch_glue p1 p2 h_outer h_in

end Spectrebound
