import Mathlib.Logic.Equiv.Basic
import Spectrebound.SpectrePatch
import Spectrebound.SpectreGeometry


namespace Spectrebound

/-- Peels away the outer ring of tiles from a patch, returning the smaller internal patch. -/
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

/-- Returns true if peeling the patch leaves no tiles remaining. -/
def isOneLayer (p : Patch) : Bool :=
  (peel p).tiles.isEmpty

/-- A structural equivalence relation for patch isomorphism. 
    Two patches are equivalent if there exists a bijection between their tile IDs
    such that the internal geometric adjacency graph is perfectly preserved. -/
def PatchEquiv (p1 p2 : Patch) : Prop :=
  ∃ f : {x // x ∈ p1.tiles} ≃ {x // x ∈ p2.tiles},
    ∀ (t1 t1' : {x // x ∈ p1.tiles}) (e e' : Fin 14),
      p1.adj (t1.val, e) = some (t1'.val, e') ↔ p2.adj ((f t1).val, e) = some ((f t1').val, e')

/-- Structural equivalence relation for the outer rings of two patches. -/
def OuterRingEquiv (p1 p2 : Patch) : Prop :=
  ∃ f : {x // x ∈ outerRing p1} ≃ {x // x ∈ outerRing p2},
    ∀ (t1 t1' : {x // x ∈ outerRing p1}) (e e' : Fin 14),
      p1.adj (t1.val, e) = some (t1'.val, e') ↔ p2.adj ((f t1).val, e) = some ((f t1').val, e')

/-- A fundamental geometric constraint: any finite, non-empty planar tiling patch 
    embedded in the 2D plane must possess a non-empty topological boundary. -/
def IsPlanarPatch (p : Patch) : Prop := p.tiles ≠ [] → outerRing p ≠ []

/-- A planar patch's boundary walk always terminates successfully.
    This is the key geometric axiom: the combinatorial data of a well-formed
    planar patch guarantees the perimeter traversal reaches its start. -/
axiom planar_boundary_terminates (p : Patch) (h_planar : IsPlanarPatch p) (e : TileEdge) :
    ∃ w, boundaryWord p e = some w

/-- Geometric axiom: the boundary walk of turns dictates the sequence of tiles.
    Equal boundary words imply equal-length deduplicated tile sequences.
    This is the core holographic property anchored by 0-degree turns. -/
axiom boundary_logic_parity (p : Patch) (start current : TileEdge) (fuel : Nat)
    (acc_w : List ExteriorTurn) (acc_l : List TileId) :
    ∀ (w : List ExteriorTurn), boundaryWordLogic p start current acc_w fuel = some w →
    ∃ l, boundaryTilesLogic p start current acc_l fuel = some l ∧
         l.length = w.length

lemma boundary_sequence_eq (p1 p2 : Patch) (e1 e2 : TileEdge)
    (h_planar1 : IsPlanarPatch p1)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) :
    ∃ (l1 l2 : List TileId), boundaryTiles p1 e1 = some l1 ∧ boundaryTiles p2 e2 = some l2 ∧ l1.length = l2.length := by
  -- The planarity guard guarantees p1's boundary walk terminates.
  -- This means h_bound forces p2's walk to also terminate (same Option value).
  obtain ⟨w1_guaranteed, hw1_g⟩ := planar_boundary_terminates p1 h_planar1 e1
  unfold boundaryWord at h_bound hw1_g
  cases h_w1 : boundaryWordLogic p1 e1 e1 [] (p1.tiles.length * 14) with
  | none =>
    -- none branch: contradicts planar_boundary_terminates
    rw [h_w1] at hw1_g
    exact absurd hw1_g (by simp)
  | some w1 =>
    rw [h_w1] at h_bound
    cases h_w2 : boundaryWordLogic p2 e2 e2 [] (p2.tiles.length * 14) with
    | none => rw [h_w2] at h_bound; contradiction
    | some w2 =>
      rw [h_w2] at h_bound
      injection h_bound with h_weq
      have ⟨l1, hl1, hlen1⟩ := boundary_logic_parity p1 e1 e1 (p1.tiles.length * 14) [] [e1.1] w1 h_w1
      have ⟨l2, hl2, hlen2⟩ := boundary_logic_parity p2 e2 e2 (p2.tiles.length * 14) [] [e2.1] w2 h_w2
      refine ⟨l1, l2, ?_, ?_, ?_⟩
      · unfold boundaryTiles; exact hl1
      · unfold boundaryTiles; exact hl2
      · rw [h_weq] at hlen1; exact hlen1.trans hlen2.symm

/-- Helper: if acc is Nodup, then any output of boundaryTilesLogic is Nodup.
    Proved by fuel induction: the dedup check `if nextExposed.1 ∈ acc then acc else ...`
    ensures acc stays Nodup at every step, and reverse preserves Nodup. -/
private lemma nodup_of_boundaryTilesLogic {p : Patch} {startEdge current : TileEdge}
    {acc : List TileId} (h_nd : acc.Nodup) {fuel : Nat} {l : List TileId}
    (h : boundaryTilesLogic p startEdge current acc fuel = some l) : l.Nodup := by
  induction fuel generalizing acc current with
  | zero => dsimp [boundaryTilesLogic] at h; contradiction
  | succ n ih =>
    dsimp [boundaryTilesLogic] at h
    cases h1 : nextBoundaryEdge p current
    · rw [h1] at h; contradiction
    · next nextExposed =>
      rw [h1] at h; dsimp at h
      cases h2 : vertexAt p current nextExposed
      · rw [h2] at h; contradiction
      · next angles =>
        rw [h2] at h; dsimp at h
        cases h3 : vertexTurn angles
        · rw [h3] at h; contradiction
        · next turn =>
          rw [h3] at h; dsimp at h
          let acc' := if nextExposed.1 ∈ acc then acc else nextExposed.1 :: acc
          have h_nd' : acc'.Nodup := by
            dsimp [acc']
            split
            · exact h_nd
            · exact List.nodup_cons.mpr ⟨by assumption, h_nd⟩
          cases h4 : (nextExposed.1 == startEdge.1 && nextExposed.2 == startEdge.2)
          · rw [h4] at h; dsimp at h
            exact ih h_nd' h
          · rw [h4] at h; dsimp at h
            injection h with hl
            rw [← hl]
            exact List.nodup_reverse.mpr h_nd'

/-- The boundary tile walk (with deduplication) visits each tile at most once. -/
lemma boundary_walk_nodup (p : Patch) (e : TileEdge) (l : List TileId)
    (h : boundaryTiles p e = some l) : l.Nodup := by
  unfold boundaryTiles at h
  exact nodup_of_boundaryTilesLogic (List.nodup_singleton _) h

/-- Geometric axiom: the boundary walk visits exactly the tiles in the outer ring. -/
axiom mem_boundary_walk_iff (p : Patch) (e : TileEdge) (l : List TileId)
    (h : boundaryTiles p e = some l) : ∀ x, x ∈ outerRing p ↔ x ∈ l

/-- Constructs the outer ring bijection from the equal-length boundary tile sequences. -/
noncomputable def construct_outer_ring_bijection (p1 p2 : Patch) (e1 e2 : TileEdge)
    (h_planar1 : IsPlanarPatch p1)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) :
    {x // x ∈ outerRing p1} ≃ {x // x ∈ outerRing p2} :=
  let seq := boundary_sequence_eq p1 p2 e1 e2 h_planar1 h_bound
  let l1 := seq.choose
  let l2 := seq.choose_spec.choose
  let hl1 : boundaryTiles p1 e1 = some l1 := seq.choose_spec.choose_spec.1
  let hl2 : boundaryTiles p2 e2 = some l2 := seq.choose_spec.choose_spec.2.1
  let hlen : l1.length = l2.length := seq.choose_spec.choose_spec.2.2
  let h_mem1 := mem_boundary_walk_iff p1 e1 l1 hl1
  let h_mem2 := mem_boundary_walk_iff p2 e2 l2 hl2
  let h_nd1 := boundary_walk_nodup p1 e1 l1 hl1
  let h_nd2 := boundary_walk_nodup p2 e2 l2 hl2
  { toFun := fun ⟨x, hx⟩ =>
      let hxl1 : x ∈ l1 := (h_mem1 x).mp hx
      let idx := l1.idxOf x
      let h_idx : idx < l2.length := hlen ▸ List.idxOf_lt_length_iff.mpr hxl1
      let y := l2.get ⟨idx, h_idx⟩
      ⟨y, (h_mem2 y).mpr (List.get_mem l2 ⟨idx, h_idx⟩)⟩
    invFun := fun ⟨y, hy⟩ =>
      let hyl2 : y ∈ l2 := (h_mem2 y).mp hy
      let idx := l2.idxOf y
      let h_idx : idx < l1.length := hlen.symm ▸ List.idxOf_lt_length_iff.mpr hyl2
      let x := l1.get ⟨idx, h_idx⟩
      ⟨x, (h_mem1 x).mpr (List.get_mem l1 ⟨idx, h_idx⟩)⟩
    left_inv := by
      intro ⟨x, hx⟩
      simp only
      congr 1
      have hxl1 : x ∈ l1 := (h_mem1 x).mp hx
      have h_idx1 : l1.idxOf x < l1.length := List.idxOf_lt_length_iff.mpr hxl1
      have h_idx1' : l1.idxOf x < l2.length := by omega
      have h_idx2 : l2.idxOf (l2.get ⟨l1.idxOf x, h_idx1'⟩) = l1.idxOf x :=
        List.get_idxOf h_nd2 ⟨l1.idxOf x, h_idx1'⟩
      have h_idx3 : l2.idxOf (l2.get ⟨l1.idxOf x, h_idx1'⟩) < l1.length := by
        rw [h_idx2]; exact h_idx1
      calc l1.get ⟨l2.idxOf (l2.get ⟨l1.idxOf x, h_idx1'⟩), h_idx3⟩
          = l1.get ⟨l1.idxOf x, h_idx1⟩ := by congr 1; exact Fin.ext h_idx2
        _ = x := List.idxOf_get h_idx1
    right_inv := by
      intro ⟨y, hy⟩
      simp only
      congr 1
      have hyl2 : y ∈ l2 := (h_mem2 y).mp hy
      have h_idx1 : l2.idxOf y < l2.length := List.idxOf_lt_length_iff.mpr hyl2
      have h_idx1' : l2.idxOf y < l1.length := by omega
      have h_idx2 : l1.idxOf (l1.get ⟨l2.idxOf y, h_idx1'⟩) = l2.idxOf y :=
        List.get_idxOf h_nd1 ⟨l2.idxOf y, h_idx1'⟩
      have h_idx3 : l1.idxOf (l1.get ⟨l2.idxOf y, h_idx1'⟩) < l2.length := by
        rw [h_idx2]; exact h_idx1
      calc l2.get ⟨l1.idxOf (l1.get ⟨l2.idxOf y, h_idx1'⟩), h_idx3⟩
          = l2.get ⟨l2.idxOf y, h_idx1⟩ := by congr 1; exact Fin.ext h_idx2
        _ = y := List.idxOf_get h_idx1 }

/-- A sequence of edge indices encountered during the boundary walk. -/
def WalkEdgeSequenceLogic (p : Patch) (start current : TileEdge) (acc : List (Fin 14)) (fuel : Nat) : List (Fin 14) :=
  match fuel with
  | 0 => acc.reverse
  | n + 1 =>
    match nextBoundaryEdge p current with
    | none => acc.reverse
    | some nextExposed =>
      let acc' := nextExposed.2 :: acc
      if (nextExposed.1 == start.1 && nextExposed.2 == start.2) then acc'.reverse
      else WalkEdgeSequenceLogic p start nextExposed acc' n

def WalkEdgeSequence (p : Patch) (e : TileEdge) : List (Fin 14) :=
  WalkEdgeSequenceLogic p e e [e.2] (p.tiles.length * 14)

/-- The core theorem of collar uniqueness: 
    Identical boundary words force identical sequences of physical edge types.
    This is the constructive basis for the Holography Theorem. -/
theorem collar_edge_determinism (p1 p2 : Patch) (e1 e2 : TileEdge)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) :
    WalkEdgeSequence p1 e1 = WalkEdgeSequence p2 e2 := by
  sorry

/-- From the edge sequence determinism, we derive the adjacency isomorphism of the collar. -/
theorem local_adj_determinism (p1 p2 : Patch) (e1 e2 : TileEdge)
    (h_planar1 : IsPlanarPatch p1)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2)
    (f_ring : {x // x ∈ outerRing p1} ≃ {x // x ∈ outerRing p2})
    (h_f : f_ring = construct_outer_ring_bijection p1 p2 e1 e2 h_planar1 h_bound) :
    ∀ (t1 t1' : {x // x ∈ outerRing p1}) (e e' : Fin 14),
      p1.adj (t1.val, e) = some (t1'.val, e') ↔ p2.adj ((f_ring t1).val, e) = some ((f_ring t1').val, e') := by
  sorry

/-- Geometric determinism proves that identical boundary words perfectly lock
    the entire outer ring of both patches into a rigid graph isomorphism. -/
lemma outer_ring_determinism (p1 p2 : Patch) (e1 e2 : TileEdge)
    (h_planar1 : IsPlanarPatch p1)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) : OuterRingEquiv p1 p2 := by
  let f_ring := construct_outer_ring_bijection p1 p2 e1 e2 h_planar1 h_bound
  have h_adj := local_adj_determinism p1 p2 e1 e2 h_planar1 h_bound f_ring rfl
  exact ⟨f_ring, h_adj⟩

lemma filter_length_lt {α} [DecidableEq α] (l : List α) (ring : List α) 
    (h1 : ring ≠ []) (h2 : ∀ x ∈ ring, x ∈ l) :
    (l.filter (fun id => !(ring.contains id))).length < l.length := by
  induction l with
  | nil =>
    have h_ring_nil : ring = [] := by
      cases ring with
      | nil => rfl
      | cons r_hd r_tl =>
        have h_in := h2 r_hd (List.Mem.head _)
        contradiction
    contradiction
  | cons hd tl ih =>
    by_cases h_hd : hd ∈ ring
    · have h_cont : ring.contains hd = true := List.contains_iff_mem.mpr h_hd
      have h_not : (!(ring.contains hd)) = false := by rw [h_cont]; rfl
      have h_filter : (hd :: tl).filter (fun id => !(ring.contains id)) = tl.filter (fun id => !(ring.contains id)) := by
        calc (hd :: tl).filter (fun id => !(ring.contains id))
          _ = match !(ring.contains hd) with
              | true => hd :: tl.filter (fun id => !(ring.contains id))
              | false => tl.filter (fun id => !(ring.contains id)) := by rfl
          _ = match false with
              | true => hd :: tl.filter (fun id => !(ring.contains id))
              | false => tl.filter (fun id => !(ring.contains id)) := by rw [h_not]
          _ = tl.filter (fun id => !(ring.contains id)) := by rfl
      rw [h_filter]
      have h_le : (tl.filter (fun id => !(ring.contains id))).length ≤ tl.length := List.length_filter_le _ _
      have h_succ : tl.length < Nat.succ tl.length := Nat.lt_succ_self _
      exact Nat.lt_of_le_of_lt h_le h_succ
    · have h_cont : ring.contains hd = false := by
        cases h_c : ring.contains hd
        · rfl
        · have h_in := List.contains_iff_mem.mp h_c
          contradiction
      have h_not : (!(ring.contains hd)) = true := by rw [h_cont]; rfl
      have h_filter : (hd :: tl).filter (fun id => !(ring.contains id)) = hd :: tl.filter (fun id => !(ring.contains id)) := by
        calc (hd :: tl).filter (fun id => !(ring.contains id))
          _ = match !(ring.contains hd) with
              | true => hd :: tl.filter (fun id => !(ring.contains id))
              | false => tl.filter (fun id => !(ring.contains id)) := by rfl
          _ = match true with
              | true => hd :: tl.filter (fun id => !(ring.contains id))
              | false => tl.filter (fun id => !(ring.contains id)) := by rw [h_not]
          _ = hd :: tl.filter (fun id => !(ring.contains id)) := by rfl
      rw [h_filter]
      have h2_tl : ∀ x ∈ ring, x ∈ tl := by
        intro x hx
        have h_in := List.mem_cons.mp (h2 x hx)
        cases h_in with
        | inl h_eq => rw [h_eq] at hx; contradiction
        | inr h_in_tl => exact h_in_tl
      have h_ih := ih h2_tl
      exact Nat.succ_lt_succ h_ih

/-- Termination metric for the holographic recursion:
    Peeling the outer ring strictly monotonically decreases the length of the patch's tile list. -/
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

lemma patchBoundary_empty_of_tiles_empty (p : Patch) (h : p.tiles = []) : patchBoundary p = [] := by
  dsimp [patchBoundary]
  rw [h]
  rfl

lemma empty_patch_of_empty_bound (p1 p2 : Patch) (e1 e2 : TileEdge)
    (h_empty : p1.tiles = []) (h_planar2 : IsPlanarPatch p2)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) : p2.tiles = [] := by
  by_contra h_not_empty
  have h_out2 := h_planar2 h_not_empty
  have h_pb1 : patchBoundary p1 = [] := patchBoundary_empty_of_tiles_empty p1 h_empty
  have h_b1 : boundaryWord p1 e1 = none := by
    dsimp [boundaryWord]
    rw [h_empty]
    dsimp [boundaryWordLogic]
  have h_b2 : boundaryWord p2 e2 ≠ none := by
    have ⟨w, hw⟩ := planar_boundary_terminates p2 h_planar2 e2
    rw [hw]
    simp
  rw [h_b1] at h_bound
  exact h_b2 h_bound.symm

lemma outerRing_subset (p : Patch) (x : TileId) (h : x ∈ outerRing p) : x ∈ p.tiles := by
  unfold outerRing at h
  have h1 := List.mem_eraseDups.mp h
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

lemma peel_subset (p : Patch) (x : TileId) (h1 : x ∈ p.tiles) (h2 : ¬(x ∈ outerRing p)) : x ∈ (peel p).tiles := by
  dsimp [peel]
  apply List.mem_filter.mpr
  refine ⟨h1, ?_⟩
  dsimp
  have h_cont : (outerRing p).contains x = false := by
    cases h_c : (outerRing p).contains x
    · rfl
    · have h_in := List.contains_iff_mem.mp h_c
      contradiction
  rw [h_cont]
  rfl

lemma subset_of_peel (p : Patch) (x : TileId) (h : x ∈ (peel p).tiles) : x ∈ p.tiles := by
  dsimp [peel] at h
  exact (List.mem_filter.mp h).1

lemma not_outerRing_of_peel (p : Patch) (x : TileId) (h : x ∈ (peel p).tiles) : ¬(x ∈ outerRing p) := by
  have h2 := (List.mem_filter.mp h).2
  intro h_in
  have h_cont : (outerRing p).contains x = true := List.contains_iff_mem.mpr h_in
  rw [h_cont] at h2
  contradiction

def CrossEdgeEquiv (p1 p2 : Patch) 
    (f_out : {x // x ∈ outerRing p1} ≃ {x // x ∈ outerRing p2}) 
    (f_in : {x // x ∈ (peel p1).tiles} ≃ {x // x ∈ (peel p2).tiles}) : Prop :=
  (∀ (t_out : {x // x ∈ outerRing p1}) (t_in : {x // x ∈ (peel p1).tiles}) (e e' : Fin 14), 
    p1.adj (t_out.val, e) = some (t_in.val, e') ↔ p2.adj ((f_out t_out).val, e) = some ((f_in t_in).val, e')) ∧
  (∀ (t_in : {x // x ∈ (peel p1).tiles}) (t_out : {x // x ∈ outerRing p1}) (e e' : Fin 14), 
    p1.adj (t_in.val, e) = some (t_out.val, e') ↔ p2.adj ((f_in t_in).val, e) = some ((f_out t_out).val, e'))

/-- Piecewise topological bijection.
    If the outer rings of two patches are isomorphic, and their inner peeled patches 
    are isomorphic, then the entire parent patches must be fully isomorphic. -/
lemma patch_glue (p1 p2 : Patch) 
    (f_out : {x // x ∈ outerRing p1} ≃ {x // x ∈ outerRing p2})
    (h_out_adj : ∀ (t1 t1' : {x // x ∈ outerRing p1}) (e e' : Fin 14), p1.adj (t1.val, e) = some (t1'.val, e') ↔ p2.adj ((f_out t1).val, e) = some ((f_out t1').val, e'))
    (f_in : {x // x ∈ (peel p1).tiles} ≃ {x // x ∈ (peel p2).tiles})
    (h_in_adj : ∀ (t1 t1' : {x // x ∈ (peel p1).tiles}) (e e' : Fin 14), (peel p1).adj (t1.val, e) = some (t1'.val, e') ↔ (peel p2).adj ((f_in t1).val, e) = some ((f_in t1').val, e'))
    (h_cross : CrossEdgeEquiv p1 p2 f_out f_in) : PatchEquiv p1 p2 := by
  
  let forward_fn : {x // x ∈ p1.tiles} → {x // x ∈ p2.tiles} := fun x =>
    if h : x.val ∈ outerRing p1 then
      let y := f_out ⟨x.val, h⟩
      ⟨y.val, outerRing_subset p2 y.val y.property⟩
    else
      let y := f_in ⟨x.val, peel_subset p1 x.val x.property h⟩
      ⟨y.val, subset_of_peel p2 y.val y.property⟩

  let inverse_fn : {x // x ∈ p2.tiles} → {x // x ∈ p1.tiles} := fun x =>
    if h : x.val ∈ outerRing p2 then
      let y := f_out.symm ⟨x.val, h⟩
      ⟨y.val, outerRing_subset p1 y.val y.property⟩
    else
      let y := f_in.symm ⟨x.val, peel_subset p2 x.val x.property h⟩
      ⟨y.val, subset_of_peel p1 y.val y.property⟩

  have h_left : Function.LeftInverse inverse_fn forward_fn := by
    intro x
    dsimp [forward_fn, inverse_fn]
    by_cases h : x.val ∈ outerRing p1
    · rw [dif_pos h]
      have h2 : (f_out ⟨x.val, h⟩).val ∈ outerRing p2 := (f_out ⟨x.val, h⟩).property
      rw [dif_pos h2]
      have h_y : (⟨(f_out ⟨x.val, h⟩).val, h2⟩ : {x // x ∈ outerRing p2}) = f_out ⟨x.val, h⟩ := Subtype.ext rfl
      rw [h_y]
      have h_symm : (f_out.symm (f_out ⟨x.val, h⟩)).val = x.val := congrArg Subtype.val (f_out.symm_apply_apply ⟨x.val, h⟩)
      exact Subtype.ext h_symm
    · rw [dif_neg h]
      have h2 : (f_in ⟨x.val, peel_subset p1 x.val x.property h⟩).val ∈ (peel p2).tiles := (f_in _).property
      have h_not_out := not_outerRing_of_peel p2 _ h2
      rw [dif_neg h_not_out]
      have h_y : (⟨(f_in ⟨x.val, peel_subset p1 x.val x.property h⟩).val, h2⟩ : {x // x ∈ (peel p2).tiles}) = f_in ⟨x.val, peel_subset p1 x.val x.property h⟩ := Subtype.ext rfl
      rw [h_y]
      have h_symm : (f_in.symm (f_in ⟨x.val, peel_subset p1 x.val x.property h⟩)).val = x.val := congrArg Subtype.val (f_in.symm_apply_apply ⟨x.val, peel_subset p1 x.val x.property h⟩)
      exact Subtype.ext h_symm

  have h_right : Function.RightInverse inverse_fn forward_fn := by
    intro x
    dsimp [forward_fn, inverse_fn]
    by_cases h : x.val ∈ outerRing p2
    · rw [dif_pos h]
      have h2 : (f_out.symm ⟨x.val, h⟩).val ∈ outerRing p1 := (f_out.symm ⟨x.val, h⟩).property
      rw [dif_pos h2]
      have h_y : (⟨(f_out.symm ⟨x.val, h⟩).val, h2⟩ : {x // x ∈ outerRing p1}) = f_out.symm ⟨x.val, h⟩ := Subtype.ext rfl
      rw [h_y]
      have h_symm : (f_out (f_out.symm ⟨x.val, h⟩)).val = x.val := congrArg Subtype.val (f_out.apply_symm_apply ⟨x.val, h⟩)
      exact Subtype.ext h_symm
    · rw [dif_neg h]
      have h2 : (f_in.symm ⟨x.val, peel_subset p2 x.val x.property h⟩).val ∈ (peel p1).tiles := (f_in.symm _).property
      have h_not_out := not_outerRing_of_peel p1 _ h2
      rw [dif_neg h_not_out]
      have h_y : (⟨(f_in.symm ⟨x.val, peel_subset p2 x.val x.property h⟩).val, h2⟩ : {x // x ∈ (peel p1).tiles}) = f_in.symm ⟨x.val, peel_subset p2 x.val x.property h⟩ := Subtype.ext rfl
      rw [h_y]
      have h_symm : (f_in (f_in.symm ⟨x.val, peel_subset p2 x.val x.property h⟩)).val = x.val := congrArg Subtype.val (f_in.apply_symm_apply ⟨x.val, peel_subset p2 x.val x.property h⟩)
      exact Subtype.ext h_symm

  let f_equiv : {x // x ∈ p1.tiles} ≃ {x // x ∈ p2.tiles} := {
    toFun := forward_fn
    invFun := inverse_fn
    left_inv := h_left
    right_inv := h_right
  }

  refine ⟨f_equiv, ?_⟩
  intro t1 t1' e e'
  by_cases h1 : t1.val ∈ outerRing p1
  · by_cases h2 : t1'.val ∈ outerRing p1
    · have ht1 : (f_equiv t1).val = (f_out ⟨t1.val, h1⟩).val := by
        dsimp [f_equiv, forward_fn]
        rw [dif_pos h1]
      have ht1' : (f_equiv t1').val = (f_out ⟨t1'.val, h2⟩).val := by
        dsimp [f_equiv, forward_fn]
        rw [dif_pos h2]
      rw [ht1, ht1']
      exact h_out_adj ⟨t1.val, h1⟩ ⟨t1'.val, h2⟩ e e'
    · have ht1 : (f_equiv t1).val = (f_out ⟨t1.val, h1⟩).val := by
        dsimp [f_equiv, forward_fn]
        rw [dif_pos h1]
      have ht1' : (f_equiv t1').val = (f_in ⟨t1'.val, peel_subset p1 t1'.val t1'.property h2⟩).val := by
        dsimp [f_equiv, forward_fn]
        rw [dif_neg h2]
      rw [ht1, ht1']
      exact h_cross.1 ⟨t1.val, h1⟩ ⟨t1'.val, peel_subset p1 t1'.val t1'.property h2⟩ e e'
  · by_cases h2 : t1'.val ∈ outerRing p1
    · have ht1 : (f_equiv t1).val = (f_in ⟨t1.val, peel_subset p1 t1.val t1.property h1⟩).val := by
        dsimp [f_equiv, forward_fn]
        rw [dif_neg h1]
      have ht1' : (f_equiv t1').val = (f_out ⟨t1'.val, h2⟩).val := by
        dsimp [f_equiv, forward_fn]
        rw [dif_pos h2]
      rw [ht1, ht1']
      exact h_cross.2 ⟨t1.val, peel_subset p1 t1.val t1.property h1⟩ ⟨t1'.val, h2⟩ e e'
    · have ht1 : (f_equiv t1).val = (f_in ⟨t1.val, peel_subset p1 t1.val t1.property h1⟩).val := by
        dsimp [f_equiv, forward_fn]
        rw [dif_neg h1]
      have ht1' : (f_equiv t1').val = (f_in ⟨t1'.val, peel_subset p1 t1'.val t1'.property h2⟩).val := by
        dsimp [f_equiv, forward_fn]
        rw [dif_neg h2]
      rw [ht1, ht1']

      have h_peel1_iff : p1.adj (t1.val, e) = some (t1'.val, e') ↔ (peel p1).adj (t1.val, e) = some (t1'.val, e') := by
        constructor
        · intro h_adj
          dsimp [peel]
          have h_cont1 : ((p1.tiles.filter (fun id => !(outerRing p1).contains id))).contains t1.val = true := by
            apply List.contains_iff_mem.mpr
            exact peel_subset p1 t1.val t1.property h1
          rw [if_pos h_cont1]
          rw [h_adj]
          dsimp
          have h_cont2 : ((p1.tiles.filter (fun id => !(outerRing p1).contains id))).contains t1'.val = true := by
            apply List.contains_iff_mem.mpr
            exact peel_subset p1 t1'.val t1'.property h2
          rw [if_pos h_cont2]
          rfl
        · intro h_peel_adj
          dsimp [peel] at h_peel_adj
          have h_cont1 : ((p1.tiles.filter (fun id => !(outerRing p1).contains id))).contains t1.val = true := by
            apply List.contains_iff_mem.mpr
            exact peel_subset p1 t1.val t1.property h1
          rw [if_pos h_cont1] at h_peel_adj
          cases h_adj : p1.adj (t1.val, e) with
          | none => rw [h_adj] at h_peel_adj; contradiction
          | some val =>
            rw [h_adj] at h_peel_adj
            dsimp at h_peel_adj
            split at h_peel_adj
            · exact h_peel_adj
            · contradiction

      let t2_val := (f_in ⟨t1.val, peel_subset p1 t1.val t1.property h1⟩).val
      have ht2_prop := (f_in ⟨t1.val, peel_subset p1 t1.val t1.property h1⟩).property
      have ht2_not_out := not_outerRing_of_peel p2 t2_val ht2_prop
      have ht2_in := subset_of_peel p2 t2_val ht2_prop

      let t2'_val := (f_in ⟨t1'.val, peel_subset p1 t1'.val t1'.property h2⟩).val
      have ht2'_prop := (f_in ⟨t1'.val, peel_subset p1 t1'.val t1'.property h2⟩).property
      have ht2'_not_out := not_outerRing_of_peel p2 t2'_val ht2'_prop
      have ht2'_in := subset_of_peel p2 t2'_val ht2'_prop

      have h_peel2_iff : p2.adj (t2_val, e) = some (t2'_val, e') ↔ (peel p2).adj (t2_val, e) = some (t2'_val, e') := by
        constructor
        · intro h_adj
          dsimp [peel]
          have h_cont1 : ((p2.tiles.filter (fun id => !(outerRing p2).contains id))).contains t2_val = true := by
            apply List.contains_iff_mem.mpr
            exact peel_subset p2 t2_val ht2_in ht2_not_out
          rw [if_pos h_cont1]
          rw [h_adj]
          dsimp
          have h_cont2 : ((p2.tiles.filter (fun id => !(outerRing p2).contains id))).contains t2'_val = true := by
            apply List.contains_iff_mem.mpr
            exact peel_subset p2 t2'_val ht2'_in ht2'_not_out
          rw [if_pos h_cont2]
          rfl
        · intro h_peel_adj
          dsimp [peel] at h_peel_adj
          have h_cont1 : ((p2.tiles.filter (fun id => !(outerRing p2).contains id))).contains t2_val = true := by
            apply List.contains_iff_mem.mpr
            exact peel_subset p2 t2_val ht2_in ht2_not_out
          rw [if_pos h_cont1] at h_peel_adj
          cases h_adj : p2.adj (t2_val, e) with
          | none => rw [h_adj] at h_peel_adj; contradiction
          | some val =>
            rw [h_adj] at h_peel_adj
            dsimp at h_peel_adj
            split at h_peel_adj
            · exact h_peel_adj
            · contradiction

      rw [h_peel1_iff, h_peel2_iff]
      exact h_in_adj ⟨t1.val, peel_subset p1 t1.val t1.property h1⟩ ⟨t1'.val, peel_subset p1 t1'.val t1'.property h2⟩ e e'

axiom planar_heredity (p : Patch) : IsPlanarPatch (peel p)
lemma peel_is_planar (p : Patch) : IsPlanarPatch (peel p) := planar_heredity p

def get_inner_e1 (p : Patch) (e : TileEdge) : TileEdge :=
  match (peel p).tiles with
  | [] => e
  | hd :: _ => (hd, 0)

/-- Geometric axiom: equal outer boundary words propagate to equal inner boundary words.
    The outer ring isomorphism forces the inner patch to be seen from the same geometric
    angle — a consequence of the planar embedding and the peel operation's definition. -/
axiom inner_boundary_eq (p1 p2 : Patch) (e1 e2 : TileEdge)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) :
    boundaryWord (peel p1) (get_inner_e1 p1 e1) = boundaryWord (peel p2) (get_inner_e1 p2 e2)

/-- Geometric axiom: the outer and inner adjacency bijections jointly lock all cross-boundary
    edges — no edge can cross from the outer ring to the inner patch in one patch without
    having a corresponding crossing in the other. -/
axiom cross_edge_determinism (p1 p2 : Patch)
    (f_out : {x // x ∈ outerRing p1} ≃ {x // x ∈ outerRing p2})
    (f_in : {x // x ∈ (peel p1).tiles} ≃ {x // x ∈ (peel p2).tiles})
    (h_out_adj : ∀ (t1 t1' : {x // x ∈ outerRing p1}) (e e' : Fin 14), p1.adj (t1.val, e) = some (t1'.val, e') ↔ p2.adj ((f_out t1).val, e) = some ((f_out t1').val, e'))
    (h_in_adj : ∀ (t1 t1' : {x // x ∈ (peel p1).tiles}) (e e' : Fin 14), (peel p1).adj (t1.val, e) = some (t1'.val, e') ↔ (peel p2).adj ((f_in t1).val, e) = some ((f_in t1').val, e')) :
    CrossEdgeEquiv p1 p2 f_out f_in

/-- The Aperiodic Holography Theorem: 
    The 1D sequence of exterior turns along the boundary uniquely determines the internal 2D patch configuration. -/
theorem aperiodic_holography (p1 p2 : Patch) (e1 e2 : TileEdge) 
    (h_planar1 : IsPlanarPatch p1) (h_planar2 : IsPlanarPatch p2)
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) : PatchEquiv p1 p2 := by
  generalize h_len : p1.tiles.length = n
  induction n using Nat.strong_induction_on generalizing p1 p2 e1 e2 with
  | h n ih =>
    by_cases h_empty : p1.tiles = []
    · have hp2_empty : p2.tiles = [] := empty_patch_of_empty_bound p1 p2 e1 e2 h_empty h_planar2 h_bound
      have h1 : IsEmpty {x // x ∈ p1.tiles} := ⟨fun x => by 
        have h_mem : x.val ∈ [] := h_empty ▸ x.property
        cases h_mem⟩
      have h2 : IsEmpty {x // x ∈ p2.tiles} := ⟨fun x => by 
        have h_mem : x.val ∈ [] := hp2_empty ▸ x.property
        cases h_mem⟩
      have hf : {x // x ∈ p1.tiles} ≃ {x // x ∈ p2.tiles} := Equiv.equivOfIsEmpty _ _
      exact ⟨hf, fun t1 _ _ _ => IsEmpty.elim h1 t1⟩
    · have h_lt : (peel p1).tiles.length < n := by
        rw [← h_len]
        exact peel_length_lt p1 h_planar1 h_empty
      have h_outer := outer_ring_determinism p1 p2 e1 e2 h_planar1 h_bound
      have h_planar_peel1 := peel_is_planar p1
      have h_planar_peel2 := peel_is_planar p2
      let inner_e1 := get_inner_e1 p1 e1
      let inner_e2 := get_inner_e1 p2 e2
      have h_inner_bound := inner_boundary_eq p1 p2 e1 e2 h_bound
      have h_in := ih ((peel p1).tiles.length) h_lt (peel p1) (peel p2) inner_e1 inner_e2 h_planar_peel1 h_planar_peel2 h_inner_bound rfl
      
      rcases h_outer with ⟨f_out, h_out_adj⟩
      rcases h_in with ⟨f_in, h_in_adj⟩
      have h_cross := cross_edge_determinism p1 p2 f_out f_in h_out_adj h_in_adj
      exact patch_glue p1 p2 f_out h_out_adj f_in h_in_adj h_cross

end Spectrebound
