# Phase 6.4: Subset Topology and Bijection Inverses

Phase 6.4 is entirely complete! The topological subset abstractions (`outerRing_subset`, `peel_subset`, `subset_of_peel`, and `not_outerRing_of_peel`) have been formalized and rigorously proved without `sorry`. Using these rules, I successfully assembled and verified the full bijection (`left_inv` and `right_inv`) for the topological glue `Equiv` function.

## Execution and Compilation Status
Execution logged silently to `cmd_status.log`. Lean 4 compiled successfully (`exit code: 0`). The `patch_glue` theorem now fully instantiates the domain `Equiv`, leaving the adjacency mapping geometric constraint (the graph edges verification) as the sole intended mathematical `sorry` in this lemma, precisely as requested.

## Implementation Details

1. **Subset Formalization**:
   - `outerRing_subset`: Extracted and formalized the cyclic ring `eraseDups` and `patchBoundary` unrolling logic initially designed in Phase 5.3.
   - `peel_subset` & `subset_of_peel`: Directly mapped logical boundaries over the `peel` def via `List.mem_filter.mpr`. `not_outerRing_of_peel` uses boolean `List.contains_iff_mem` contradiction.

2. **Inverse Equivalence (`left_inv` & `right_inv`)**:
   - I used `by_cases h : x.val ∈ outerRing` over `dsimp [forward_fn, inverse_fn]` to split the topological branches.
   - Using `rw [dif_pos]` and `rw [dif_neg]`, I isolated the specific nested equivalences (e.g., `f_out.symm_apply_apply`).
   - The primary challenge in Lean 4 here is that `congrArg` on subtypes evaluates strictly. I used `Subtype.ext rfl` coercion equations like `have h_y : (⟨...⟩ : ...) = f_out ⟨x.val, h⟩ := Subtype.ext rfl` to rigorously convince Lean's kernel that re-wrapping the resulting boundary values in dependent subsets preserves referential equality against the mapped `Equiv` variables.

## Updated Code Snippet (`Spectrebound/SpectreHolography.lean`)
```lean
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

/-- Piecewise topological bijection.
    If the outer rings of two patches are isomorphic, and their inner peeled patches 
    are isomorphic, then the entire parent patches must be fully isomorphic. -/
lemma patch_glue (p1 p2 : Patch) (h_out : OuterRingEquiv p1 p2) (h_in : PatchEquiv (peel p1) (peel p2)) : PatchEquiv p1 p2 := by
  rcases h_out with ⟨f_out, h_out_adj⟩
  rcases h_in with ⟨f_in, h_in_adj⟩
  
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

  exact ⟨f_equiv, sorry⟩
```
