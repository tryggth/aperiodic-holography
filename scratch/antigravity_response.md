# Milestone 237.5 — Execution Report: Clean Modularization of Clause 6 Inventory Logic

## Summary

The Clause 6 inventory logic has been successfully extracted from the monolithic `peel_patch` theorem into standalone, reusable lemmas. The `peel_patch` block is now compact and modular, with each clause (5, 6, 7) calling pre-verified lemmas instead of carrying inline proof mass.

**Commit:** `548e2da` — `refactor: securely script Clause 6 extraction into standalone lemmas to modularize peel_patch and fix parser crash for Milestone 237.5`

## Verification Constraints

| Constraint | Status |
|---|---|
| **Axiom Prohibition** | ✅ PASSED — No `axiom` keyword in source |
| **Warning Baseline** | ✅ PRESERVED — 11 topological `sorry` warnings (was 13 pre-milestone; 2 dead `sorry` in removed lemmas) |
| **Build** | ✅ PASSED — `lake build Spectrebound.SpectreBoundary` completed (507 jobs, 43s) |
| **Parser Crash** | ✅ FIXED — Indentation corrected from col-0 to 6-space indent for `· -- Clause 5` bullet |

## Changes Applied

### Dead Code Removed

- **`TilingPatch.orientation_uniform_invariant`** — Unused orientation uniformity lemma (contained `sorry`)
- **`TilingPatch.boundary_step_origin_invariant`** — Unused step-origin mapping lemma (contained `sorry`)

### Standalone Lemma Extraction (inserted after `sumPatchInventory_filter_peel`)

1. **`findTileAtStep_mem_or_eq`** (line 3251) — Proves that `findTileAtStep L dir def_t` returns either a list member or the default tile. Previously inlined as ~10 lines inside the Clause 6 proof block.

2. **`sumPatchInventory_reduced_patch`** (line 3263) — Proves that filtering a peel tile from a valid patch preserves the corner inventory invariant `sumPatchInventory reduced_tiles = patchCornerInventory reduced_tiles.length`. Previously duplicated as a ~25-line inline proof inside Clause 6.

### Clause 5/6/7 Block Compaction (inside `peel_patch`)

- **Clause 5** (Step Direction Boundary Bounds): Simplified from a 15-line `h_dir_propagate`/`h_step_dir_map` cascade referencing dead `orientation_uniform_invariant` / `boundary_step_origin_invariant` to a direct 2-line `intro s _hs; exact s.dir.isLt`.
- **Clause 6** (Corner Pool Inventory Invariant): Replaced ~30 lines of inline inventory arithmetic with a 7-line proof using the extracted `findTileAtStep_mem_or_eq` and `sumPatchInventory_reduced_patch` lemmas. Added `change` tactic to explicitly unfold the `t_peel` let-binding for rewriting.
- **Clause 7** (Edge Witness Containment Loop): Unchanged — already clean, using `peel_patch_general_spliced` and `peel_patch_general_remainder`.

### Parser Crash Fix

The `· -- Clause 5:` bullet at the boundary of the Clause 4/5 transition was at column 0 (no whitespace), causing Lean's parser to emit `unexpected token '·'; expected command`. Fixed to 6-space indent to match the `refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` block structure.

### `omega` Fix

The standalone `sumPatchInventory_reduced_patch` lemma's internal `omega` call needed `h_p_pos : 0 < P.tiles.length` (derived from `h_peel_mem`) to close the `P.tiles.length - 1 + 1 = P.tiles.length` Nat arithmetic gap.

**Net effect:** 49 insertions, 65 deletions (−16 lines net).

## Build Output

```
⚠ [507/507] Built Spectrebound.SpectreBoundary (43s)
warning: Spectrebound/SpectreBoundary.lean:571:4: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:776:8: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:2261:6: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:2325:6: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:2775:6: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:2807:6: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:2910:6: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:2925:6: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:3489:8: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:3785:18: declaration uses `sorry`
warning: Spectrebound/SpectreBoundary.lean:3852:8: declaration uses `sorry`
Build completed successfully (507 jobs).
```

## Modified Source Section Delta (Milestone 237.5)

```diff
diff --git a/Spectrebound/SpectreBoundary.lean b/Spectrebound/SpectreBoundary.lean
index e7b45aa..4e1f75b 100644
--- a/Spectrebound/SpectreBoundary.lean
+++ b/Spectrebound/SpectreBoundary.lean
@@ -3165,16 +3165,6 @@ instance : LawfulBEq PlacedTile where
       simp only [LawfulBEq.rfl (α := LatticePoint)]
       simp [BEq.beq, instBEqPlacedTile.beq, instDecidableEqFin, Fin.decEq]

-/-- All tiles in a valid patch have the same orientation. -/
-lemma TilingPatch.orientation_uniform_invariant (P : TilingPatch) (t1 t2 : Fin P.tiles.length) :
-  (P.tiles.get t1).orientation = (P.tiles.get t2).orientation := by
-  sorry
-
-/-- Every step in the boundary path has a direction from some tile in the patch. -/
-lemma TilingPatch.boundary_step_origin_invariant (P : TilingPatch) (steps' : List BoundaryStep) (s : BoundaryStep) (hs : s ∈ steps') :
-  ∃ (k : Nat) (hk : k < P.tiles.length), s.dir = (P.tiles.get ⟨k, hk⟩).orientation := by
-  sorry
-
 /-- Helper lemma: filtering out an element not in the list is identity. -/
 lemma filter_not_mem (L : List PlacedTile) (x : PlacedTile) (h : x ∉ L) :
   L.filter (fun t => t ≠ x) = L := by
@@ -3258,6 +3248,44 @@ lemma sumPatchInventory_filter_peel (L : List PlacedTile) (t_peel : PlacedTile)
   ext <;> (push_cast; omega)


+lemma findTileAtStep_mem_or_eq (L : List PlacedTile) (dir : EdgeDirection) (def_t : PlacedTile) :
+  findTileAtStep L dir def_t ∈ L ∨ findTileAtStep L dir def_t = def_t := by
+  induction L with
+  | nil => exact Or.inr rfl
+  | cons hd tl ih =>
+    dsimp [findTileAtStep]
+    split
+    · exact Or.inl List.mem_cons_self
+    · cases ih with
+      | inl h => exact Or.inl (List.mem_cons_of_mem hd h)
+      | inr h => exact Or.inr h
+
+lemma sumPatchInventory_reduced_patch (P : TilingPatch) (steps : List BoundaryStep)
+  (t_peel : PlacedTile) (reduced_tiles : List PlacedTile)
+  (h_bdry : is_boundary_of steps P)
+  (h_peel_mem : t_peel ∈ P.tiles)
+  (h_red : reduced_tiles = P.tiles.filter (fun t => t ≠ t_peel)) :
+  sumPatchInventory reduced_tiles = patchCornerInventory reduced_tiles.length := by
+  have h_parent_inventory := h_bdry.2.2.2.2.2.1
+  have h_inventory_peel : sumPatchInventory P.tiles = TileCornerInventory.add singleTileInventory (sumPatchInventory reduced_tiles) := by
+    rw [h_red]
+    exact sumPatchInventory_filter_peel P.tiles t_peel h_bdry.2.2.1 h_peel_mem
+  have h_patch_inventory_step : patchCornerInventory P.tiles.length = TileCornerInventory.add singleTileInventory (patchCornerInventory reduced_tiles.length) := by
+    have h_len_eq : P.tiles.length = reduced_tiles.length + 1 := by
+      have h_p_pos : 0 < P.tiles.length := by
+        cases h_t : P.tiles with
+        | nil => rw [h_t] at h_peel_mem; contradiction
+        | cons => simp
+      have h_sub_len : reduced_tiles.length = P.tiles.length - 1 := by
+        rw [h_red]
+        rw [sumPatchInventory_filter_peel.h_sub_len P.tiles t_peel h_bdry.2.2.1 h_peel_mem]
+      omega
+    dsimp [patchCornerInventory, TileCornerInventory.add, singleTileInventory]
+    rw [h_len_eq]
+    ext <;> (push_cast; omega)
+  rw [h_inventory_peel, h_patch_inventory_step] at h_parent_inventory
+  exact patch_inventory_inj (sumPatchInventory reduced_tiles) (patchCornerInventory reduced_tiles.length) h_parent_inventory
+
       · -- Clause 5: Step Direction Boundary Bounds Updates
-        have h_dir_propagate : ... [~15 lines removed]
-        have h_step_dir_map : ... [~10 lines removed]
-        intro s hs
+        intro s _hs
         exact s.dir.isLt
-      · -- Update corner pool inventory invariant
-        have h_inventory_sum : ... [~30 lines removed]
-        exact h_inventory_sum
-      · -- Update edge witness containment loop
+      · -- Clause 6: Update corner pool inventory invariant
+        have h_peel_mem : t_peel ∈ P.tiles := by
+          have h_def_in : default_tile ∈ P.tiles := List.get_mem P.tiles ⟨0, h_p⟩
+          cases findTileAtStep_mem_or_eq P.tiles anchor_step.dir default_tile with
+          | inl h => exact h
+          | inr h =>
+            change findTileAtStep P.tiles anchor_step.dir default_tile ∈ P.tiles
+            rw [h]; exact h_def_in
+        exact sumPatchInventory_reduced_patch P B.steps t_peel reduced_tiles h_bdry h_peel_mem rfl
+      · -- Clause 7: Update edge witness containment loop
```

## Predictive Horizon: Next Milestone Suggestion

### Milestone 238 — Global Inductive Minimum Perimeter Bounds (`multitile_patch_minimum_perimeter`)

**Objective:** Prove that any finite patch of `n ≥ 1` Spectre tiles has a boundary path with at least 14 edges (the irreducible perimeter of a single tile).

**Strategic Approach:**

1. **Inductive Framework Setup:** Define a `patch_perimeter_bound (n : Nat) : Prop := ∀ B : BoundaryPath, B.tile_count = n → B.steps.length ≥ 14`. The base case `n = 1` follows from the known single-tile perimeter length of 14 (already established via `spectrePerimeterTurns.length = 14`).

2. **Peel-Add Preservation:** The modularized `sumPatchInventory_reduced_patch` lemma now provides a clean interface for the inductive step. When peeling a tile via `peelBoundary`, the reduced patch satisfies the inventory invariant. The key insight for Milestone 238 is that peeling **removes at most 14 boundary edges** (one tile's worth) but the splice replacement adds at least 1 edge (since `rule.replacement.length > 0` is already proven via `rule_replacement_nonempty`). This gives the inductive inequality:
   ```
   B'.steps.length ≥ B.steps.length - 14 + 1
   ```
   Combined with `B.tile_count = n + 1` and the inductive hypothesis for `n`, this closes the bound.

3. **Edge Count Tracking:** Formalize the relationship between `steps.length` and `tile_count` by establishing that `B.steps.length = 14 * B.tile_count - 2 * (shared_edges B)` where shared edges are interior edges shared between adjacent tiles. Since each shared edge reduces the boundary by exactly 2 (one from each tile), and shared edges are always ≥ 0, we get `B.steps.length ≤ 14 * B.tile_count` with the tight lower bound requiring the `crosses_always_overlap` spatial sorry to close.

4. **Dependency on Remaining Sorries:** The `isSimple` (topological simplicity) sorry is the primary blocker. For Milestone 238, we can work *conditional* on `isSimple`, establishing the bound as `isSimple steps → steps.length ≥ 14` — which is sound and useful for downstream proofs once the spatial embedding placeholder is resolved.

**Estimated Complexity:** Medium. The core proof structure follows directly from the `peelBoundary`/`peel_preserves_boundary_properties` machinery. The main new content is the edge-count bookkeeping lemmas.
