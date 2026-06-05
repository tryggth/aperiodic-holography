# Milestone 155: Unique Element Sublist Filtration Bounding

## Summary of Accomplishments
We have successfully resolved the list length reduction property `h_sub_len` inside the lemma `sumPatchInventory_filter_peel` in `Spectrebound/SpectreBoundary.lean`. This completely clears the top-level inventory proof tree of `sorry` placeholders.

1. **Lemma Verification**: We fully resolved the `h_sub_len` property inside `sumPatchInventory_filter_peel`. This lemma asserts that the length of a duplicate-free list `L` after filtering out a unique element `t_peel ∈ L` is exactly `L.length - 1`.
2. **Implementation Strategy**:
   - Reverted dependent variables (`t_peel`, `h_mem`, `h_nd`) to avoid shadowing or elaborator generalization errors.
   - Performed list induction on `L`.
   - Utilized a helper lemma `filter_not_mem` to handle the case where the peeled tile is no longer present in the tail list `tl`.
   - Proved the length calculation using natural number arithmetic and `omega`.
3. **Workspace Validation**: Run `lake build Spectrebound.SpectreBoundary` to confirm clean compilation and type-checking across all targets.

## Predictive Horizon: Next Milestone Suggestion
For Milestone 156, the objective is to transition out of the corner inventory loop entirely and open verification on Clause 7: Update edge witness containment loop. We will target the standalone helper lemma `peel_patch_general_spliced` to prove that the newly introduced boundary steps at the spliced boundary insertion point correctly overlap with the remaining patch tiles.

### Blueprint for Milestone 156
Inside `peel_patch_general_spliced`, we need to resolve the contradiction case where `t_orig = t_peel`. Under this contradiction, the original tile's edge-sharing properties would collide with the boundary step, which is ruled out by boundary path simplicity `B.simple`:
```lean
  have h_neq : t_orig ≠ t_peel := by
    intro h_false_eq
    -- Extract the edge-sharing identity under the contradiction state
    have h_edge_collision : (t_orig.pos, anchor_step.dir) ∈ getPlacedTileEdges t_orig := ht_edge
    subst h_false_eq
    -- Unpack boundary simplicity to show that an interior edge cannot collide with an outer boundary edge
    have h_simple_path := B.simple
    dsimp [isSimple] at h_simple_path
    -- Show contradiction using boundary simplicity and getPlacedTileEdges properties
    sorry
```
We should:
1. Formulate a boundary simplicity contradiction helper or directly unfold `isSimple` to prove that an edge on the peeled tile `t_peel` cannot simultaneously participate in the boundary path and satisfy the interior disjointness invariant.
2. Resolve `sorry` in `peel_patch_general_spliced` and verify compilation.

### Modified Source Section Delta (Milestone 155)
```diff
diff --git a/Spectrebound/SpectreBoundary.lean b/Spectrebound/SpectreBoundary.lean
index 1a83c88..f46112e 100644
--- a/Spectrebound/SpectreBoundary.lean
+++ b/Spectrebound/SpectreBoundary.lean
@@ -2996,13 +2996,61 @@ lemma sumPatchInventory_eq_length (L : List PlacedTile) :
       dsimp [patchCornerInventory]
       ext <;> (push_cast; omega)
 
+/-- Helper lemma: filtering out an element not in the list is identity. -/
+lemma filter_not_mem (L : List PlacedTile) (x : PlacedTile) (h : x ∉ L) :
+  L.filter (fun t => t ≠ x) = L := by
+  induction L with
+  | nil => rfl
+  | cons hd tl ih =>
+      dsimp [List.filter]
+      have h_not : x ∉ tl := fun hc => h (List.mem_cons_of_mem hd hc)
+      have h_ne : hd ≠ x := fun hc => h (hc ▸ List.mem_cons_self)
+      have : (decide (hd ≠ x)) = true := by simp [h_ne]
+      rw [this]
+      dsimp
+      congr 1
+      exact ih h_not
+
 /-- Lemma: Filtering an inhabited element from a duplicate-free tile list partitions its corner inventory. -/
 lemma sumPatchInventory_filter_peel (L : List PlacedTile) (t_peel : PlacedTile) 
   (h_nd : L.Nodup) (h_mem : t_peel ∈ L) :
   sumPatchInventory L = TileCornerInventory.add singleTileInventory (sumPatchInventory (L.filter (fun t => t ≠ t_peel))) := by
   rw [sumPatchInventory_eq_length, sumPatchInventory_eq_length]
   have h_sub_len : (L.filter (fun t => t ≠ t_peel)).length = L.length - 1 := by
-    sorry
+    revert t_peel h_mem h_nd
+    induction L with
+    | nil =>
+        intro t_peel h_nd h_mem
+        contradiction
+    | cons hd tl ih =>
+        intro t_peel h_nd h_mem
+        by_cases h_eq : hd = t_peel
+        · subst h_eq
+          have h_not_mem : hd ∉ tl := (List.nodup_cons.mp h_nd).1
+          have h_filter_id := filter_not_mem tl hd h_not_mem
+          dsimp [List.filter]
+          have : (decide (hd ≠ hd)) = false := by simp
+          rw [this]
+          dsimp
+          rw [h_filter_id]
+        · have : (decide (hd ≠ t_peel)) = true := by
+            simp [h_eq]
+          dsimp [List.filter]
+          rw [this]
+          dsimp
+          have h_mem_tl : t_peel ∈ tl := by
+            have h_mem_cons := h_mem
+            rw [List.mem_cons] at h_mem_cons
+            cases h_mem_cons with
+            | inl h => exact False.elim (h_eq h.symm)
+            | inr h => exact h
+          have h_nd_tl := (List.nodup_cons.mp h_nd).2
+          have ih_val := ih t_peel h_nd_tl h_mem_tl
+          cases tl with
+          | nil => contradiction
+          | cons hd'' tl'' =>
+              dsimp [List.length] at *
+              omega
   have h_L_pos : 0 < L.length := by
     cases L with
     | nil => contradiction
```
