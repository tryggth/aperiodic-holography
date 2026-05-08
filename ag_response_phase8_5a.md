# Phase 8.5a: Pure Combinatorial Bijection Construction

## Execution Status
- Build command: `lake build > cmd_status.log 2>&1`
- **Exit code: 0** — `Build completed successfully (1030 jobs)`
- All theorem signatures accepted by Lean ✅

---

## What Was Changed

### `SpectreHolography.lean` — Scaffolded Index-Based Bijection

Two supporting lemmas and the scaffolded `construct_outer_ring_bijection` replaced the previous single-sorry stub. Two engineering corrections were required:

**1. `noncomputable def` (not `def`):**
The original script used `by` tactic mode with `have ⟨l1, l2, ...⟩ :=`, which triggers `Exists.casesOn`. Since `construct_outer_ring_bijection` returns `≃` (a `Type`, not a `Prop`), Lean 4 disallows this elimination. Fixed by switching to term-mode with `Classical.choose`/`choose_spec` chaining via `noncomputable def`:
```lean
noncomputable def construct_outer_ring_bijection ... :=
  let seq := boundary_sequence_eq p1 p2 e1 e2 h_planar1 h_bound
  let l1 := seq.choose
  let l2 := seq.choose_spec.choose
  let hl1 : ... := seq.choose_spec.choose_spec.1
  ...
```

**2. `List.idxOf` (not `List.indexOf`):**
The provided script used `l1.indexOf x`, but Lean 4 / Mathlib uses `List.idxOf`. Corrected to `l1.idxOf x`.

### Final Structure

```lean
/-- A boundary walk does not visit the same tile twice. -/
lemma boundary_walk_nodup (p : Patch) (e : TileEdge) (l : List TileId)
    (h : boundaryTiles p e = some l) : l.Nodup := by sorry

/-- The tiles visited in the boundary walk are exactly the tiles in the outer ring. -/
lemma mem_boundary_walk_iff (p : Patch) (e : TileEdge) (l : List TileId)
    (h : boundaryTiles p e = some l) : ∀ x, x ∈ outerRing p ↔ x ∈ l := by sorry

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
  { toFun := fun ⟨x, hx⟩ =>
      let idx := l1.idxOf x
      ⟨l2.get ⟨idx, by sorry⟩, by sorry⟩
    invFun := fun ⟨y, hy⟩ =>
      let idx := l2.idxOf y
      ⟨l1.get ⟨idx, by sorry⟩, by sorry⟩
    left_inv := by sorry
    right_inv := by sorry }
```

---

## Sorry Inventory After Phase 8.5a

| Line | Declaration | Obligation |
|------|------------|------------|
| 118 | `boundary_walk_nodup` | Prove boundary walk has no duplicate tiles |
| 123 | `mem_boundary_walk_iff` | Prove boundary walk ↔ outerRing membership |
| 140 | `construct_outer_ring_bijection` toFun `h_idx` | `l1.idxOf x < l2.length` (from equal lengths + membership) |
| 140 | `construct_outer_ring_bijection` toFun `hx2` | `l2.get ⟨idx, ...⟩ ∈ outerRing p2` (from `h_mem2`) |
| 143 | `construct_outer_ring_bijection` invFun `h_idx` | `l2.idxOf y < l1.length` |
| 143 | `construct_outer_ring_bijection` invFun `hx1` | `l1.get ⟨idx, ...⟩ ∈ outerRing p1` |
| 144 | `construct_outer_ring_bijection` `left_inv` | Round-trip: forward ∘ inverse = id |
| 145 | `construct_outer_ring_bijection` `right_inv` | Round-trip: inverse ∘ forward = id |
| 154 | `local_adj_determinism` | Adjacency locking from boundary word |
| 504 | `inner_boundary_eq` | Pre-existing (Phase 7.5) |
| 513 | `cross_edge_determinism` | Pre-existing (Phase 7.5) |

The scaffolding is accepted by Lean 4. All remaining sorrys are properly isolated named obligations ready for systematic closure in Phase 8.5b+.
