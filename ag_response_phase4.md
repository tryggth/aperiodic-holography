# Phase 4: Holographic Recursion

I have successfully completed Phase 4 by implementing the formal structures for the topological peeling operation and stating the master Holography Theorem in `SpectreHolography.lean`.

## Execution and Compilation Status
Following the execution directive, the `lake build` output was piped into `cmd_status.log`. The project successfully built (`exit code: 0`). Lean successfully compiled the types and definitions for peeling the patch. As expected, Lean emitted warnings for the intentional `sorry` placeholders used for the placeholders `PatchEquiv` and `aperiodic_holography`. 

## Implementation Details
1. **Peel Operation**: Defined `peel p` which uses `outerRing` from `SpectrePatch.lean` to identify the boundary tiles. It filters these tiles from the `p.tiles` list and constructs a new inner patch. The adjacency mapping `newAdj` strictly verifies that any connected hinges only exist between tiles that survived the peel (removing dangling hinges).
2. **Terminal Base Case**: Defined `isOneLayer` to test if a patch is terminal (e.g. a star or worm) by checking if `peel p` yields an empty list.
3. **Master Theorem**: Stated the `aperiodic_holography` theorem linking the `boundaryWord` equivalence to a `PatchEquiv` isomorphism. Because the boundary traversal sequence must be oriented, I parameterized the theorem over two distinct starting edges (`e1` and `e2`).

## Added Code (`Spectrebound/SpectreHolography.lean`)

```lean
import Spectrebound.SpectrePatch

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

/-- A placeholder equivalence relation for patch isomorphism. 
    Two patches are equivalent if they have the same internal geometric graph. -/
def PatchEquiv (p1 p2 : Patch) : Prop := sorry

/-- The Aperiodic Holography Theorem: 
    The 1D sequence of exterior turns along the boundary uniquely determines the internal 2D patch configuration. -/
theorem aperiodic_holography (p1 p2 : Patch) (e1 e2 : TileEdge) 
    (h_bound : boundaryWord p1 e1 = boundaryWord p2 e2) : PatchEquiv p1 p2 := by
  sorry

end Spectrebound
```
