import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Spectrebound.SpectreGeometry

namespace Spectrebound

/-- A unique identifier for a tile in a patch -/
abbrev TileId := Nat

/-- A specific edge of a specific tile (the Spectre tile has 14 edges) -/
def TileEdge := TileId × Fin 14

/-- A combinatorial representation of a tiling patch -/
structure Patch where
  tiles : List TileId
  /-- Adjacency mapping: returns the adjacent TileEdge if one exists.
      A valid patch would require this to be an involution (symmetric relation) and
      only connect edges of tiles present in the patch.
      
      TODO: Apply geometric validity proofs (planar embedding, vertex sum checking)
      using the `vertexTurn` predicate on the edge cycles formed by this mapping. -/
  adj : TileEdge → Option TileEdge

/-- Returns all edges of tiles in the patch that are unmatched in the adjacency mapping (exposed to the outside) -/
def patchBoundary (p : Patch) : List TileEdge :=
  -- Generate all edges for all tiles in the patch
  let allEdges := p.tiles.flatMap (fun id => (List.finRange 14).map (fun e => (id, e)))
  -- Filter to keep only those that have no adjacent edge in the mapping
  allEdges.filter (fun edge => (p.adj edge).isNone)

/-- Returns the unique set of tiles that possess at least one edge in the boundary -/
def outerRing (p : Patch) : List TileId :=
  let boundaryEdges := patchBoundary p
  -- Extract the TileId from each boundary edge and remove duplicates
  let boundaryTiles := boundaryEdges.map Prod.fst
  boundaryTiles.eraseDups

/-- Given an exposed edge, finds the next exposed boundary edge by walking 
    clockwise along the native tile perimeter and crossing adj hinges. -/
partial def nextBoundaryEdge (p : Patch) (current : TileEdge) : Option TileEdge :=
  let nextNative := (current.1, current.2 + 1)
  match p.adj nextNative with
  | none => some nextNative
  | some matedEdge =>
      -- Cross the hinge to the neighboring tile and continue
      nextBoundaryEdge p matedEdge

/-- Helper to collect interior angles across mated tiles at a vertex -/
partial def vertexAtLogic (p : Patch) (curr : TileEdge) (acc : List InteriorAngle) : Option (List InteriorAngle) :=
  match Tile11[curr.2.val]? with
  | none => none
  | some angle =>
      let acc' := angle :: acc
      let nextNative := (curr.1, curr.2 + 1)
      match p.adj nextNative with
      | none => some acc'.reverse
      | some matedEdge =>
          vertexAtLogic p matedEdge acc'

/-- Collects the interior angles of all tiles meeting at the vertex
    between exposed edge e1 and exposed edge e2. -/
def vertexAt (p : Patch) (e1 _e2 : TileEdge) : Option (List InteriorAngle) :=
  -- e2 is functionally the next boundary edge from e1
  vertexAtLogic p e1 []

/-- Recursive walk of the patch perimeter to generate the sequence of exterior turns. -/
def boundaryWordLogic (p : Patch) (startEdge current : TileEdge) (acc : List ExteriorTurn) (fuel : Nat) : Option (List ExteriorTurn) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match nextBoundaryEdge p current with
    | none => none
    | some nextExposed =>
        match vertexAt p current nextExposed with
        | none => none
        | some angles =>
            match vertexTurn angles with
            | none => none
            | some turn =>
                let acc' := turn :: acc
                if nextExposed.1 == startEdge.1 && nextExposed.2 == startEdge.2 then
                  some acc'.reverse
                else
                  boundaryWordLogic p startEdge nextExposed acc' fuel'

/-- Computes the ordered sequence of exterior turns for the patch boundary. -/
def boundaryWord (p : Patch) (startEdge : TileEdge) : Option (List ExteriorTurn) :=
  boundaryWordLogic p startEdge startEdge [] (p.tiles.length * 14)

def boundaryTilesLogic (p : Patch) (startEdge current : TileEdge) (acc : List TileId) (fuel : Nat) : Option (List TileId) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match nextBoundaryEdge p current with
    | none => none
    | some nextExposed =>
        match vertexAt p current nextExposed with
        | none => none
        | some angles =>
            match vertexTurn angles with
            | none => none
            | some _ =>
                let acc' := nextExposed.1 :: acc
                if nextExposed.1 == startEdge.1 && nextExposed.2 == startEdge.2 then
                  some acc'.reverse
                else
                  boundaryTilesLogic p startEdge nextExposed acc' fuel'

/-- Computes the ordered sequence of tile IDs along the patch boundary. -/
def boundaryTiles (p : Patch) (startEdge : TileEdge) : Option (List TileId) :=
  boundaryTilesLogic p startEdge startEdge [startEdge.1] (p.tiles.length * 14)

end Spectrebound
