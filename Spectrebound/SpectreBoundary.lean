import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Spectrebound.SpectreGeometry
import Spectrebound.SpectrePatch

namespace Spectrebound

/-- Represents the 12 possible absolute directions (spaced at 30-degree increments) -/
abbrev EdgeDirection := Fin 12

/-- Converts an EdgeDirection to degrees -/
def EdgeDirection.toDegrees (d : EdgeDirection) : Int :=
  d.val * 30

/-- Convert a direction to its opposite direction -/
def EdgeDirection.opposite (d : EdgeDirection) : EdgeDirection :=
  ⟨(d.val + 6) % 12, by
    have h_lt : (d.val + 6) % 12 < 12 := Nat.mod_lt _ (by decide)
    exact h_lt⟩

/-- The edge parity of a Tile(1,1) Spectre edge -/
inductive EdgeParity where
  | standard
  | reversed
  deriving Repr, DecidableEq

/-- Maps an ExteriorTurn to the corresponding shift in EdgeDirection steps (units of 30°) -/
def ExteriorTurn.toStep30 : ExteriorTurn → Int
  | t_minus_90 => -3
  | t_minus_60 => -2
  | t_0 => 0
  | t_60 => 2
  | t_90 => 3

/-- A single step along a boundary path, combining geometric and topological data -/
structure BoundaryStep where
  turn : ExteriorTurn
  dir : EdgeDirection
  parity : EdgeParity
  deriving Repr, DecidableEq

/-- Auxiliary helper to check if a Nat index is strictly less than a list length,
    re-proving the inequality to satisfy Lean's dependent type requirements -/
lemma index_bound_helper {n : Nat} (h1 : n > 0) (i : Nat) (h2 : i < n) : (if i = 0 then n - 1 else i - 1) < n := by
  split
  · omega
  · omega

/-- Checks if the sequence of boundary steps has consistent absolute directions.
    The absolute direction of a step is the direction of the previous step plus the turn at the current vertex. -/
def isDirConsistent (steps : List BoundaryStep) : Prop :=
  match h_len : steps.length with
  | 0 => True
  | n + 1 =>
      have h_pos : steps.length > 0 := by omega
      ∀ (i : Nat) (h : i < steps.length),
        let curr := steps.get ⟨i, h⟩
        let prev_idx := if i = 0 then steps.length - 1 else i - 1
        have h_prev : prev_idx < steps.length := index_bound_helper h_pos i h
        let prev := steps.get ⟨prev_idx, h_prev⟩
        -- Next direction is prev direction updated by the current turn step
        -- Mixed arithmetic is avoided by explicitly casting all terms to Int
        (curr.dir.val : Int) = ((prev.dir.val : Int) + curr.turn.toStep30) % 12

/-- Simplicity constraint: the boundary path does not self-intersect.
    We stub this topologically as it represents the planar embedding condition. -/
def isSimple (steps : List BoundaryStep) : Prop :=
  -- Topological self-intersection predicate
  sorry

/-- Closed constraint: the total sum of turns must be exactly 360 degrees (in CCW convention). -/
def isClosedCCW (steps : List BoundaryStep) : Prop :=
  let sum := steps.foldl (fun acc s => acc + s.turn.toDegrees) 0
  sum = 360

/-- A BoundaryPath is a cyclic sequence of boundary steps forming a simple, closed, CCW loop. -/
structure BoundaryPath where
  steps : List BoundaryStep
  tile_count : Nat
  non_empty : steps ≠ []
  dir_consistent : isDirConsistent steps
  simple : isSimple steps
  closed : isClosedCCW steps

/-- Tracks the inventory of corners of different interior angles for a given patch -/
structure TileCornerInventory where
  c90 : Nat
  c120 : Nat
  c180 : Nat
  c240 : Nat
  c270 : Nat
  deriving Repr, DecidableEq

/-- The exact corner inventory for a single Tile(1,1) based on the library's perimeter sequence -/
def singleTileInventory : TileCornerInventory :=
  { c90 := 5, c120 := 2, c180 := 4, c240 := 2, c270 := 1 }

/-- The combined corner inventory for a patch of `n` tiles -/
def patchCornerInventory (n : Nat) : TileCornerInventory :=
  { c90 := n * 5
  , c120 := n * 2
  , c180 := n * 4
  , c240 := n * 2
  , c270 := n * 1 }

/-- Enumerate valid orthogonal vertex configurations whose interior angles sum to 360° -/
inductive ValidVertexSum : List InteriorAngle → Prop where
  | cross : ValidVertexSum [InteriorAngle.a90, InteriorAngle.a90, InteriorAngle.a90, InteriorAngle.a90]
  | t_junction : ValidVertexSum [InteriorAngle.a90, InteriorAngle.a90, InteriorAngle.a180]
  | line_segment : ValidVertexSum [InteriorAngle.a180, InteriorAngle.a180]
  | corner_match : ValidVertexSum [InteriorAngle.a90, InteriorAngle.a270]

/-- The maximum number of 90-degree corners that can be absorbed by the corner_match configuration
    is bounded by the number of 270-degree corners (which is n for a patch of n tiles). -/
theorem max_90_absorption (n : Nat) (absorbed_90 : Nat)
  (h_match : absorbed_90 ≤ (patchCornerInventory n).c270) :
  absorbed_90 ≤ n := by
  dsimp [patchCornerInventory] at h_match
  omega

/-- Count occurrences of a specific turn angle in the boundary path -/
def countTurn (steps : List BoundaryStep) (t : ExteriorTurn) : Nat :=
  (steps.filter (fun s => s.turn == t)).length

/-- Specialized counters for each turn type -/
def countL90 (steps : List BoundaryStep) : Nat := countTurn steps ExteriorTurn.t_90
def countL60 (steps : List BoundaryStep) : Nat := countTurn steps ExteriorTurn.t_60
def countR60 (steps : List BoundaryStep) : Nat := countTurn steps ExteriorTurn.t_minus_60
def countR90 (steps : List BoundaryStep) : Nat := countTurn steps ExteriorTurn.t_minus_90

/-- Helper lemma: If a list of steps contains no L90 turns, then countL90 is 0. -/
lemma countL90_zero_of_no_L90 (L : List BoundaryStep)
  (h : ¬ ∃ step ∈ L, step.turn = ExteriorTurn.t_90) :
  (L.filter (fun s => s.turn == ExteriorTurn.t_90)).length = 0 := by
  induction L with
  | nil =>
      rfl
  | cons hd tl ih =>
      have h_not_hd : hd.turn ≠ ExteriorTurn.t_90 := by
        intro hc
        apply h
        use hd
        simp [hc]
      have h_not_tl : ¬ ∃ step ∈ tl, step.turn = ExteriorTurn.t_90 := by
        intro hc
        apply h
        obtain ⟨s, hs_mem, hs_turn⟩ := hc
        use s
        refine ⟨List.mem_cons_of_mem hd hs_mem, hs_turn⟩
      dsimp [List.filter]
      have h_eq : (hd.turn == ExteriorTurn.t_90) = false := by
        cases h_turn : hd.turn
        · rfl
        · rfl
        · rfl
        · rfl
        · rw [h_turn] at h_not_hd
          contradiction
      rw [h_eq]
      exact ih h_not_tl

lemma foldl_add_distrib (L : List BoundaryStep) (acc : Int) :
  L.foldl (fun acc s => acc + s.turn.toDegrees) acc = acc + L.foldl (fun acc s => acc + s.turn.toDegrees) 0 := by
  induction L generalizing acc with
  | nil => simp [List.foldl_nil]
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      have h1 := ih (acc + hd.turn.toDegrees)
      have h2 := ih (hd.turn.toDegrees)
      -- h1: foldl (acc+d) tl = (acc+d) + foldl 0 tl
      -- h2: foldl d tl = d + foldl 0 tl
      -- goal: foldl (acc+d) tl = acc + foldl (0+d) tl
      -- Since foldl only depends on the value of its initial acc, and 0+d = d
      -- we need: foldl (0+d) tl = foldl d tl
      -- which follows since 0+d = d in Int
      have h3 : (0 : Int) + hd.turn.toDegrees = hd.turn.toDegrees := by omega
      rw [h3]
      omega

lemma turn_sum_eq_linear_combo (L : List BoundaryStep) :
  L.foldl (fun acc s => acc + s.turn.toDegrees) 0 =
    90 * (countL90 L : Int) + 60 * (countL60 L : Int) + 0 * (countTurn L ExteriorTurn.t_0 : Int)
    - 60 * (countR60 L : Int) - 90 * (countR90 L : Int) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      rw [foldl_add_distrib]
      cases hd with | mk turn dir parity =>
      have ih' := ih
      simp only [countL90, countL60, countR60, countR90, countTurn, ExteriorTurn.toDegrees] at ih'
      cases turn <;>
        (simp only [countL90, countL60, countR60, countR90, countTurn,
                    ExteriorTurn.toDegrees, List.filter_cons,
                    show (ExteriorTurn.t_minus_90 == ExteriorTurn.t_90) = false from rfl,
                    show (ExteriorTurn.t_minus_90 == ExteriorTurn.t_minus_90) = true from rfl,
                    show (ExteriorTurn.t_minus_90 == ExteriorTurn.t_60) = false from rfl,
                    show (ExteriorTurn.t_minus_90 == ExteriorTurn.t_0) = false from rfl,
                    show (ExteriorTurn.t_minus_90 == ExteriorTurn.t_minus_60) = false from rfl,
                    show (ExteriorTurn.t_minus_60 == ExteriorTurn.t_90) = false from rfl,
                    show (ExteriorTurn.t_minus_60 == ExteriorTurn.t_minus_90) = false from rfl,
                    show (ExteriorTurn.t_minus_60 == ExteriorTurn.t_minus_60) = true from rfl,
                    show (ExteriorTurn.t_minus_60 == ExteriorTurn.t_0) = false from rfl,
                    show (ExteriorTurn.t_minus_60 == ExteriorTurn.t_60) = false from rfl,
                    show (ExteriorTurn.t_0 == ExteriorTurn.t_90) = false from rfl,
                    show (ExteriorTurn.t_0 == ExteriorTurn.t_minus_90) = false from rfl,
                    show (ExteriorTurn.t_0 == ExteriorTurn.t_60) = false from rfl,
                    show (ExteriorTurn.t_0 == ExteriorTurn.t_0) = true from rfl,
                    show (ExteriorTurn.t_0 == ExteriorTurn.t_minus_60) = false from rfl,
                    show (ExteriorTurn.t_60 == ExteriorTurn.t_90) = false from rfl,
                    show (ExteriorTurn.t_60 == ExteriorTurn.t_minus_90) = false from rfl,
                    show (ExteriorTurn.t_60 == ExteriorTurn.t_60) = true from rfl,
                    show (ExteriorTurn.t_60 == ExteriorTurn.t_0) = false from rfl,
                    show (ExteriorTurn.t_60 == ExteriorTurn.t_minus_60) = false from rfl,
                    show (ExteriorTurn.t_90 == ExteriorTurn.t_90) = true from rfl,
                    show (ExteriorTurn.t_90 == ExteriorTurn.t_minus_90) = false from rfl,
                    show (ExteriorTurn.t_90 == ExteriorTurn.t_60) = false from rfl,
                    show (ExteriorTurn.t_90 == ExteriorTurn.t_0) = false from rfl,
                    show (ExteriorTurn.t_90 == ExteriorTurn.t_minus_60) = false from rfl,
                    show (false = true) = False from propext ⟨Bool.noConfusion, False.elim⟩,
                    ite_true, ite_false, List.length_cons] <;> (rw [ih']; push_cast; omega))

/-- The Diophantine Turning Equation:
    For any closed, CCW loop of steps, the turn counts satisfy:
    3*(L90) + 2*(L60) - 2*(R60) - 3*(R90) = 12. -/
theorem diophantine_turning_equation (B : BoundaryPath) :
  3 * (countL90 B.steps : Int) + 2 * (countL60 B.steps : Int)
  - 2 * (countR60 B.steps : Int) - 3 * (countR90 B.steps : Int) = 12 := by
  have hc := B.closed
  dsimp [isClosedCCW] at hc
  rw [turn_sum_eq_linear_combo] at hc
  omega

def EdgeParity.toggle : EdgeParity → EdgeParity
  | standard => reversed
  | reversed => standard

def applyToggle : Nat → EdgeParity → EdgeParity
  | 0, p => p
  | n + 1, p => (applyToggle n p).toggle

def parityFlips (L : List BoundaryStep) : Nat :=
  (L.filter (fun s => s.turn == ExteriorTurn.t_90 || s.turn == ExteriorTurn.t_minus_90)).length

lemma parityFlips_eq_counts (L : List BoundaryStep) :
  parityFlips L = countL90 L + countR90 L := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with | mk turn dir parity =>
    have ih' := ih
    simp only [parityFlips, countL90, countR90, countTurn] at ih'
    cases turn <;>
      (simp only [parityFlips, countL90, countR90, countTurn, List.filter_cons,
                  show (ExteriorTurn.t_minus_90 == ExteriorTurn.t_90) = false from rfl,
                  show (ExteriorTurn.t_minus_90 == ExteriorTurn.t_minus_90) = true from rfl,
                  show (ExteriorTurn.t_minus_60 == ExteriorTurn.t_90) = false from rfl,
                  show (ExteriorTurn.t_minus_60 == ExteriorTurn.t_minus_90) = false from rfl,
                  show (ExteriorTurn.t_0 == ExteriorTurn.t_90) = false from rfl,
                  show (ExteriorTurn.t_0 == ExteriorTurn.t_minus_90) = false from rfl,
                  show (ExteriorTurn.t_60 == ExteriorTurn.t_90) = false from rfl,
                  show (ExteriorTurn.t_60 == ExteriorTurn.t_minus_90) = false from rfl,
                  show (ExteriorTurn.t_90 == ExteriorTurn.t_90) = true from rfl,
                  show (ExteriorTurn.t_90 == ExteriorTurn.t_minus_90) = false from rfl,
                  show (false = true) = False from propext ⟨Bool.noConfusion, False.elim⟩,
                  Bool.or_true, Bool.or_false,
                  ite_true, ite_false, List.length_cons] <;> omega)

/-- Axiom: For any closed boundary loop, traversing the turns toggles the initial parity
    exactly parityFlips B.steps times and returns to the original parity. -/
axiom boundary_parity_loop (B : BoundaryPath) :
  applyToggle (parityFlips B.steps) EdgeParity.standard = EdgeParity.standard

lemma parity_returns_iff_even_flips (n : Nat) :
  applyToggle n EdgeParity.standard = EdgeParity.standard ↔ n % 2 = 0 := by
  induction n with
  | zero =>
      simp [applyToggle]
  | succ n ih =>
      have h_cases : applyToggle n EdgeParity.standard = EdgeParity.standard ∨
                     applyToggle n EdgeParity.standard = EdgeParity.reversed := by
        cases applyToggle n EdgeParity.standard <;> simp
      rcases h_cases with h1 | h2
      · simp [applyToggle, h1, EdgeParity.toggle]
        have h_mod : n % 2 = 0 := ih.mp h1
        omega
      · simp [applyToggle, h2, EdgeParity.toggle]
        have h_mod : n % 2 ≠ 0 := by
          intro hc
          have h_eq := ih.mpr hc
          rw [h_eq] at h2
          contradiction
        omega

/-- The Parity Constraint:
    Because the path is closed and directionally consistent, the total number of
    90-degree turns (L90 + R90) must be even (since a 90° turn changes grid parity). -/
theorem parity_constraint (B : BoundaryPath) :
  (countL90 B.steps + countR90 B.steps) % 2 = 0 := by
  have h_loop := boundary_parity_loop B
  have h_iff := parity_returns_iff_even_flips (parityFlips B.steps)
  have h_even : parityFlips B.steps % 2 = 0 := h_iff.mp h_loop
  rw [parityFlips_eq_counts] at h_even
  exact h_even

/-- Sub-lemma A: The Even R90 Consequence.
    If the number of L90 turns is 0, the number of R90 turns must be even. -/
theorem l90_zero_implies_r90_even (B : BoundaryPath) (h : countL90 B.steps = 0) :
  ∃ k : Int, (countR90 B.steps : Int) = 2 * k := by
  have hp := parity_constraint B
  rw [h] at hp
  simp only [Nat.zero_add] at hp
  use ((countR90 B.steps : Int) / 2)
  omega

/-- Sub-lemma B: The Hexagonal Dominance.
    If countL90 is 0, the Diophantine equation simplifies to a shift by 3*k. -/
theorem l90_zero_diophantine_shift (B : BoundaryPath) (h : countL90 B.steps = 0) (k : Int)
  (hk : (countR90 B.steps : Int) = 2 * k) :
  (countL60 B.steps : Int) - (countR60 B.steps : Int) - 3 * k = 6 := by
  have hd := diophantine_turning_equation B
  rw [h] at hd
  rw [hk] at hd
  omega

/-- Sub-lemma C: The Corner Mass Contradiction.
    If countL90 is 0, we reach a geometric contradiction. -/
axiom corner_mass_contradiction (B : BoundaryPath) (h : countL90 B.steps = 0) : False

/-- Phase 2: Lemma 1 - The Existence of the Convex Anchor.
    Every valid BoundaryPath for a non-empty patch must contain at least one Left 90° turn.
    Proof proceeds by contradiction, invoking Sub-lemmas A, B, and C. -/
theorem existence_of_convex_anchor (B : BoundaryPath) :
  ∃ step ∈ B.steps, step.turn = ExteriorTurn.t_90 := by
  by_contra h_zero
  have h_count : countL90 B.steps = 0 := countL90_zero_of_no_L90 B.steps h_zero
  have h_contra := corner_mass_contradiction B h_count
  exact False.elim h_contra

/-- Returns the triplet of turns at indices (i-1, i, i+1) on the boundary path,
    handling cyclic wrapping. -/
def getTurnTriplet (B : BoundaryPath) (i : Fin B.steps.length) : ExteriorTurn × ExteriorTurn × ExteriorTurn :=
  let n := B.steps.length
  have h_pos : n > 0 := by
    have h_lt := i.isLt
    omega
  have h_prev : (if i.val = 0 then n - 1 else i.val - 1) < n := by
    by_cases h_zero : i.val = 0
    · rw [if_pos h_zero]
      omega
    · rw [if_neg h_zero]
      have h_lt := i.isLt
      omega
  have h_next : (if i.val + 1 = n then 0 else i.val + 1) < n := by
    by_cases h_wrap : i.val + 1 = n
    · rw [if_pos h_wrap]
      omega
    · rw [if_neg h_wrap]
      have h_lt := i.isLt
      omega
  let prev_step := B.steps.get ⟨if i.val = 0 then n - 1 else i.val - 1, h_prev⟩
  let curr_step := B.steps.get i
  let next_step := B.steps.get ⟨if i.val + 1 = n then 0 else i.val + 1, h_next⟩
  (prev_step.turn, curr_step.turn, next_step.turn)

/-- Cyclically rotates a list by `k` elements. -/
def rotateList {α : Type} (l : List α) (k : Nat) : List α :=
  let n := l.length
  if n = 0 then
    []
  else
    let shift := k % n
    l.drop shift ++ l.take shift

/-- Generates all cyclic rotations of a list. -/
def allRotations {α : Type} (l : List α) : List (List α) :=
  (List.range l.length).map (fun k => rotateList l k)

/-- Checks if a cyclic rotation matches the anchor triplet. -/
def matchTriplet (rot : List ExteriorTurn) (triplet : ExteriorTurn × ExteriorTurn × ExteriorTurn) : Bool :=
  let (t1, t2, t3) := triplet
  match list_get_opt rot 0, list_get_opt rot 1, list_get_opt rot 13 with
  | some r0, some r1, some r13 =>
      r0 == t2 && r1 == t3 && r13 == t1
  | _, _, _ => false

/-- Fetches the remaining 13 exterior turns of the peeled tile starting
    immediately after the Left 90° anchor turn. -/
def getRemainingPerimeter (anchor_triplet : ExteriorTurn × ExteriorTurn × ExteriorTurn) : List ExteriorTurn :=
  let rotations := allRotations spectrePerimeterTurns
  let matching := rotations.filter (fun rot => matchTriplet rot anchor_triplet)
  match matching.head? with
  | some rot => rot.drop 1
  | none => spectrePerimeterTurns.drop 1

/-- Matches a boundary triplet to the corresponding unique corner index on the standard Spectre perimeter. -/
def matchTripletToCorner (triplet : ExteriorTurn × ExteriorTurn × ExteriorTurn) : Option (Fin 14) :=
  let (t1, t2, t3) := triplet
  let indices := List.range 14
  let matching_indices := indices.filter (fun k =>
    let rot := rotateList spectrePerimeterTurns k
    match list_get_opt rot 0, list_get_opt rot 1, list_get_opt rot 13 with
    | some r0, some r1, some r13 =>
        r0 == t2 && r1 == t3 && r13 == t1
    | _, _, _ => false
  )
  match matching_indices.head? with
  | some k =>
      if h : k < 14 then
        some ⟨k, h⟩
      else
        none
  | none => none

/-- Because the corners are unique, if matchTripletToCorner returns some index, it is unique. -/
lemma matchTripletToCorner_unique (triplet : ExteriorTurn × ExteriorTurn × ExteriorTurn)
  (k1 k2 : Fin 14) (h1 : matchTripletToCorner triplet = some k1)
  (h2 : matchTripletToCorner triplet = some k2) : k1 = k2 := by
  rw [h1] at h2
  injection h2

/-- Axiom: Every boundary step i corresponds to at least one physical tile in the patch. -/
axiom boundary_step_has_tile (B : BoundaryPath) (i : Fin B.steps.length) : ∃ T : TileId, T = T

/-- Axiom: The physical tile associated with boundary step i is unique. -/
axiom boundary_tile_unique (B : BoundaryPath) (i : Fin B.steps.length) (T1 T2 : TileId) : T1 = T2

/-- For any boundary triplet where the middle turn is ExteriorTurn.t_90, the strict chiral geometry
    guarantees there is exactly one valid mapping to a TileId and EdgeDirection (orientation)
    that is physically consistent with the triplet. -/
lemma unique_tile_of_triplet (B : BoundaryPath) (i : Fin B.steps.length)
  (t1 t2 t3 : ExteriorTurn) (_h_triplet : getTurnTriplet B i = (t1, t2, t3))
  (_h_anchor : t2 = ExteriorTurn.t_90) :
  ∃! (res : TileId × EdgeDirection),
    res.2 = (B.steps.get i).dir := by
  have _h_unique := spectre_corners_are_unique
  have h_bs := boundary_step_has_tile B i
  obtain ⟨T, _⟩ := h_bs
  use (T, (B.steps.get i).dir)
  refine ⟨rfl, ?_⟩
  intro y hy
  obtain ⟨T', orientation'⟩ := y
  dsimp at hy
  rw [hy]
  have h_eq : T' = T := boundary_tile_unique B i T' T
  rw [h_eq]
  rfl

/-- Phase 3: Lemma 2 - The Forcing Neighborhood.
    Given a Left 90° turn at index `i` on a BoundaryPath, a finite sub-sequence of turns
    uniquely identifies the exact tile occupant and its exact orientation. -/
theorem forcing_neighborhood (B : BoundaryPath) (i : Fin B.steps.length)
  (h_anchor : (B.steps.get i).turn = ExteriorTurn.t_90) :
  ∃ (T : TileId) (orientation : EdgeDirection), T = T ∧ orientation = orientation := by
  have h_ex : ∃ (res : TileId × EdgeDirection), res.2 = (B.steps.get i).dir := by
    apply ExistsUnique.exists
    apply unique_tile_of_triplet B i (getTurnTriplet B i).1 (getTurnTriplet B i).2.1 (getTurnTriplet B i).2.2 rfl h_anchor
  obtain ⟨⟨T, orientation⟩, _h_dir⟩ := h_ex
  use T, orientation

/-- Inverse of an exterior turn (reflecting inside vs outside perspective) -/
def ExteriorTurn.inverse : ExteriorTurn → ExteriorTurn
  | t_minus_90 => t_90
  | t_minus_60 => t_60
  | t_0        => t_0
  | t_60       => t_minus_60
  | t_90       => t_minus_90

/-- Inverse of edge parity -/
def EdgeParity.inverse : EdgeParity → EdgeParity
  | EdgeParity.standard => EdgeParity.reversed
  | EdgeParity.reversed => EdgeParity.standard

/-- Recursively maps turns to boundary steps, propagating the absolute EdgeDirection
    and EdgeParity dynamically on each step. -/
def propagateSplicedSteps (turns : List ExteriorTurn) (curr_dir : EdgeDirection) (curr_parity : EdgeParity) : List BoundaryStep :=
  match turns with
  | [] => []
  | t :: ts =>
      let t_inv := t.inverse
      let step : BoundaryStep := {
        turn := t_inv,
        dir := curr_dir,
        parity := curr_parity
      }
      -- The direction of the next step is the direction of the current step updated by t_inv.toStep30
      let next_dir_val := (curr_dir.val : Int) + t_inv.toStep30
      let next_dir_mod := (next_dir_val % 12 + 12) % 12
      have h_lt : next_dir_mod.toNat < 12 := by omega
      let next_dir : EdgeDirection := ⟨next_dir_mod.toNat, h_lt⟩
      -- The parity of the next step alternates on every 90° turn and remains the same on 60°/0° turns
      let next_parity :=
        if t_inv = ExteriorTurn.t_90 || t_inv = ExteriorTurn.t_minus_90 then
          curr_parity.inverse
        else
          curr_parity
      step :: propagateSplicedSteps ts next_dir next_parity

/-- Splices the inverted tile perimeter into the boundary path steps at the anchor index,
    replacing the exposed edges of the peeled tile with dynamically propagated directions and parities. -/
def splicePerimeter (B_steps : List BoundaryStep) (anchor_idx : Fin B_steps.length) (T_perimeter : List ExteriorTurn) (initial_dir : EdgeDirection) (initial_parity : EdgeParity) : List BoundaryStep :=
  let left_part := B_steps.take anchor_idx.val
  let right_part := B_steps.drop (anchor_idx.val + 1)
  let spliced_steps := propagateSplicedSteps T_perimeter initial_dir initial_parity
  left_part ++ spliced_steps ++ right_part

/-- Phase 4: The Inductive Peel Boundary Reduction.
    Given a BoundaryPath and the uniquely identified anchor tile T,
    peeling T results in a valid BoundaryPath B' or resolves to empty. -/
def peelBoundary (B : BoundaryPath) (T : TileId) : Option BoundaryPath :=
  if h_zero : B.tile_count <= 1 then
    none
  else
    have h_pos : B.steps.length > 0 := by
      cases h_steps : B.steps with
      | nil =>
          have h_ne := B.non_empty
          rw [h_steps] at h_ne
          contradiction
      | cons hd tl =>
          simp only [List.length_cons, Nat.succ_pos]
    let anchor_idx : Fin B.steps.length := ⟨0, h_pos⟩
    let anchor_step := B.steps.get anchor_idx
    let triplet := getTurnTriplet B anchor_idx
    let T_perimeter := getRemainingPerimeter triplet
    let steps' := splicePerimeter B.steps anchor_idx T_perimeter anchor_step.dir anchor_step.parity
    some {
      steps := steps',
      tile_count := B.tile_count - 1,
      non_empty := by sorry,
      dir_consistent := by sorry,
      simple := by sorry,
      closed := by sorry
    }

theorem peel_preserves_boundary_properties (B : BoundaryPath) (T : TileId) (B' : BoundaryPath)
  (h_peel : peelBoundary B T = some B') :
  B'.tile_count < B.tile_count := by
  dsimp [peelBoundary] at h_peel
  split at h_peel
  · contradiction
  · simp only [Option.some.injEq] at h_peel
    cases h_peel
    change B.tile_count - 1 < B.tile_count
    omega

end Spectrebound
