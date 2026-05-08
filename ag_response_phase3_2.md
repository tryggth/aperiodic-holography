# Phase 3.2: Local Rigidity Lemmas - Superpositions

I have successfully expanded `SpectreRigidity.lean` to formally prove the exact exhaustive bounds of interior angles for all remaining exterior turn permutations. The proofs rigorously define the geometric conditions required to enforce tiling determinism (for positive turns) and constrained superposition (for negative turns).

## Execution and Compilation Status
Following your directive, I executed `lake build Spectrebound.SpectreRigidity` and piped the output to `cmd_status.log`.
The file compiled perfectly without any `sorry` placeholders.
`Build completed successfully (127 jobs).`

## Proof Strategy
I continued utilizing the established `foldl_eq_sumAngles_add` property to rewrite list aggregations into clean recursive sums. By defining two new bounding lemmas, `sumAngles_ge_180` (for bounding length <= 2 strings) and `sumAngles_ge_360` (for bounding length <= 4 strings), I constrained the `omega` decision procedure. This allowed `decide` to systematically filter out over-constrained or under-constrained cases in the small combinatorial spaces, leaving only the exact exact target constraints:

- Positive Turns (Deterministic bounds): Forced deterministic constraints matching singleton lists `[a120]` and `[a90]`.
- Negative Turns (Superpositions): Bounded length to < 4 configurations, resulting in the valid combinations bounded by `Or` gates.

## Added Code to `Spectrebound/SpectreRigidity.lean`

```lean
lemma fromDegrees_eq_t_60 (x : Int) : ExteriorTurn.fromDegrees? x = some ExteriorTurn.t_60 ↔ x = 60 := by
  unfold ExteriorTurn.fromDegrees?
  split <;> simp_all

lemma fromDegrees_eq_t_90 (x : Int) : ExteriorTurn.fromDegrees? x = some ExteriorTurn.t_90 ↔ x = 90 := by
  unfold ExteriorTurn.fromDegrees?
  split <;> simp_all

lemma fromDegrees_eq_t_m60 (x : Int) : ExteriorTurn.fromDegrees? x = some ExteriorTurn.t_minus_60 ↔ x = -60 := by
  unfold ExteriorTurn.fromDegrees?
  split <;> simp_all

lemma fromDegrees_eq_t_m90 (x : Int) : ExteriorTurn.fromDegrees? x = some ExteriorTurn.t_minus_90 ↔ x = -90 := by
  unfold ExteriorTurn.fromDegrees?
  split <;> simp_all

lemma sumAngles_ge_180 (a b : InteriorAngle) (tl : List InteriorAngle) :
    sumAngles (a :: b :: tl) ≥ 180 := by
  have ha : a.toDegrees ≥ 90 := by cases a <;> decide
  have hb : b.toDegrees ≥ 90 := by cases b <;> decide
  have h_tl : sumAngles tl ≥ 0 := by
    induction tl with
    | nil => simp [sumAngles]
    | cons hd tl ih =>
      have h : hd.toDegrees ≥ 90 := by cases hd <;> decide
      simp [sumAngles]
      omega
  simp [sumAngles]
  omega

lemma sumAngles_ge_360 (a b c d : InteriorAngle) (tl : List InteriorAngle) :
    sumAngles (a :: b :: c :: d :: tl) ≥ 360 := by
  have ha : a.toDegrees ≥ 90 := by cases a <;> decide
  have hb : b.toDegrees ≥ 90 := by cases b <;> decide
  have hc : c.toDegrees ≥ 90 := by cases c <;> decide
  have hd : d.toDegrees ≥ 90 := by cases d <;> decide
  have h_tl : sumAngles tl ≥ 0 := by
    induction tl with
    | nil => simp [sumAngles]
    | cons hd tl ih =>
      have h : hd.toDegrees ≥ 90 := by cases hd <;> decide
      simp [sumAngles]
      omega
  simp [sumAngles]
  omega

theorem positive_turn_60 (angles : List InteriorAngle) :
    vertexTurn angles = some ExteriorTurn.t_60 → angles = [InteriorAngle.a120] := by
  intro h
  unfold vertexTurn at h
  have h_sum : angles.foldl (fun acc x => acc + x.toDegrees) 0 = 120 := by
    rw [fromDegrees_eq_t_60] at h
    omega
  rw [foldl_eq_sumAngles_add, Int.zero_add] at h_sum
  rcases angles with _ | ⟨a, _ | ⟨b, tl⟩⟩
  · revert h_sum; decide
  · cases a <;> (revert h_sum; decide)
  · have h_big := sumAngles_ge_180 a b tl
    omega

theorem positive_turn_90 (angles : List InteriorAngle) :
    vertexTurn angles = some ExteriorTurn.t_90 → angles = [InteriorAngle.a90] := by
  intro h
  unfold vertexTurn at h
  have h_sum : angles.foldl (fun acc x => acc + x.toDegrees) 0 = 90 := by
    rw [fromDegrees_eq_t_90] at h
    omega
  rw [foldl_eq_sumAngles_add, Int.zero_add] at h_sum
  rcases angles with _ | ⟨a, _ | ⟨b, tl⟩⟩
  · revert h_sum; decide
  · cases a <;> (revert h_sum; decide)
  · have h_big := sumAngles_ge_180 a b tl
    omega

theorem negative_turn_60 (angles : List InteriorAngle) :
    vertexTurn angles = some ExteriorTurn.t_minus_60 →
    angles = [InteriorAngle.a240] ∨
    angles = [InteriorAngle.a120, InteriorAngle.a120] ∨
    angles = [InteriorAngle.a90, InteriorAngle.a150] ∨
    angles = [InteriorAngle.a150, InteriorAngle.a90] := by
  intro h
  unfold vertexTurn at h
  have h_sum : angles.foldl (fun acc x => acc + x.toDegrees) 0 = 240 := by
    rw [fromDegrees_eq_t_m60] at h
    omega
  rw [foldl_eq_sumAngles_add, Int.zero_add] at h_sum
  rcases angles with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · revert h_sum; decide
  · cases a <;> (revert h_sum; decide)
  · cases a <;> cases b <;> (revert h_sum; decide)
  · have h_big := sumAngles_ge_270 a b c tl
    omega

theorem negative_turn_90 (angles : List InteriorAngle) :
    vertexTurn angles = some ExteriorTurn.t_minus_90 →
    angles = [InteriorAngle.a270] ∨
    angles = [InteriorAngle.a120, InteriorAngle.a150] ∨
    angles = [InteriorAngle.a150, InteriorAngle.a120] ∨
    angles = [InteriorAngle.a90, InteriorAngle.a90, InteriorAngle.a90] := by
  intro h
  unfold vertexTurn at h
  have h_sum : angles.foldl (fun acc x => acc + x.toDegrees) 0 = 270 := by
    rw [fromDegrees_eq_t_m90] at h
    omega
  rw [foldl_eq_sumAngles_add, Int.zero_add] at h_sum
  rcases angles with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tl⟩⟩⟩⟩
  · revert h_sum; decide
  · cases a <;> (revert h_sum; decide)
  · cases a <;> cases b <;> (revert h_sum; decide)
  · cases a <;> cases b <;> cases c <;> (revert h_sum; decide)
  · have h_big := sumAngles_ge_360 a b c d tl
    omega
```
