import Mathlib.Data.Int.Basic
import Spectrebound.SpectreGeometry
namespace Spectrebound

lemma fromDegrees_eq_t_0 (x : Int) : ExteriorTurn.fromDegrees? x = some ExteriorTurn.t_0 ↔ x = 0 := by
  unfold ExteriorTurn.fromDegrees?
  split <;> simp_all

def sumAngles : List InteriorAngle → Int
  | [] => 0
  | hd :: tl => hd.toDegrees + sumAngles tl

lemma foldl_eq_sumAngles_add (l : List InteriorAngle) (init : Int) :
    l.foldl (fun acc x => acc + x.toDegrees) init = init + sumAngles l := by
  induction l generalizing init with
  | nil => simp [sumAngles]
  | cons hd tl ih =>
    dsimp [List.foldl]
    rw [ih, sumAngles]
    omega

lemma sumAngles_ge_270 (a b c : InteriorAngle) (tl : List InteriorAngle) :
    sumAngles (a :: b :: c :: tl) ≥ 270 := by
  have ha : a.toDegrees ≥ 90 := by cases a <;> decide
  have hb : b.toDegrees ≥ 90 := by cases b <;> decide
  have hc : c.toDegrees ≥ 90 := by cases c <;> decide
  have h_tl : sumAngles tl ≥ 0 := by
    induction tl with
    | nil =>
      simp [sumAngles]
    | cons hd tl ih =>
      have h : hd.toDegrees ≥ 90 := by cases hd <;> decide
      simp [sumAngles]
      omega
  simp [sumAngles]
  omega

theorem zero_degree_anchor (angles : List InteriorAngle) :
    vertexTurn angles = some ExteriorTurn.t_0 → 
    angles = [InteriorAngle.a180] ∨ angles = [InteriorAngle.a90, InteriorAngle.a90] := by
  intro h
  unfold vertexTurn at h
  have h_sum : angles.foldl (fun acc x => acc + x.toDegrees) 0 = 180 := by
    rw [fromDegrees_eq_t_0] at h
    omega
  rw [foldl_eq_sumAngles_add, Int.zero_add] at h_sum
  
  rcases angles with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · revert h_sum; decide
  · cases a <;> (revert h_sum; decide)
  · cases a <;> cases b <;> (revert h_sum; decide)
  · have h_big := sumAngles_ge_270 a b c tl
    omega

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
    angles = [InteriorAngle.a120, InteriorAngle.a120] := by
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
    angles = [InteriorAngle.a180, InteriorAngle.a90] ∨
    angles = [InteriorAngle.a90, InteriorAngle.a180] ∨
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

lemma collapse_example (a b : InteriorAngle) (h1 : a = InteriorAngle.a120) (h_pair : isValidNativePair a b = true) : b = InteriorAngle.a270 := by
  revert h_pair
  rw [h1]
  cases b <;> decide

end Spectrebound
