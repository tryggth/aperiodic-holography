inductive ExteriorTurn where
  | t_minus_90
  | t_minus_60
  | t_0
  | t_60
  | t_90
  deriving DecidableEq, Repr, BEq

inductive EdgeParity where
  | standard
  | reversed
  deriving DecidableEq, Repr

abbrev EdgeDirection := Fin 12

structure BoundaryStep where
  turn : ExteriorTurn
  dir : EdgeDirection
  parity : EdgeParity
  deriving DecidableEq, Repr

def countTurn (steps : List BoundaryStep) (t : ExteriorTurn) : Nat :=
  (steps.filter (fun s => s.turn == t)).length

def countL90 (steps : List BoundaryStep) : Nat := countTurn steps ExteriorTurn.t_90
def countR90 (steps : List BoundaryStep) : Nat := countTurn steps ExteriorTurn.t_minus_90

def parityFlips (L : List BoundaryStep) : Nat :=
  (L.filter (fun s => s.turn == ExteriorTurn.t_90 || s.turn == ExteriorTurn.t_minus_90)).length

theorem parityFlips_eq_counts (L : List BoundaryStep) :
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
