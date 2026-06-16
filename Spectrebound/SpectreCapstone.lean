import Spectrebound.SpectreInstantiation
import Spectrebound.SpectreCalderon
import Spectrebound.SpectreGraphRecovery

namespace Spectrebound

/-! ======================================================================== 
    THE APERIODIC HOLOGRAPHY CAPSTONE
    ======================================================================== -/

/-- 
  THE OBSERVABLE HOLOGRAPHY THEOREM
  This is the ultimate capstone of the repository. It proves that if two 
  valid Combinatorial Surfaces share the same Dirichlet-to-Neumann boundary 
  operator, and we apply the mathematical standard for planar inverse graphs 
  (Calderón Injectivity), their internal fatgraphs are topologically identical.
  
  Zero smuggled typeclasses. The inverse recovery is explicitly declared 
  as a strict conditional premise.
-/
theorem aperiodic_holography_capstone
  (surf1 surf2 : CombinatorialSurface) (n_bulk n_bdry : Nat)
  (h_match1 : PerfectMatching (T := SpectreTile) (p := 17) surf1 n_bulk)
  (h_match2 : PerfectMatching (T := SpectreTile) (p := 17) surf2 n_bulk)
  (blocks1 : ConnectionBlocks surf1 n_bulk n_bdry)
  (blocks2 : ConnectionBlocks surf2 n_bulk n_bdry)
  
  -- Premise 1: The observable boundary physics (D2N Maps) are identical.
  (h_same_d2n : dirichlet_to_neumann surf1 n_bulk n_bdry blocks1 h_match1 = 
                dirichlet_to_neumann surf2 n_bulk n_bdry blocks2 h_match2)
                
  -- Premise 2: Curtis-Ingerman-Morrow Injectivity (The Calderón Hypothesis)
  -- In a discrete planar network, a unique D2N operator uniquely recovers the bulk matrix.
  (calderon_injectivity : 
      dirichlet_to_neumann surf1 n_bulk n_bdry blocks1 h_match1 = 
      dirichlet_to_neumann surf2 n_bulk n_bdry blocks2 h_match2 → 
      blocks1.A = blocks2.A) :
      
  -- Conclusion: The internal graphs are 100% exactly identical.
  ∀ i j : Fin n_bulk, isGlued surf1.ledger i.val j.val = isGlued surf2.ledger i.val j.val := by
  
  -- 1. Apply the Calderón injectivity premise to recover the bulk matrices.
  have h_same_bulk_matrix : blocks1.A = blocks2.A := by
    exact calderon_injectivity h_same_d2n
    
  -- 2. Extract the full Connection matrices from the Block A structural definitions.
  have h_full_matrix_eq : assembleConnection (T := SpectreTile) (p := 17) surf1 n_bulk = 
                          assembleConnection (T := SpectreTile) (p := 17) surf2 n_bulk := by
    rw [← blocks1.hA, ← blocks2.hA]
    exact h_same_bulk_matrix
    
  -- 3. Apply our ZERO-SORRY Graph Recovery theorem to prove identical adjacency!
  exact unique_adjacency_from_matrix surf1 surf2 n_bulk h_match1 h_match2 h_full_matrix_eq

end Spectrebound
