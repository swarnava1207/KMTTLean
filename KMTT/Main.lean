import Mathlib
import KMTT.Matrices
import KMTT.Graph

/-- The main theorem that we need to prove. -/
theorem KMTT {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
  : G.numSpanningTrees = (G.Lapminor).det := by
    sorry
