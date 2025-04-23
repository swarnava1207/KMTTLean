import Mathlib
import KMTT.Matrices
import KMTT.Graph

theorem KMTT {n : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
  : G.numSpanningTrees = (G.Lapminor).det := by
    sorry
