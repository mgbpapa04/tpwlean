-- SWT Imports
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.DenseEmbedding
import Mathlib.Algebra.Algebra.Subalgebra.Basic
-- import Mathlib.Topology.ContinuousMap.Algebra -- Separates Points
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Data.Real.Basic

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
variable {F : Subalgebra ℝ C(Ω, ℝ)}
variable {A : F.topologicalClosure}


/- Definition of a Set of functions separating points -/
def SetSeparatesPoints {α β : Type*} (A : Set (α → β)) : Prop :=
  ∀ {x y : α}, x ≠ y → ∃ f ∈ A, (f x ≠ f y)

/- Definition of what it means for a Subalgebra of C(Ω, ℝ) to separate points -/
abbrev SeparatesPoints (F : Subalgebra ℝ C(Ω, ℝ)) : Prop :=
  SetSeparatesPoints ((fun f : C(Ω, ℝ) ↦ (f : Ω → ℝ)) '' ↑F)

/- Proof that the Topological Closure that separates points, also separates points -/
lemma SubAlgClosureSeparatesPoints (F : Subalgebra ℝ C(Ω, ℝ)) (hF: F.SeparatesPoints) : F.topologicalClosure.SeparatesPoints := by
  sorry


/- The Stone-Weierstrass Theorem -/
theorem Stone_Weierstrass (F : Subalgebra ℝ C(Ω, ℝ)) (hF : F.SeparatesPoints) : F.topologicalClosure = C(Ω, ℝ) := by
  -- apply hF
  sorry
