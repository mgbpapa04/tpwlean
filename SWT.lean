-- SWT Imports
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.DenseEmbedding
import Mathlib.Algebra.Algebra.Subalgebra.Basic
-- import Mathlib.Topology.ContinuousMap.Algebra -- Separates Points
-- import Mathlib.Topology.ContinuousFunction.Lattice
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Data.Real.Basic

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
variable {F : Subalgebra ℝ C(Ω, ℝ)}
variable {A : F.topologicalClosure}

-- set_option diagnostics true

/- Proof that a Subalgebra is topologically closed under pointwise absolute value -/
lemma SubAlgClosureUnderAbs (F : Subalgebra ℝ C(Ω, ℝ)) (f : F.topologicalClosure) : |(f : C(Ω, ℝ))| ∈ F.topologicalClosure := by
  sorry

/- Proof that a Subalgebra is topologically closed under pointwise maximum -/
lemma SubAlgClosureUnderMax (F : Subalgebra ℝ C(Ω, ℝ)) (f g : F.topologicalClosure) : ↑f ⊔ ↑g ∈ F.topologicalClosure := by
  sorry

/- Proof that a Subalgebra is topologically closed under pointwise minimum -/
lemma SubAlgClosureUnderMin (F : Subalgebra ℝ C(Ω, ℝ)) (f g : F.topologicalClosure) : ↑f ⊓ ↑g ∈ F.topologicalClosure := by
  sorry

-- /- Definition of a non-zero constant function -/
-- def NonZeroConst {α β : Type*} (A : Set (α → β)) : Prop :=
--   ∀ {x y : α}, x ≠ y → ∃ f ∈ A, (f x ≠ f y)

/- Definition of a Set of functions separating points -/
def SetSeparatesPoints {α β : Type*} (A : Set (α → β)) : Prop :=
  ∀ {x y : α}, x ≠ y → ∃ f ∈ A, (f x ≠ f y)

/- Definition of what it means for a Subalgebra of C(Ω, ℝ) to separate points -/
abbrev SeparatesPoints (F : Subalgebra ℝ C(Ω, ℝ)) : Prop :=
  SetSeparatesPoints ((fun f : C(Ω, ℝ) ↦ (f : Ω → ℝ)) '' ↑F)

/- Proof that if the Subalgebra separates points, then so does its Topological Closure -/
lemma SubAlgClosureSeparatesPoints (F : Subalgebra ℝ C(Ω, ℝ)) (hF: F.SeparatesPoints) : F.topologicalClosure.SeparatesPoints := by
  sorry


/- The Stone-Weierstrass Theorem -/
theorem Stone_Weierstrass (F : Subalgebra ℝ C(Ω, ℝ)) (hF : F.SeparatesPoints) : F.topologicalClosure = C(Ω, ℝ) := by
  -- apply hF
  sorry
