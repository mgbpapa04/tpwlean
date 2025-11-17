-- SWT Imports
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.ContinuousMap.Bounded.Normed

variable {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
variable {F : Subalgebra ℝ C(Ω, ℝ)}
variable (A := F.topologicalClosure)

set_option diagnostics true
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false


/- For a polynomial p and a function a ∈ A, p ∘ a ∈ A -/
lemma SubAlgClosureUnderPolyComp (f : C(Ω, ℝ)) (hf : f ∈ A) (p : Polynomial ℝ):
    (Polynomial.aeval f p) ∈ A := by
  sorry

/- Proof that a Subalgebra is topologically closed under pointwise absolute value -/
lemma SubAlgClosureUnderAbs (f : C(Ω, ℝ)) (hf : f ∈ A):
    |f| ∈ A := by

  -- Show that f(Ω) is compact (with Ω compact)
  have h_image_compact : IsCompact (f '' Set.univ) := by
    apply IsCompact.image
    · apply isCompact_univ
    · exact f.continuous

  -- Show that f(Ω) ⊆ ℝ is bounded by BWT
  have h_image_bounded : Bornology.IsBounded (f '' Set.univ) := by
    apply h_image_compact.isBounded

  -- Define the interval [-M, M] which is the domain of g=|·|
  let M := ‖f‖
  let I := Set.Icc (-M) M
  let g: I → ℝ := fun x ↦ |x|

  -- Show that f(Ω) ⊆ I = [-M, M]
  have h_f_range : (f '' Set.univ) ⊆ I := by
    -- apply BoundedContinuousFunction.neg_norm_le_apply
    -- apply BoundedContinuousFunction.apply_le_norm
    -- rw[Set.Icc_subset_Icc]
    sorry

  -- Show that there exists a polynomial that can arbitrarily approximate abs on I by Weierstrass Approximation
  have Weierstrass : ∀ ε > 0, ∃ (p : Polynomial ℝ), ∀ y ∈ I, |Polynomial.eval y p - g y| < ε := by
    apply exists_polynomial_near_of_continuousOn
    apply ContinuousOn.abs
    exact continuousOn_id' (Set.Icc (-M) M)

  -- Re-write the goal to be equivalent to showing there is an element b ∈ A which can arbitrarily approximate |f|
  apply Metric.mem_closure_iff.mpr

  -- Fix a specific ε > 0
  intro (ε : ℝ) (hε : ε > 0)

  -- Choose the polynomial p that arbitrarily approximates |·| on I (Weierstrass)
  let p : Polynomial ℝ := Exists.choose (Weierstrass ε hε)

  -- Use the fact that p ∘ f ∈ A as A is the topological closure of a subalgebra
  apply SubAlgClosureUnderPolyComp _ f p

  -- Show that b = p ∘ f that arbitrarily approximates |f|
  have : ‖|f| - Polynomial.aeval f p‖ < ε := by
    sorry

  -- Show that this means |f| ∈ A

  done


/- Proof of Max identity with absolute value for Reals -/
lemma MaxIdentityAbsR (x y : ℝ) : 2 * max x y = (x + y + |x - y|) := by
  cases le_total x y with
  | inl leq =>
    rw[max_eq_right leq]
    rw [abs_of_nonpos (sub_nonpos_of_le leq)]
    ring
  | inr geq =>
    rw[max_eq_left geq]
    rw [abs_of_nonneg (sub_nonneg_of_le geq)]
    ring

  done


/- Proof of Min identity with absolute value for Reals -/
lemma MinIdentityAbsR (x y : ℝ) : 2 * min x y = (x + y - |x - y|) := by
  cases le_total x y with
  | inl leq =>
    rw[min_eq_left leq]
    rw [@eq_sub_iff_add_eq]
    rw [abs_of_nonpos (sub_nonpos_of_le leq)]
    ring
  | inr geq =>
    rw[min_eq_right geq]
    rw [abs_of_nonneg (sub_nonneg_of_le geq)]
    ring
  done


/- Proof of pointwise Max identity with absolute value for Functions -/
lemma MaxIdentityAbsFunc {X} [TopologicalSpace X] (f g : C(X, ℝ)) :
    2 • (f ⊔ g) = (f + g + |f - g|) := by
  ext a
  rw [@ContinuousMap.nsmul_apply]
  simp
  rw [← MaxIdentityAbsR]
  done


/- Proof of pointwise Min identity with absolute value for Functions -/
lemma MinIdentityAbsFunc {X} [TopologicalSpace X] (f g : C(X, ℝ)) :
    2 • (f ⊓ g) = (f + g - |f - g|) := by
  ext a
  rw [@ContinuousMap.nsmul_apply]
  simp
  rw [← MinIdentityAbsR]
  done


/- Proof that a Subalgebra is topologically closed under pointwise maximum -/
lemma SubAlgClosureUnderMax (F : Subalgebra ℝ C(Ω, ℝ)) (f g : A) :
    ↑f ⊔ ↑g ∈ A := by
  sorry


/- Proof that a Subalgebra is topologically closed under pointwise minimum -/
lemma SubAlgClosureUnderMin (F : Subalgebra ℝ C(Ω, ℝ)) (f g : A) :
    ↑f ⊓ ↑g ∈ A := by
  sorry


/- Definition of a Set of functions separating points -/
def SetSeparatesPoints {α β : Type*} (S : Set (α → β)) : Prop :=
  ∀ {x y : α}, x ≠ y → ∃ f ∈ S, (f x ≠ f y)


/- Definition of what it means for a Subalgebra of C(Ω, ℝ) to separate points -/
abbrev SeparatesPoints : Prop :=
  SetSeparatesPoints ((fun f : C(Ω, ℝ) ↦ (f : Ω → ℝ)) '' ↑F)


-- lemma Urysohn () : F.SeparatesPoints


/- Proof that if the Subalgebra separates points, then so does its Topological Closure -/
lemma SubAlgClosureSeparatesPoints (hF : F.SeparatesPoints) :
    A.SeparatesPoints := by
  sorry

-- lemma SubAlgClosureMatchesAt2Points {f : C(Ω, ℝ)} {g_xy : A} (F : Subalgebra ℝ C(Ω, ℝ)) (hF: F.SeparatesPoints) :
--     ∀ x y : Ω, x ≠ y → ∃ g_xy, (g_xy x = f x) ∧ (g_xy y = f y) := by
--   sorry


/- The Stone-Weierstrass Theorem -/
theorem Stone_Weierstrass (h1 : 1 ∈ F) (hF : F.SeparatesPoints) :
    A = C(Ω, ℝ) := by

  sorry
