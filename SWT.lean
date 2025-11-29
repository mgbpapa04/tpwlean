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
import Mathlib.Topology.ContinuousMap.Algebra

variable {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
variable {A : Subalgebra ℝ C(Ω, ℝ)}
variable (hA_closed : IsClosed (A : Set C(Ω, ℝ)))

set_option diagnostics true
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

open ContinuousMap Set

/- For a polynomial p and a function a ∈ A, p ∘ a ∈ A -/
lemma polynomial_comp_mem_subalg (p : Polynomial ℝ) (f : C(Ω, ℝ)) (hf : f ∈ A) :
    (p.toContinuousMap.comp f) ∈ A := by
  sorry

/- Proof that a Subalgebra is topologically closed under pointwise absolute value -/
lemma exists_mem_near_abs (ε : ℝ) (hε : 0 < ε) (f : C(Ω, ℝ)) (hf : f ∈ A) :
    ∃ g ∈ A, ‖g - |f|‖ < ε := by

  let M := ‖f‖
  let K := Icc (-M) M

  -- Proof that f maps into K
  have h_range : MapsTo f univ K := by
    intro x _
    rw [mem_Icc, ← @abs_le]
    exact norm_coe_le_norm f x

  let g : C(K, ℝ) := ⟨fun y => |(y : ℝ)|, continuous_abs.comp continuous_subtype_val⟩

  -- Show that there exists a polynomial that can arbitrarily approximate abs on I by Weierstrass Approximation
  have Weierstrass : ∃ (p : Polynomial ℝ), ‖p.toContinuousMapOn K - g‖ < ε := by
    apply exists_polynomial_near_continuousMap
    exact hε

  obtain ⟨p, hp⟩ := Weierstrass

  use p.toContinuousMap.comp f

  have ha : p.toContinuousMap.comp f ∈ A := by
    apply polynomial_comp_mem_subalg
    apply hf

  constructor
  · apply ha
  · rw [ContinuousMap.norm_lt_iff _ hε] at hp ⊢
    intro x
    specialize hp ⟨f x, h_range (Set.mem_univ x)⟩
    exact hp
  done

--   apply Metric.mem_closure_iff.mpr

lemma abs_mem_subalg (f : C(Ω, ℝ)) (hf : f ∈ A) (hA : IsClosed (A : Set C(Ω, ℝ))):
    |f| ∈ A := by
  sorry

/- Proof of Max identity with absolute value for Reals -/
lemma max_id_abs (x y : ℝ) : 2 * max x y = (x + y + |x - y|) := by
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
lemma min_id_abs (x y : ℝ) : 2 * min x y = (x + y - |x - y|) := by
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
lemma max_id_abs_func (f g : C(Ω, ℝ)) :
    2 • (f ⊔ g) = (f + g + |f - g|) := by
  ext a
  rw [@ContinuousMap.nsmul_apply]
  simp
  rw [← max_id_abs]
  done


/- Proof of pointwise Min identity with absolute value for Functions -/
lemma min_id_abs_func (f g : C(Ω, ℝ)) :
    2 • (f ⊓ g) = (f + g - |f - g|) := by
  ext a
  rw [@ContinuousMap.nsmul_apply]
  simp
  rw [← min_id_abs]
  done


/- Proof that a Subalgebra is topologically closed under pointwise maximum -/
lemma sup_mem_of_closed_subalg (f g : A) (hA : IsClosed (A : Set C(Ω, ℝ))) :
    ↑f ⊔ ↑g ∈ A := by
  sorry


/- Proof that a Subalgebra is topologically closed under pointwise minimum -/
lemma inf_mem_of_closed_subalg (f g : A) (hA : IsClosed (A : Set C(Ω, ℝ))) :
    ↑f ⊓ ↑g ∈ A := by
  sorry


/- Definition of a Set of functions separating points -/
def SetSeparatesPoints {α β : Type*} (S : Set (α → β)) : Prop :=
  ∀ {x y : α}, x ≠ y → ∃ f ∈ S, (f x ≠ f y)


/- Definition of what it means for a Subalgebra of C(Ω, ℝ) to separate points -/
abbrev SeparatesPoints : Prop :=
  SetSeparatesPoints ((fun f : C(Ω, ℝ) ↦ (f : Ω → ℝ)) '' ↑A)


-- lemma Urysohn () : F.SeparatesPoints


/- Proof that if the Subalgebra separates points, then so does its Topological Closure -/
lemma subalg_closure_sep_points (h_sep : A.SeparatesPoints) :
    A.topologicalClosure.SeparatesPoints := by
  sorry

-- lemma SubAlgClosureMatchesAt2Points {f : C(Ω, ℝ)} {g_xy : A} (F : Subalgebra ℝ C(Ω, ℝ)) (hF: F.SeparatesPoints) :
--     ∀ x y : Ω, x ≠ y → ∃ g_xy, (g_xy x = f x) ∧ (g_xy y = f y) := by
--   sorry


/- The Stone-Weierstrass Theorem -/
theorem stone_weierstrass (h1 : 1 ∈ A) (h_sep : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ := by
  sorry
