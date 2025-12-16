/- To Do List: -/
-- Update definitions regarding polynomials and images of functions
-- Redefine variables, assumptions and name spaces
-- Simplify lemmas with max/min or sup/inf
-- Make the subalgebra non unital

/- Imports -/
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.ContinuousMap.Weierstrass

/- Linters -/
set_option diagnostics true
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

namespace SWT
open ContinuousMap Set

/- Variable declaration (to be changed to remove extra assumptions)-/
variable {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
variable {A : Subalgebra ℝ C(Ω, ℝ)} -- Unital subalgebra
variable (hA_closed : IsClosed (A : Set C(Ω, ℝ)))


/- For a polynomial p and a function f ∈ A, p ∘ f ∈ A
I suspect this needs to be redone using (aeval p).toRingHom -/
lemma polynomial_comp_mem_subalg (p : Polynomial ℝ) (f : C(Ω, ℝ)) (hf : f ∈ A) :
    (p.toContinuousMap.comp f) ∈ A := by

  -- Show that the composition is equal to the algebraic evaluation
  have h_eq : p.toContinuousMap.comp f = Polynomial.aeval f p := by
    ext x
    simp

  -- Now prove the result for the aeval
  rw [h_eq]

  -- By induction on polynomials:
  induction p using Polynomial.induction_on with
  -- A constant function composed with f remains in the algebra (as it becomes a constant function)
  | C r =>
    simp only [Polynomial.aeval_C, algebraMap_mem] -- Uses that the algebra is unital so contains all constant functions
  -- A monomial composed with f remains in the algebra (closed under scalar and elementwise multiplication)
  | monomial p hp =>
    simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    finiteness
  -- Addition of monomials remains in the algebra
  | add p q hp hq =>
    simp only [map_add]
    bound

  done


/- Proof that pointwise absolute value of a function can be arbitrarily approximated in the subalgebra-/
lemma exists_mem_near_abs (ε : ℝ) (hε : 0 < ε) (f : C(Ω, ℝ)) (hf : f ∈ A) :
    ∃ a ∈ A, ‖a - |f|‖ < ε := by -- Swap this around

  -- Define an interval K that covers f(Ω)
  let M := ‖f‖
  let K := Icc (-M) M

  -- Show that the image of f is contained within k
  have h_range : MapsTo f univ K := by
    intro x _
    rw [mem_Icc, ← @abs_le]
    exact norm_coe_le_norm f x

  -- Define a function g = |·| on the interval K
  let g : C(K, ℝ) := ⟨fun y => |(y : ℝ)|, continuous_abs.comp continuous_subtype_val⟩

  -- Show that there exists a polynomial that can arbitrarily approximate g on K by Weierstrass Approximation
  have Weierstrass : ∃ (p : Polynomial ℝ), ‖p.toContinuousMapOn K - g‖ < ε := by
    apply exists_polynomial_near_continuousMap
    exact hε

  -- Select a p for an arbitrary ε
  obtain ⟨p, hp⟩ := Weierstrass

  -- Use p ∘ f as a in the proof to approximate g ∘ f = |f|
  use p.toContinuousMap.comp f -- aeval?

  constructor
  -- Use the lemma that shows p ∘ f ∈ A
  · apply polynomial_comp_mem_subalg
    apply hf
  --
  · rw [ContinuousMap.norm_lt_iff _ hε] at hp ⊢ -- Apply "ext" to hp and our goal
    intro x -- Fix an x
    specialize hp ⟨f x, h_range (Set.mem_univ x)⟩ -- Exchange x ∈ K for f(x) ∈ f(Ω) ⊆ K where x ∈ Ω
    exact hp
  done


/- Proof that a Subalgebra is topologically closed under pointwise absolute value -/
lemma abs_mem_subalg (f : C(Ω, ℝ)) (hf : f ∈ A) (hA : IsClosed (A : Set C(Ω, ℝ))):
    |f| ∈ A := by
  -- Re write the goal to use the epsilon definition
  rw [← SetLike.mem_coe]
  rw [← hA.closure_eq]
  rw [Metric.mem_closure_iff]
  intro ε hε

  -- Apply the result that |·| can be arbitrarily approximated
  obtain ⟨a, ha, ha_dist⟩ := exists_mem_near_abs ε hε f hf
  use a

  constructor
  -- Use that a ∈ A
  · exact ha
  -- Show the distance is less than ε
  · rw [dist_eq_norm]
    rw [← neg_sub a |f|]
    rw [norm_neg]
    exact ha_dist
  done


/- Proof of Max identity with absolute value for Reals -/
lemma max_id_abs (x y : ℝ) : max x y = 1/2 * (x + y + |x - y|) := by
  -- Split into the case where x ≤ y or y ≤ x
  cases le_total x y with
  | inl leq => -- x ≤ y
    rw[max_eq_right leq]
    rw [abs_of_nonpos (sub_nonpos_of_le leq)]
    ring
  | inr geq => -- x ≥ y
    rw[max_eq_left geq]
    rw [abs_of_nonneg (sub_nonneg_of_le geq)]
    ring
  done


/- Proof of Min identity with absolute value for Reals (rw using above)-/
lemma min_id_abs (x y : ℝ) : min x y = 1/2 * (x + y - |x - y|) := by
-- Split into the case where x ≤ y or y ≤ x
  cases le_total x y with
  | inl leq => -- x ≤ y
    rw[min_eq_left leq]
    rw [abs_of_nonpos (sub_nonpos_of_le leq)]
    ring
    | inr geq => -- x ≥ y
    rw[min_eq_right geq]
    rw [abs_of_nonneg (sub_nonneg_of_le geq)]
    ring
  done


/- Proof of pointwise Max identity with absolute value for Functions -/
lemma max_id_abs_func (f g : C(Ω, ℝ)) :
    f ⊔ g = (1/2 : ℝ) • (f + g + |f - g|) := by
  -- Convert from functions into points
  ext a
  rw [@smul_apply, sup_apply]
  -- Apply above result for max
  rw [max_id_abs]
  simp
  done


/- Proof of pointwise Min identity with absolute value for Functions -/
lemma min_id_abs_func (f g : C(Ω, ℝ)) :
    f ⊓ g = (1/2 : ℝ) • (f + g - |f - g|) := by
  -- Convert from functions into points
  ext a
  rw [@smul_apply, inf_apply]
  -- Apply above result for min
  rw [min_id_abs]
  simp
  done


/- Proof that a Subalgebra is topologically closed under pointwise maximum -/
lemma sup_mem_of_closed_subalg (f g : A) (hA : IsClosed (A : Set C(Ω, ℝ))) :
    (f : C(Ω, ℝ)) ⊔ (g : C(Ω, ℝ)) ∈ A := by
  -- Apply the sup identity
  rw [max_id_abs_func]
  -- Simplify and split into terms that are trivially in A
  simp only [one_div, smul_add]
  apply A.add_mem
  · apply A.add_mem
    · apply A.smul_mem
      apply SetLike.coe_mem
    · apply A.smul_mem
      apply SetLike.coe_mem
  · apply A.smul_mem
    apply abs_mem_subalg
    · apply A.sub_mem
      · apply SetLike.coe_mem
      · apply SetLike.coe_mem
    · apply hA
  done


/- Proof that a Subalgebra is topologically closed under pointwise minimum -/
lemma inf_mem_of_closed_subalg (f g : A) (hA : IsClosed (A : Set C(Ω, ℝ))) :
    (f : C(Ω, ℝ)) ⊓ (g : C(Ω, ℝ)) ∈ A := by
  -- Apply the sup identity
  rw [min_id_abs_func]
  -- Simplify and split into terms that are trivially in A
  simp only [one_div, smul_add, smul_sub]
  apply A.sub_mem
  · apply A.add_mem
    · apply A.smul_mem
      apply SetLike.coe_mem
    · apply A.smul_mem
      apply SetLike.coe_mem
  · apply A.smul_mem
    apply abs_mem_subalg
    · apply A.sub_mem
      · apply SetLike.coe_mem
      · apply SetLike.coe_mem
    · apply hA
  done


-- /- Uryshon Lemma -/
-- lemma Urysohn () : F.SeparatesPoints


/- Proof that if the Subalgebra separates points, then so does its Topological Closure -/
lemma subalg_closure_sep_points (h_sep : A.SeparatesPoints) :
    A.topologicalClosure.SeparatesPoints := by
  -- Rewrite using definition of separating points (unfold doesn't work?)
  intro x y h_neq
  obtain ⟨f, hf_in_A, hf_sep⟩ := h_sep h_neq
  use f
  -- Use the fact that A ⊆ Closure(A)
  constructor
  · apply Set.image_mono A.le_topologicalClosure
    exact hf_in_A
  · exact hf_sep
  done


/- Proof that there exists a function in the Subalgebra that matches any function at 2 points -/
-- lemma SubAlgClosureMatchesAt2Points {f : C(Ω, ℝ)} {g_xy : A} (hF: F.SeparatesPoints) :
--     ∀ x y : Ω, x ≠ y → ∃ g_xy, (g_xy x = f x) ∧ (g_xy y = f y) := by
--   sorry


/- The Stone-Weierstrass Theorem -/
theorem stone_weierstrass (h1 : 1 ∈ A) (h_sep : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ := by
  sorry

end SWT
