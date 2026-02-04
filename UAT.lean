/- To Do List: -/
-- Redefine variables, assumptions and name spaces

/- Imports -/
-- Import the SWT file (Contains the imports we need including Mathlib.Tactic etc.)
import SWT

/- Linters -/
-- set_option diagnostics true
-- set_option linter.unusedSectionVars false
set_option linter.unusedTactic false  -- Clears done warnings

section UniversalApproximation
open ContinuousMap Set


-- ===============================================================
--   PART 1: Definitions
-- ===============================================================

variable {d : ℕ}  -- Dimension of the input space
variable (Ω : Set (EuclideanSpace ℝ (Fin d))) -- Domain (later assumed to be compact)

-- A Non-polynomial function
def IsNonPolynomial (σ : ℝ → ℝ) : Prop :=
  ∀ (p : Polynomial ℝ), (fun x ↦ p.eval x) ≠ σ


-- A general continuous non-polynomial activation function
variable (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (h_nonpoly : IsNonPolynomial σ)


-- A single Neuron: x ↦ σ(wᵀx + b)
noncomputable def neuron (w : EuclideanSpace ℝ (Fin d)) (b : ℝ) : C(Ω, ℝ) :=
  ⟨fun x: Ω ↦ σ (inner ℝ w x.1 + b), by fun_prop⟩


-- The set of all possible single neurons on Ω
def SetOfNeurons : Set C(Ω, ℝ) :=
  {f | ∃ (w : EuclideanSpace ℝ (Fin d)) (b : ℝ), f = neuron Ω σ hσ_cont w b}


-- A Single-Layer Perceptron (F_sigma): The span of the set of neurons
def F_sigma : Submodule ℝ C(Ω, ℝ) :=
  Submodule.span ℝ (SetOfNeurons Ω σ hσ_cont)


-- The closure of F_sigma = A, i.e. the set of functions approximable by networks
noncomputable def A : Submodule ℝ C(Ω, ℝ) :=
  (F_sigma Ω σ hσ_cont).topologicalClosure


-- ===============================================================
--   PART 2: The class of neurons with an exponential activation function forms a subalgebra F_exp
--     · We need to show it contains 1
--     · We need to show closed under elementwise multiplication
--     · We need to show closed under addition and scalar multiplication (from the submodule definition)
-- ===============================================================

-- The product of two exponential neurons is another exponential neuron
lemma neuron_mul_neuron_exp (w1 w2 : EuclideanSpace ℝ (Fin d)) (b1 b2 : ℝ) :
    (neuron Ω Real.exp Real.continuous_exp w1 b1) * (neuron Ω Real.exp Real.continuous_exp w2 b2) =
    neuron Ω Real.exp Real.continuous_exp (w1 + w2) (b1 + b2) := by
  ext x -- Use extentionallity and show that it holds for all x in Ω
  simp only [mul_apply, neuron, ContinuousMap.coe_mk] -- Use the definition of an exponential neuron
  rw[← Real.exp_add, inner_add_left] -- Use the property that exp(a + b) = exp(a) * exp(b) and the linearity of inner products
  simp only [Real.exp_eq_exp] -- Use the property that exp(x) = exp(y) ↔ x = y
  field -- Simplify the expression
  done


-- The constant function 1 is in the class of exponential neurons (1 = exp(⟨0, x⟩ + 0))
lemma one_mem_F_exp : (1 : C(Ω, ℝ)) ∈ F_sigma Ω Real.exp Real.continuous_exp := by
  -- Define the exponential neuron with zero weight and bias (which equals 1)
  have h1 : (1 : C(Ω, ℝ)) = neuron Ω Real.exp Real.continuous_exp 0 0 := by
    ext x -- We show it holds for all x in Ω
    simp [neuron, Real.exp_zero, inner_zero_left] -- Use the definition of the neuron and simplify
  rw [h1] -- Use this as the candidate neuron
  apply Submodule.subset_span -- Show that this is in the span
  use 0, 0 -- Use the zero weight and bias as the candidate neuron
  done


-- The product of two elements in F_exp is in F_exp
lemma mul_mem_F_exp (f g : C(Ω, ℝ)) (hf : f ∈ F_sigma Ω Real.exp Real.continuous_exp) (hg : g ∈ F_sigma Ω Real.exp Real.continuous_exp) :
  f * g ∈ F_sigma Ω Real.exp Real.continuous_exp := by
  -- We use induction on f, and then on g
  revert g -- Show that it holds for all g in F_exp
  induction hf using Submodule.span_induction -- Induction over all f in F_exp
  -- Case when f is a neuron
  case mem f hf =>
    intro g hg
    induction hg using Submodule.span_induction -- Induction over all g in F_exp
    -- Case when f and g are neurons
    case mem g hg =>
      obtain ⟨w1, b1, rfl⟩ := hf -- Use the definition of a neuron
      obtain ⟨w2, b2, rfl⟩ := hg -- Use the definition of a neuron
      rw [neuron_mul_neuron_exp] -- Use the property that the product of two exponential neurons is another exponential neuron
      apply Submodule.subset_span -- Show that this is in the span
      use w1 + w2, b1 + b2 -- Use the candidate neuron found in the pervious lemma
    -- Case when f is a neuron and g is zero
    case zero =>
      rw [mul_zero] -- The product is just 0
      exact Submodule.zero_mem _ -- 0 is in the span of neurons F_exp
    -- Case when f is a neuron and g is a sum of functions
    case add g1 g2 hg1 hg2 ih1 ih2 =>
      rw [mul_add] -- The product is just the sum of the products f * (g1 + g2) = f * g1 + f * g2
      exact Submodule.add_mem _ ih1 ih2 -- The sum of products of neurons is in the span F_exp
    -- Case when f is a neuron and g is a scalar multiple of a neuron
    case smul r g hg ih =>
      rw [mul_smul_comm] -- The product is just the scalar multiple of f * g
      exact Submodule.smul_mem _ r ih -- The scalar multiple of a product of neurons is in the span F_exp
  -- Case when f is zero
  case zero =>
    intro g hg -- Pick g
    rw [zero_mul] -- The product is just 0
    exact Submodule.zero_mem _ -- 0 is in the span of neurons F_exp
  -- Case when f is a sum of functions
  case add f1 f2 hf1 hf2 ih1 ih2 =>
    intro g hg -- Pick g
    rw [add_mul] -- The product is just the sum of the products (f1 + f2) * g = f1 * g + f2 * g
    exact Submodule.add_mem _ (ih1 g hg) (ih2 g hg) -- The sum of products of neurons is in the span F_exp
  -- Case when f is a scalar multiple of a function
  case smul r f hf ih =>
    intro g hg -- Pick g
    rw [smul_mul_assoc] -- The product is just the scalar multiple of f * g
    exact Submodule.smul_mem _ r (ih g hg) -- The scalar multiple of a product of neurons is in the span F_exp
  done


-- Define F_exp to be the subalgebra of C(Ω, ℝ) that the submodule of single layer perceptrons form
noncomputable def F_exp : Subalgebra ℝ C(Ω, ℝ) where
  -- 1. The underlying set is the F_exp submodule of the span of exponential neurons
  carrier := F_sigma Ω Real.exp Real.continuous_exp

  -- 2. Addition and scalar multiplication (Inherited from Submodule)
  add_mem' := (F_sigma Ω Real.exp Real.continuous_exp).add_mem
  zero_mem' := (F_sigma Ω Real.exp Real.continuous_exp).zero_mem

  -- 3. Products of elements (from the above lemma)
  mul_mem' := fun {f g} hf hg ↦ mul_mem_F_exp Ω f g hf hg

  -- 4. Constant function 1 ∈ F_exp (from the above lemma)
  one_mem' := one_mem_F_exp Ω

  -- 5. Constant functions are in F_exp
  algebraMap_mem' := fun r ↦ by
    rw [Algebra.algebraMap_eq_smul_one] -- Use the property that the algebra map is a multiple of 1
    apply Submodule.smul_mem _ r -- Use the property that the scalar multiples are in F_exp
    exact one_mem_F_exp Ω -- Use the property that 1 is in F_exp


-- ===============================================================
--   PART 3: F_exp separates points
--     · This is required to use Stone-Weierstrass Theorem
-- ===============================================================

-- Prove that ∀ x ≠ y ∈ Ω, there is an element f ∈ F_exp with f(x) ≠ f(y)
lemma F_exp_separates_points : (F_exp Ω).SeparatesPoints := by
  intro x y hxy -- Introduce x and y, and the assumption x ≠ y
  let v := x.1 - y.1 -- Define v := x - y
  have hv : v ≠ 0 := fun h ↦ hxy (Subtype.eq (sub_eq_zero.mp h)) -- Show that v is not zero as x ≠ y
  have h_norm_sq_pos : 0 < ‖v‖^2 := pow_pos (norm_pos_iff.mpr hv) 2 -- Show that the norm of v is positive

  -- 1. Define weights and bias to create the neuron f(z) = exp(⟨x-y, z-y⟩ / ‖x-y‖^2) = exp(⟨w, z⟩ + b)
  let w : EuclideanSpace ℝ (Fin d) := (‖v‖^2)⁻¹ • v -- w = v / ‖v‖^2 = (x-y) / ‖x-y‖^2
  let b : ℝ := - inner ℝ w y.1 -- b = -⟨w, y⟩ = -⟨v, y⟩ / ‖v‖^2 = -⟨x-y, y⟩ / ‖x-y‖^2

  -- 2. Use the Neuoron with this specific weight and bias
  use neuron Ω Real.exp Real.continuous_exp w b
  constructor
  -- 3. Show that this neuron is in F_exp (techincally the image is in the image of the span of exponential neurons)
  · have h_mem : neuron Ω Real.exp Real.continuous_exp w b ∈ SetOfNeurons Ω Real.exp Real.continuous_exp := by
      use w, b
    exact Set.mem_image_of_mem _ (Submodule.subset_span (R := ℝ) h_mem)
  -- 4. Show that ⟨w, x⟩ + b = 1 and ⟨w, y⟩ + b = 0
  · simp only [neuron, ContinuousMap.coe_mk] -- Apply the defintion of the neuron
    have h_inner_y : inner ℝ w y.1 + b = 0 := by simp [b] -- Show that the inner product of w and y is 0
    have h_inner_x : inner ℝ w x.1 + b = 1 := by -- Show that the inner product of w and x is 1
      simp only [b] -- Apply the defintion of b
      rw [← sub_eq_add_neg, ← inner_sub_right, show x.1 - y.1 = v from rfl] -- Show that this is the inner product of w and v
      simp only [w, inner_smul_left] -- Apply the defintion of w
      rw [real_inner_self_eq_norm_sq] -- Use that ⟨v, v⟩ = ‖v‖^2
      field_simp [h_norm_sq_pos.ne'] -- Show that the norm of v is positive
      simp only [one_div, map_inv₀, conj_trivial]
      field
  -- 5. Show that f(x) = e and f(y) = 1
    rw [h_inner_x, h_inner_y, Real.exp_zero]
    simp only [ne_eq, Real.exp_eq_one_iff, one_ne_zero, not_false_eq_true] -- Use that e ≠ 1 thus f(x) ≠ f(y)
  done


-- ===============================================================
--   PART 4: Show F_exp is dense in ⊤ = C(Ω, ℝ), i.e. UAT for F_exp
--     · We have that F_exp is a subalgebra that separates points
--     · We can apply SWT to show that F_exp is dense in C(Ω, ℝ)
-- ===============================================================

-- Define the domain to be compact
variable [CompactSpace Ω]

-- Show that F_exp is dense in C(Ω, ℝ)
lemma F_exp_UAT_top : (F_exp Ω).topologicalClosure = ⊤ := by
  exact SWT.SWT_top (F_exp_separates_points Ω) -- Apply SWT
  done

-- Show that the submodule of exponential neurons is dense in C(Ω, ℝ)
example : Submodule.topologicalClosure (F_sigma Ω Real.exp Real.continuous_exp) = ⊤ := by
  -- We want to show the underlying set of the submodule closure is the universal set.
  apply SetLike.ext' -- Convert the Subalgebra equality to a Set equality
  have h_set_eq := congr_arg SetLike.coe (F_exp_UAT_top Ω) -- Use the density of the algebra
  change closure ((F_sigma Ω Real.exp Real.continuous_exp) : Set C(Ω, ℝ)) = Set.univ -- Convert to set closure
  exact h_set_eq -- Show that the closure is the universal set
  done


-- Equivalence Check: Shows that ⊤ is indeed the set of all functions C(Ω, ℝ)
example : ((⊤ : Subalgebra ℝ C(Ω, ℝ)) : Set C(Ω, ℝ)) = Set.univ := rfl
example : ((⊤ : Submodule ℝ C(Ω, ℝ)) : Set C(Ω, ℝ)) = Set.univ := rfl


-- Show closure(F_exp) = C(Ω, ℝ)
lemma F_exp_UAT_cont : ((F_exp Ω).topologicalClosure : Set C(Ω, ℝ)) = Set.univ := by
  exact SWT.SWT_cont (F_exp_separates_points Ω) -- Apply SWT
  done

example : (Submodule.topologicalClosure (F_sigma Ω Real.exp Real.continuous_exp) : Set C(Ω, ℝ)) = Set.univ := by
  exact SWT.SWT_cont (F_exp_separates_points Ω) -- Apply SWT
  done


-- UAT for F_exp i.e. any f ∈ C(Ω, ℝ) can be arbitrarily approximated by a function g ∈ F_exp
theorem F_exp_UAT (f : C(Ω, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ F_exp Ω, ‖g - f‖ < ε := by

  -- Since f is a continuous function, it is in the closure of F_exp by UAT
  have hf_mem_closure : f ∈ (F_exp Ω).topologicalClosure := by
    rw [F_exp_UAT_top Ω]
    simp

  rw [← SetLike.mem_coe] at hf_mem_closure -- Convert to set
  change f ∈ closure ((F_exp Ω) : Set C(Ω, ℝ)) at hf_mem_closure -- Convert to set closure
  rw [Metric.mem_closure_iff] at hf_mem_closure -- Use the metric characterization of closure
  obtain ⟨g, _, hf_dist⟩ := hf_mem_closure ε hε -- Obtain g ∈ F_exp
  use g -- Need to show g ∈ F_exp and ‖g - f‖ < ε
  constructor
  · finiteness -- Use g ∈ F_exp
  · rw [dist_eq_norm, norm_sub_rev] at hf_dist -- Rewrite the distance statement as a norm
    exact hf_dist
  done

-- UAT for the submodule of exponential neurons
example (f : C(Ω, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ (F_sigma Ω Real.exp Real.continuous_exp), ‖g - f‖ < ε := by
  apply F_exp_UAT -- Use the result for the subalgebra
  exact hε -- Use ε > 0
  done

end UniversalApproximation
