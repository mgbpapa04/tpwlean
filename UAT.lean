/- We have used AI tools (mostly the Google AI Overview) when searching for results that we expected
to be formalised in Mathlib, but that we were not able to find in the Mathlib documentation. -/

/- Imports -/
-- Import the SWT file (Contains all the imports we need including Mathlib.Tactic etc.)
import SWT

/- Linters -/
-- set_option diagnostics true
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false  -- Clears done warnings


section UniversalApproximation
open ContinuousMap Set


-- ===============================================================
--   PART 1: Definitions
-- ===============================================================

variable {d : ℕ}  -- Dimension of the input space
variable (Ω : Set (EuclideanSpace ℝ (Fin d))) -- Domain (later assumed to be compact)


-- A general continuous non-polynomial activation function
variable (σ : ℝ → ℝ) (hσ_cont : Continuous σ)


-- A single Neuron: x ↦ σ(wᵀx + b)
noncomputable def neuron (w : EuclideanSpace ℝ (Fin d)) (b : ℝ) : C(Ω, ℝ) :=
  ⟨fun x: Ω ↦ σ (inner ℝ w x.1 + b), by fun_prop⟩


-- The set of all possible single neurons on Ω
def SetOfNeurons : Set C(Ω, ℝ) :=
  {f | ∃ (w : EuclideanSpace ℝ (Fin d)) (b : ℝ), f = neuron Ω σ hσ_cont w b}


-- A shallow neural network (F_sigma): The span of the set of neurons
def F_sigma : Submodule ℝ C(Ω, ℝ) :=
  Submodule.span ℝ (SetOfNeurons Ω σ hσ_cont)


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


-- Define F_exp to be the subalgebra of C(Ω, ℝ) that the submodule of shallow neural networks form
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

lemma F_exp_submodule_UAT_cont : (Submodule.topologicalClosure (F_sigma Ω Real.exp Real.continuous_exp) : Set C(Ω, ℝ)) = Set.univ := by
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


/-
Proof of the UAT for F_sigma with σ a continuous monotonic function that tends to 1 at inf and 0 at -inf
  · This uses the intermediate result that F_exp is dense in C(Ω, ℝ)
  · We define H_sigma as a shallow neural network from a compact set T ⊆ ℝ → ℝ with this activation function can approximate the exponential function
  · This hardest part of the proof is showing that this H_sigma can approximate the exponential function on T (we have not done this)
  · The approach we take for this is as follows:
    1. Define H_sigma as the span of the set of scalar neurons over T
    2. Show that a sigma of this form can approximate a step function
        · e.g. (tanh + 1)/2 is an example of this type of activation function (i.e. monotonic, continuous, with the right limits)
        · Imagine the function (tanh(wx - wb) + 1)/2
        · As w approaches infinity, the function approaches θ(x-b) (heavyside step function at b)
    3. Show that exp can be approximated by step functions on T (and thus by H_sigma)
    4. Show that our approximation of exp composed with an affine map is an element of F_sigma
    5. Show that an element of F_sigma (namely the one we just showed was in F_sigma) can approxmiate an exponential neuron
    6. Show that any function in the algebra F_exp can be approximated by F_sigma (i.e. F_exp = Closure(F_sigma))
    7. Show that Closure(F_sigma) = ⊤ = C(Ω, ℝ) i.e. the UAT for F_sigma
-/

-- A class for activation functions that are "sigmoidal"
-- They must be monotone, and tend to 0 at -∞ and 1 at +∞
-- We are also assuming that σ is continuous as defined above
-- You can imagine a function like (tanh(x) + 1)/2 or the sigmoid function
class Sigmoidal (σ : ℝ → ℝ) : Prop where
  monotone : Monotone σ
  lim_at_bot : Filter.Tendsto σ Filter.atBot (nhds 0)
  lim_at_top : Filter.Tendsto σ Filter.atTop (nhds 1)

variable [Sigmoidal σ] -- We define σ to be sigmoidal for this proof


-- We define a compact subset of ℝ for H_sigma to approximate exp on
variable {T : Set ℝ} [CompactSpace T]


-- We define the set of scalar neurons over T (this will be the image of the F_sigma on Ω)
def SetOfScalarNeurons (T : Set ℝ) : Set C(T, ℝ) :=
  {f | ∃ (u v : ℝ), f = fun t : T ↦ σ (u * (t : ℝ) + v)}


-- We define the submodule H_sigma formed by the span of these scalar neurons (shallow neural networks T ⊆ ℝ → ℝ)
def H_sigma (T : Set ℝ) : Submodule ℝ C(T, ℝ) :=
  Submodule.span ℝ (SetOfScalarNeurons σ T)


-- ===============================================================
--   PART 5: Show H_sigma can approximate exp to arbitrary precision
--     · We defined H_sigma as a shallow neural network from a compact subset T ⊆ ℝ → ℝ
--     · We can then show that H_sigma can approximate exp to arbitrary precision on T
--     · This will allow us to swap the exponential activation function with an approximation in H_sigma
-- ===============================================================

-- Show that a sigma of this form can approximate a step function
-- We are showing that ‖σ - θ‖ < ε outside some interval [z-δ, z+δ]
-- This is our first step in showing that H_sigma can approximate exp to arbitrary precision on T
-- We don't end up using this lemma but it would be used in the proof that H_sigma can approximate exp on T
-- e.g. (tanh + 1)/2 is an example of this type of activation function (i.e. monotonic, continuous, with the right limits)
--      Imagine the function (tanh(wx - wb) + 1)/2
--      As w approaches infinity, the function approaches θ(x-b) (heavyside step function at b)
lemma sigma_approx_step (z : ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) : ∃ w b : ℝ,
    (∀ x, x < z - δ → |σ (w * x + b)| < ε) ∧ -- σ(w*x+b) ≈ 0 for x < z-δ
    (∀ x, z + δ < x → |σ (w * x + b) - 1| < ε) := by -- σ(w*x+b) ≈ 1 for x > z+δ

  -- 1. Unpack the limit definitions using the definition of a limit

  -- Convert the lower limit into ∀ x ≤ M1, d(σ(x), 0) < ε
  have h_bot := Metric.tendsto_nhds.mp (@Sigmoidal.lim_at_bot σ _) ε hε
  rw [Filter.eventually_atBot] at h_bot -- Convert into the distance form
  obtain ⟨M1, hM1⟩ := h_bot -- Call this lower bound M1, (hM1 : ∀ x ≤ M1, dist (σ x) 0 < ε)

  -- Convert the upper limit into ∀ x ≥ M2, d(σ(x), 1) < ε
  have h_top := Metric.tendsto_nhds.mp (@Sigmoidal.lim_at_top σ _) ε hε
  rw [Filter.eventually_atTop] at h_top -- Convert into the distance form
  obtain ⟨M2, hM2⟩ := h_top -- Call this upper bound M2, (hM2 : ∀ x ≥ M2, dist (σ x) 1 < ε)

  -- 2. Define parameters to compress the transition from 0 to 1 into the interval (z-δ, z+δ)
  let num : ℝ := |M1| + |M2| + 1 -- This is what we scale w by to ensure this
  let w := num / δ -- Define w large enough to compress the transition into a width of 2δ
  let b := -w * z -- Define b to center the transition at z

  -- Show that w > 0
  have hw_pos : 0 < w := by
    dsimp [w] -- Apply the definition of w
    apply div_pos -- Show this by showing numerator and denominator are positive
    · dsimp [num] -- Apply the definition of num
      finiteness -- Apply the fact that num is positive
    · exact hδ -- Apply the fact that δ is positive

  use w, b -- Use this w and b in our goal

  -- We now have to show each side of the goal
  constructor
  -- 3. Prove that ∀ x < z - δ, then |σ (w*x + b)| < ε
  · intro x hx
    have h_bound : w * x + b ≤ M1 := by -- Want to show w*x + b ≤ M1 to apply hM1
      dsimp [w, b] -- Apply the definition of w and b
      ring_nf -- Simplify
      field_simp -- Simplify
      nlinarith [hx, abs_nonneg M1, abs_nonneg M2, neg_abs_le M1] -- Simplify

    specialize hM1 (w * x + b) h_bound -- Use hM1 to show that d(σ(w*x+b), 0) < ε
    rw [Real.dist_eq, sub_zero] at hM1 -- Use the definition of distance to show that |σ(w*x+b)| < ε
    exact hM1

  -- 4. Prove that ∀ x > z + δ, then |σ (w*x + b) - 1| < ε
  · intro x hx
    have h_bound : M2 ≤ w * x + b := by -- Want to show M2 ≤ w*x + b to apply hM2
      dsimp [w, b] -- Apply the definition of w and b
      ring_nf -- Simplify
      field_simp -- Simplify
      nlinarith [hx, abs_nonneg M1, abs_nonneg M2, le_abs_self M2] -- Simplify

    specialize hM2 (w * x + b) h_bound -- Use hM2 to show that d(σ(w*x+b), 1) < ε
    rw [Real.dist_eq] at hM2 -- Use the definition of distance to show that |σ(w*x+b) - 1| < ε
    exact hM2
  done


-- Define ext_T to be the function t ↦ exp(t), where t ∈ T (This is the function we approximate by H_sigma)
noncomputable def ext_T : C(T, ℝ) := ⟨fun t => Real.exp t.1, Real.continuous_exp.comp continuous_subtype_val⟩


-- Any exponential function can be approximated by a function in H_sigma
-- We haven't been able to prove this result, as it relies on a very fiddely construction with step functions
--  1. We have shown that σ can approximate a step function on T (shown above).
--  2. Since exp is monotone, we can approximate it with a "staircase" of step functions.
--  3. We replace the sharp steps with the smooth sigmoids.
--  4. Since both exp and our approximation are monotone, we can bound the error in the transition regions
lemma exp_in_H_sigma (ε : ℝ) (hε : 0 < ε) :
    ∃ h ∈ H_sigma σ T, ‖h - ext_T‖ < ε := by
  sorry


-- ===============================================================
--   PART 6: Show F_sigma can approximate exp to arbitrary precision
--     · We want to show that our approximation for exp in H_sigma can be lifted to an element of F_sigma
--     · We do this by defining an affine map L : C(Ω, T) such that L(x) = w·x + b
--     · This will allow us to swap the exponential activation function with an approximation in H_sigma using the σ above
-- ===============================================================

-- If h ∈ H_sigma is a scalar approximation, and L(x) = w·x + b is an affine map in C(Ω, T), then h(L(x)) ∈ F_sigma
-- This does not require the compactness of T or Ω, but I have kept it here becasue of the order of the proof of UAT
lemma lift_H_sigma_to_F_sigma (L : C(Ω, T)) (hL : ∀ x, (L x : ℝ) = inner ℝ w x.1 + b) (h : C(T, ℝ)) (hH : h ∈ H_sigma σ T) :
    h.comp L ∈ F_sigma Ω σ hσ_cont := by

  -- We prove this by induction on the structure of h as it is in the span of H_sigma.
  induction hH using Submodule.span_induction

  -- Case 1: h is a single scalar neuron of the form σ(u·t + v)
  case mem h hh_gen =>
    obtain ⟨u, v, h_eq⟩ := hh_gen -- Extract the scalar weights and bias
    apply Submodule.subset_span -- h is in the span of the new neuron
    use (u • w), (u * b + v) -- Define the new neuron with the composed weights and bias: u(w⋅x + b) + v = (u⋅w)⋅x + (u⋅b + v)
    ext x -- Show it holds for every point x ∈ Ω
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, neuron] -- Apply the composition and neuron defintion
    rw [real_inner_smul_left] -- Factor the scalars out the inner product
    rw [h_eq] -- Use the fact that h = σ(u·t + v)
    simp only -- Simplify
    rw [hL x] -- Use the definition of L
    congr 1 -- σ(x) = σ(y) → x = y since σ is strictly increasing
    ring -- Ring isomorphism

  -- Case 2: h is the zero function
  case zero =>
    simp only [zero_comp, zero_mem]

  -- Case 3: h is the sum of two functions in H_sigma
  case add x y hx hy hx_in hy_in =>
    simp only [add_comp] -- Composition of addition is addition of the composition
    exact Submodule.add_mem _ hx_in hy_in -- H_sigma closed under addition

  -- Case 4: h is the scalar multiple of a function in H_sigma
  case smul r x hx hx_in =>
    simp only [smul_comp] -- Composition of scalar multiplication is scalar multiplication of the composition
    exact Submodule.smul_mem _ r hx_in -- H_sigma closed under scalar multiplication
  done


-- Any exponential neuron exp(w·x + b) can be approximated by functions in F_sigma
-- We use our exponential approximation lemma on the range of L(x) = w·x + b, i.e. T
lemma exp_neuron_approx_in_F_sigma
  (w : EuclideanSpace ℝ (Fin d)) (b : ℝ) (ε : ℝ) (hε : 0 < ε) :
  ∃ g ∈ F_sigma Ω σ hσ_cont, ‖g - neuron Ω Real.exp Real.continuous_exp w b‖ < ε := by

  -- 1. Define the affine map L(x) = w·x + b and its range T ⊆ ℝ compact
  let L : C(Ω, ℝ) := ⟨fun x => inner ℝ w x.1 + b, by fun_prop⟩
  let T : Set ℝ := Set.range L
  have hT_compact : IsCompact T := isCompact_range L.continuous

  -- Coerce the set T into compact space for the next lemma
  let T_subtype : Type := T
  have : CompactSpace T_subtype := isCompact_iff_compactSpace.mp hT_compact

  -- 2. Apply the 1D approximation assumption (exp_in_H_sigma) on T to get our approximator exp_approx ∈ H_sigma(T)
  obtain ⟨exp_approx, h_exp_approx_mem, h_exp_approx_dist⟩ := exp_in_H_sigma σ ε hε (T := T)

  -- 3. Lift exp_approx to G ∈ C(Ω, T), G(x) = exp_approx(w·x + b)
  let L_res : C(Ω, T) := ⟨fun x => ⟨L x, Set.mem_range_self x⟩, Continuous.subtype_mk L.continuous _⟩ -- L restricted to T
  let G : C(Ω, ℝ) := exp_approx.comp L_res

  -- 4. Show G is in F_sigma using the lifting lemma (we use L restricted to T, and h = exp_approx)
  have hG_mem : G ∈ F_sigma Ω σ hσ_cont :=
    lift_H_sigma_to_F_sigma Ω σ hσ_cont L_res (w := w) (b := b) (hL := by dsimp [L_res, L]; simp) (h := exp_approx) (hH := h_exp_approx_mem)

  use G, hG_mem -- We now want to show G approximates exp_neuron = exp(w·x + b)

  -- 5. Bound the error ‖G - exp_neuron‖_Ω ≤ ‖exp_approx - ext_T‖_K
  apply lt_of_le_of_lt _ h_exp_approx_dist -- Use that ‖exp_approx - ext_T‖ < ε
  rw [ContinuousMap.norm_le _ (by positivity)] -- Use that |f(x)| ≤ ‖f‖ for all x ∈ Ω
  intro x

  -- 6. We want to show |exp_approx(w·x + b) - exp(w·x + b)| = |exp_approx(L(x)) - exp(L(x))| = |exp_approx(t) - exp(t)| for t = L(x) ∈ T
  let t : T_subtype := ⟨L x, Set.mem_range_self x⟩ -- Define t = L(x) ∈ T
  calc ‖(G - neuron Ω Real.exp Real.continuous_exp w b) x‖ -- Use calc to show these equalities

    -- ‖(G - neuron Ω Real.exp Real.continuous_exp w b) x‖ = ‖exp_approx t - ext_T t‖
    _ = ‖exp_approx t - ext_T t‖ := by
      simp only [G, neuron, L_res, L, ContinuousMap.sub_apply, ContinuousMap.comp_apply] -- Apply the defintions and expand everything
      unfold ext_T -- Unfold the definition of ext_T
      rfl -- Show that the two sides are equal

    -- ‖exp_approx t - ext_T t‖ = ‖(exp_approx - ext_T) t‖ < ε
    _ = ‖(exp_approx - ext_T : C(T, ℝ)) t‖ := by
      simp only [ContinuousMap.sub_apply] -- Apply the subtraction definition

    -- ‖(exp_approx - ext_T) t‖ ≤ ‖exp_approx - ext_T‖
    _ ≤ ‖exp_approx - ext_T‖ := ContinuousMap.norm_coe_le_norm (exp_approx - ext_T) t -- Use that |f(x)| ≤ ‖f‖ for all x ∈ Ω
  done


-- ===============================================================
--   PART 7: The UAT for monotone continuous activation functions
--     · We have that closure(F_exp) = C(Ω, ℝ) from before
--     · We have that any exponential neuron is approiximated in F_sigma
--     · Thus any linear combination of exponential neurons is the linear combination of the approximations which is in F_sigma
--     · This implies that F_exp ⊆ Closure(F_sigma) so F_sigma is dense in F_exp and thus in C(Ω, ℝ) (UAT)
-- ===============================================================

-- Any function in the algebra of exponential neurons can be approximated by F_sigma
-- We use that an exponential neuron is approximated by F_sigma
-- Thus the linear combination of approximations of the exponential neurons is also in F_sigma
lemma F_exp_subset_closure_F_sigma :
(F_exp Ω : Set C(Ω, ℝ)) ⊆ (F_sigma Ω σ hσ_cont).topologicalClosure := by

  intro f hf -- Take an arbitrary function f ∈ F_exp.
  change f ∈ Submodule.span ℝ (SetOfNeurons Ω Real.exp Real.continuous_exp) at hf -- Use the definition of F_exp as a submodule

  -- We proceed by induction on f ∈ F_exp (p is the property that f is in the closure of F_sigma)
  -- We are essentially showing that any f ∈ F_exp is an element of the closure of F_sigma
  apply Submodule.span_induction (p := fun f _ => f ∈ (F_sigma Ω σ hσ_cont).topologicalClosure) (hx := hf)

  -- Case 1: f = exp(w·x + b) is a single exponential neuron
  · intros f hf
    change f ∈ closure ((F_sigma Ω σ hσ_cont) : Set C(Ω, ℝ)) -- Use closure of the set of elements of F_sigma
    rw [Metric.mem_closure_iff] -- Use the metric definition of closure (∀ ε > 0, ∃ b ∈ F_sigma, dist(f, b) < ε)
    intros ε hε -- Take an arbitrary ε > 0
    obtain ⟨w, b, rfl⟩ := hf -- Use the definition of f as an exponential neuron
    -- Use the approximation lemma we just proved to get an element g ∈ F_sigma that is close to f
    obtain ⟨g, hg_mem, hg_dist⟩ := exp_neuron_approx_in_F_sigma Ω σ hσ_cont (w := w) (b := b) ε hε
    use g, hg_mem -- Use g as the element in F_sigma that is close to f
    rw [dist_comm, dist_eq_norm] -- Use convert the metric to a norm
    exact hg_dist -- Use the fact that g approximates f (from the result of the above lemma)

  -- Case 2: f = 0
  · exact Submodule.zero_mem _ -- The zero function is in the closure of F_sigma

  -- Case 3: Addition
  · intros x y hx hy ihx ihy -- x, y are elements of F_exp that are in the closure of F_sigma
    exact Submodule.add_mem _ ihx ihy -- Submodule is closed under addition

  -- Case 4: Scalar multiplication
  · intros r x hx ih -- r is a scalar, x is an element of F_exp that is in the closure of F_sigma
    exact Submodule.smul_mem _ r ih -- Submodule is closed under scalar multiplication
  done


-- The Universal Approximation Theorem for monotone continuous activation functions
-- The result we want to show here is Closure(F_exp) ⊆ Closure(F_sigma)
-- Thus would give us C(Ω, ℝ) = ⊤ = Closure(F_exp) ⊆ Closure(F_sigma) ⊆ ⊤ so Closure(F_sigma) = ⊤
theorem monotone_UAT_top : Submodule.topologicalClosure (F_sigma Ω σ hσ_cont) = ⊤ := by
  apply SetLike.ext' -- Switch from Submodule equality to Set equality
  apply Set.eq_univ_of_forall -- Show every element of universe is in Closure(F_sigma)
  intro f -- Pick an arbitrary element f ∈ ⊤
  apply closure_minimal -- This lemma states that if A ⊆ B and B is closed, then Closure(A) ⊆ B
  apply F_exp_subset_closure_F_sigma Ω σ -- Use F_exp ⊆ Closure(F_sigma) (from above lemma)
  apply Submodule.isClosed_topologicalClosure -- Show Closure(F_sigma) is closed (Now we need to show that f is in Closure(F_exp))
  change f ∈ ((F_exp Ω).topologicalClosure : Set C(Ω, ℝ)) at ⊢ -- Switch from the set closure to topological closure of F_exp
  rw [F_exp_UAT_cont Ω] -- Use the fact that F_exp is dense in C(Ω, ℝ) (from part 4)
  simp only [mem_univ] -- Use the fact that f is trivially in C(Ω, ℝ)
  done


-- ε-δ version of the UAT for monotone continuous activation functions
-- Proof is exactly the same as the proof of F_exp_UAT from F_exp_UAT_top
theorem monotone_UAT (f : C(Ω, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ (F_sigma Ω σ hσ_cont), ‖g - f‖ < ε := by

  -- Since f is a continuous function, it is in the closure of F_sigma by UAT
  have hf_mem_closure : f ∈ (F_sigma Ω σ hσ_cont).topologicalClosure := by
    rw [monotone_UAT_top Ω σ]
    simp

  rw [← SetLike.mem_coe] at hf_mem_closure -- Convert to set
  change f ∈ closure ((F_sigma Ω σ hσ_cont) : Set C(Ω, ℝ)) at hf_mem_closure -- Convert to set closure
  rw [Metric.mem_closure_iff] at hf_mem_closure -- Use the metric characterization of closure
  obtain ⟨g, _, hf_dist⟩ := hf_mem_closure ε hε -- Obtain g ∈ F_sigma
  use g -- Need to show g ∈ F_sigma and ‖g - f‖ < ε
  constructor
  · finiteness -- Use g ∈ F_sigma
  · rw [dist_eq_norm, norm_sub_rev] at hf_dist -- Rewrite the distance statement as a norm
    exact hf_dist
  done

end UniversalApproximation
