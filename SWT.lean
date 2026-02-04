/- To Do List: -/
-- Redefine variables, assumptions and name spaces

/- Imports -/
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.ContinuousMap.Weierstrass

/- Linters -/
-- set_option diagnostics true
-- set_option linter.unusedSectionVars false
set_option linter.unusedTactic false -- Clears done warnings

namespace SWT
open ContinuousMap Set

-- ===============================================================
--   PART 1: Real Number Identities
-- ===============================================================

/- Proof of max(x, y) = (x + y + |x - y|) / 2 for x, y ∈ ℝ -/
lemma max_id_abs (x y : ℝ) : max x y = 1/2 * (x + y + |x - y|) := by
  cases le_total x y with -- Split into cases based cases: either x ≤ y or y ≤ x.
  | inl leq => -- Case 1: x ≤ y
    rw[max_eq_right leq] -- max(x, y) = y
    rw [abs_of_nonpos (sub_nonpos_of_le leq)] -- |x - y| = -(x - y) = y - x
    ring -- Verify: y = 1/2 * (x + y + (y - x)) → y = 1/2 * 2y → y = y
  | inr geq => -- Case 2: y ≤ x
    rw[max_eq_left geq] -- max(x, y) = x
    rw [abs_of_nonneg (sub_nonneg_of_le geq)] -- |x - y| = x - y
    ring -- Verify: x = 1/2 * (x + y + (x - y)) → x = 1/2 * 2x → x = x
  done

/- Proof of min(x, y) = (x + y - |x - y|) / 2 for x, y ∈ ℝ -/
lemma min_id_abs (x y : ℝ) : min x y = 1/2 * (x + y - |x - y|) := by
  cases le_total x y with -- Split into cases based cases: either x ≤ y or y ≤ x.
  | inl leq => -- Case 1: x ≤ y
    rw[min_eq_left leq] -- min(x, y) = x
    rw [abs_of_nonpos (sub_nonpos_of_le leq)] -- |x - y| = y - x
    ring -- Verify: x = 1/2 * (x + y - (y - x)) → x = 1/2 * 2x
  | inr geq => -- Case 2: y ≤ x
    rw[min_eq_right geq] -- min(x, y) = y
    rw [abs_of_nonneg (sub_nonneg_of_le geq)] -- |x - y| = x - y
    ring -- Verify: y = 1/2 * (x + y - (x - y)) → y = 1/2 * 2y
  done

-- ===============================================================
--   PART 2: Function Lattice Operations
-- ===============================================================

variable {Ω : Type*} [TopologicalSpace Ω]

/- Proof of pointwise Max identity with absolute value for Functions -/
lemma max_id_abs_func (f g : C(Ω, ℝ)) : f ⊔ g = (1/2 : ℝ) • (f + g + |f - g|) := by
  ext x -- Two functions are equal if they agree at all points x (extensionality)
  rw [@smul_apply, sup_apply] -- Definition of scalar mult and sup for functions.
  rw [max_id_abs] -- Apply the lemma we just proved for reals.
  simp
  done

/- Proof of pointwise Min identity with absolute value for Functions -/
lemma min_id_abs_func (f g : C(Ω, ℝ)) : f ⊓ g = (1/2 : ℝ) • (f + g - |f - g|) := by
  ext x -- Two functions are equal if they agree at all points x (extensionality)
  rw [@smul_apply, inf_apply] -- Definition of scalar mult and inf for functions.
  rw [min_id_abs] -- Apply the lemma we just proved for reals.
  simp
  done

-- ===============================================================
--   PART 3: Subalgebra Properties
-- ===============================================================

variable {A : Subalgebra ℝ C(Ω, ℝ)} -- (Note that this is a unital subalgebra)

/- For a polynomial p and a function f ∈ A, p ∘ f = p(f) ∈ A -/
lemma polynomial_comp_mem_subalg (p : Polynomial ℝ) (f : C(Ω, ℝ)) (hf : f ∈ A) :
    (p.toContinuousMap.comp f) ∈ A := by

  -- 1. Express the composition polynomial ∘ continuous_map as the algebraic evaluation of p at f.
  -- This allows us to use ring properties of the algebra A.
  have h_eq : p.toContinuousMap.comp f = Polynomial.aeval f p := by
    ext x -- To show two functions are equal, we show they agree at every point x.
    simp -- Simplifies the definitions of polynomial evaluation and composition.
  rw [h_eq]

  -- 2. We proceed by induction on the structure of the polynomial p.
  -- A polynomial is built from constants (C r), variable (X), addition, and multiplication.
  induction p using Polynomial.induction_on with
  -- Base case: p is a constant polynomial C r.
  | C r =>
    -- The evaluation of a constant polynomial is a constant function.
    -- Since A is a unital subalgebra, it contains all constant functions (scalar multiples of 1).
    simp only [Polynomial.aeval_C, algebraMap_mem]
  -- Induction step: Monomials / Scaling.
  -- If property holds for p, we show it holds for p * X (conceptually similar to induction on degree or monomials).
  | monomial p hp =>
    -- The evaluation separates into multiplication and powers.
    -- Since A is a subalgebra, it is closed under multiplication (map_mul) and scalar multiplication.
    simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    -- The term is a product of a constant and a power of f.
    -- f ∈ A implies f^n ∈ A (multiplicative closure).
    -- c • (f^n) ∈ A (scalar closure).
    finiteness
  -- Induction step: Addition.
  -- If property holds for p and q, we show it holds for p + q.
  | add p q hp hq =>
    -- The map is additive: (p+q)(f) = p(f) + q(f).
    simp only [map_add]
    -- Since A is a subspace, it is closed under addition.
    -- hp says p(f) ∈ A, hq says q(f) ∈ A, so p(f) + q(f) ∈ A.
    bound
  done

/- Proof that there exists a function in the Subalgebra that matches any function at 2 points -/
-- Note that the assumption that A separates points implies that Ω is Hausdorff.
lemma exists_mem_subalg_interp_two {f : C(Ω, ℝ)} (hA : A.SeparatesPoints) :
    ∀ x y : Ω, x ≠ y → ∃ g ∈ A, (g x = f x) ∧ (g y = f y) := by

  intro x y hxy -- Fix distinct points x, y.

  -- 1. Use the separation property to get a function h ∈ A where h(x) ≠ h(y).
  obtain ⟨h_fun, h_in_fun_A, h_sep⟩ := hA hxy -- h_fun is the function h ∈ A, as a map in C(Ω, ℝ)
  obtain ⟨h, h_mem, h_eq⟩ := h_in_fun_A
  rw [← h_eq] at h_sep -- h(x) ≠ h(y).

  -- 2. We want g(x) = f(x) and g(y) = f(y), so construct g = a * (h - h(y)) + b * (h - h(x)), where:
  let a := f x / (h x - h y) -- Cancels the term at y (since h(y) - h(y) = 0) meaning g(x) = f(x)
  let b := f y / (h y - h x) -- Cancels the term at x (since h(x) - h(x) = 0) meaning g(y) = f(y)
  use a • (h - ContinuousMap.C (h y)) + b • (h - ContinuousMap.C (h x))

  -- 3. Show g ∈ A.
  constructor
  -- Use that A is a subalgebra, so it's closed under:
  -- 1. Constants (algebraMap_mem)
  -- 2. Subtraction/Addition (sub_mem, add_mem)
  -- 3. Scalar multiplication (smul_mem)
  · apply A.add_mem
    · apply A.smul_mem
      apply A.sub_mem
      · exact h_mem -- h ∈ A
      · apply A.algebraMap_mem -- Constant h(y) ∈ A
    · apply A.smul_mem
      apply A.sub_mem
      · exact h_mem
      · apply A.algebraMap_mem -- Constant h(x) ∈ A

  -- 4. Verify values at x and y.
  · constructor
    -- At x: The second term vanishes (h(x) - h(x) = 0), the first term becomes a * (h(x) - h(y)) = f(x).
    · simp [a, b, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.C_apply]
      have h_diff : h x - h y ≠ 0 := sub_ne_zero.mpr h_sep-- Avoid zero division
      field
    -- At y: The first term vanishes (h(y) - h(y) = 0), the second term becomes b * (h(y) - h(x)) = f(y).
    · simp [a, b, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.C_apply]
      have h_diff : h y - h x ≠ 0 := sub_ne_zero.mpr (Ne.symm h_sep) -- Avoid zero division
      field
  done

-- ===============================================================
--   PART 4: Absolute Value Approximation in the subalgebra A
-- ===============================================================

variable [CompactSpace Ω]
variable (hA_closed : IsClosed (A : Set C(Ω, ℝ)))

/- Proof that pointwise absolute value of a function can be arbitrarily approximated in the subalgebra-/
lemma exists_approx_abs (ε : ℝ) (hε : 0 < ε) (f : C(Ω, ℝ)) (hf : f ∈ A) :
    ∃ a ∈ A, ‖a - |f|‖ < ε := by

  -- 1. Bounding: Find a compact interval K = [-M, M] that contains the range of f.
  let M := ‖f‖
  let K := Icc (-M) M
  have h_range : MapsTo f univ K := by -- Prove that f maps all of Ω into K.
    intro x _
    rw [mem_Icc, ← @abs_le] -- The condition y ∈ [-M, M] is equivalent to |y| ≤ M.
    exact norm_coe_le_norm f x -- |f(x)| ≤ ‖f‖ by definition of uniform norm.

  -- 2. Define g(y) = |y| restricted to the interval K, on which it is continuous.
  let g : C(K, ℝ) := ⟨fun y => |(y : ℝ)|, continuous_abs.comp continuous_subtype_val⟩

  -- 3. Approximation: Apply the Weierstrass Approximation Theorem (for intervals).
  -- Since g is continuous on the compact interval K, there exists a polynomial p such that p is within ε of g on K.
  have Weierstrass : ∃ (p : Polynomial ℝ), ‖p.toContinuousMapOn K - g‖ < ε := by
    apply exists_polynomial_near_continuousMap
    exact hε
  obtain ⟨p, hp⟩ := Weierstrass -- Extract the polynomial p.

  -- 4. Construct our candidate a = p(f) and show its satisfies the goal.
  use p.toContinuousMap.comp f
  constructor
  -- Show that a ∈ A by the previous lemma
  · apply polynomial_comp_mem_subalg
    apply hf
  -- Show that ‖a - |f|‖ < ε.
  · rw [ContinuousMap.norm_lt_iff _ hε] at hp ⊢ -- Show that the functions agree at every point in hp and goal
    intro x -- Take an arbitrary point x ∈ Ω.
    -- We need to show ‖p(f(x)) - |f(x)|‖ < ε.
    specialize hp ⟨f x, h_range (Set.mem_univ x)⟩ -- The Weierstrass estimate hp holds for all y ∈ K.
    exact hp -- Since f(x) is in K, the estimate applies directly.
  done


/- Proof that a Subalgebra is topologically closed under pointwise absolute value -/
lemma abs_mem_closed_subalg (f : C(Ω, ℝ)) (hf : f ∈ A) (hA : IsClosed (A : Set C(Ω, ℝ))):
    |f| ∈ A := by

  -- 1. Show its equivalent to there being an a ∈ A such that dist(a, |f|) < ε
  rw [← SetLike.mem_coe, ← hA.closure_eq] -- A = closure A
  rw [Metric.mem_closure_iff] -- |f| ∈ closure A ↔ ∀ ε > 0, ∃ a ∈ A, dist(a, |f|) < ε
  intro ε hε

  -- 2. Apply the previous lemma to get the a ∈ A approximating |f| within ε.
  obtain ⟨a, ha, ha_dist⟩ := exists_approx_abs ε hε f hf
  use a

  constructor
  -- Show that a ∈ A
  · exact ha
  -- Show that dist(a, |f|) < ε
  · rw [dist_eq_norm, ← neg_sub a |f|, norm_neg] -- dist(a, |f|) = ‖a - |f|‖
    exact ha_dist -- Use that a satisfies this property from the previous lemma
  done


-- ===============================================================
--   PART 5: Closure under pointwise maximum and minimum
-- ===============================================================

/- Proof that a Subalgebra is topologically closed under pointwise maximum, i.e. ∀f,g ∈ A, max(f,g) ∈ A -/
lemma sup_mem_of_closed_subalg (f g : A) (hA : IsClosed (A : Set C(Ω, ℝ))) :
    (f : C(Ω, ℝ)) ⊔ (g : C(Ω, ℝ)) ∈ A := by

  -- 1. Use the identity: max(f, g) = 1/2 * (f + g + |f - g|)
  rw [max_id_abs_func]

  -- 2. Show that every component of the RHS is in A.
  simp only [one_div, smul_add]
  apply A.add_mem -- A is closed under addition
  · apply A.add_mem
    · apply A.smul_mem -- A is closed under scalar multiplication
      apply SetLike.coe_mem -- f ∈ A
    · apply A.smul_mem
      apply SetLike.coe_mem -- g ∈ A
  · apply A.smul_mem
    apply abs_mem_closed_subalg -- Use |f - g| ∈ A (previous lemma)
    · apply A.sub_mem -- A is closed under subtraction
      · apply SetLike.coe_mem
      · apply SetLike.coe_mem
    · apply hA -- Requires A to be topologically closed
  done


/- Proof that a Subalgebra is topologically closed under pointwise minimum -/
lemma inf_mem_of_closed_subalg (f g : A) (hA : IsClosed (A : Set C(Ω, ℝ))) :
    (f : C(Ω, ℝ)) ⊓ (g : C(Ω, ℝ)) ∈ A := by

  -- 1. Use the identity: min(f, g) = 1/2 * (f + g - |f - g|)
  rw [min_id_abs_func]

  -- 2. Show that every component of the RHS is in A.
  simp only [one_div, smul_add, smul_sub]
  apply A.sub_mem -- A is closed under subtraction
  · apply A.add_mem -- A is closed under addition
    · apply A.smul_mem -- A is closed under scalar multiplication
      apply SetLike.coe_mem -- f ∈ A
    · apply A.smul_mem
      apply SetLike.coe_mem -- g ∈ A
  · apply A.smul_mem
    apply abs_mem_closed_subalg -- Use |f - g| ∈ A (previous lemma)
    · apply A.sub_mem -- A is closed under subtraction
      · apply SetLike.coe_mem
      · apply SetLike.coe_mem
    · apply hA -- Requires A to be topologically closed
  done


/- Proof that a Subalgebra is closed under finite pointwise maximum -/
-- S is a finite, non-empty set of indicies
-- i ∈ S is an index
-- F(i) is an element of the subalgebra A (an indexed countinuous function)
-- We want to show that the pointwise maximum of a collection of functions F_i ∈ A is in A.
-- We use sup' which also requires a proof that the set is nonempty (which we have)
lemma finset_sup_mem_of_closed_subalg {ι : Type*} [DecidableEq ι] (s : Finset ι) (h_nonempty : s.Nonempty)
    (F : ι → C(Ω, ℝ)) (hF : ∀ i ∈ s, F i ∈ A) (hA : IsClosed (A : Set C(Ω, ℝ))) :
    (s.sup' h_nonempty F) ∈ A := by
  -- We prove by induction that the max of a finite set of functions in A is in A.
  induction s using Finset.induction_on with
  | empty => simp at h_nonempty -- Base case: empty set is impossible (Nonempty requirement)
  -- We assume it holds for s, and prove it holds for s ∪ {a}.
  | insert a s ha ih => -- "insert" is the insertion of a ∉ s, into s ∪ {a} (nonempty)
    rcases s.eq_empty_or_nonempty with rfl | h_s_ne
    · -- Case: {a}, i.e. sup(F_a) = F_a ∈ A by hypothesis.
      simp only [insert_empty_eq, Finset.sup'_singleton]
      exact hF a (Finset.mem_singleton_self a)

    · -- Case: {a} ∪ s, i.e. sup({a} ∪ s) → sup(F_a, sup(F_s)) ∈ A by pairwise max lemma.
      rw [Finset.sup'_insert h_s_ne] -- Now s is nonempty

      -- Head f is F_a as an element of A
      let f_head : A := ⟨F a, hF a (Finset.mem_insert_self a s)⟩

      -- Tail f is sup(F_i_1, ..., F_i_n) ∈ A by inductive hypothesis
      let f_tail : A := ⟨s.sup' h_s_ne F, ih h_s_ne (λ i hi => hF i (Finset.mem_insert_of_mem hi))⟩

      exact sup_mem_of_closed_subalg f_head f_tail hA -- Apply pairwise sup lemma above
  done


/- Proof that a Subalgebra is closed under finite pointwise minimum -/
-- S is a finite, non-empty set of indicies
-- i ∈ S is an index
-- F(i) is an element of the subalgebra A (an indexed countinuous function)
-- We want to show that the pointwise minimum of a collection of functions F_i ∈ A is in A.
-- We use inf' which also requires a proof that the set is nonempty (which we have)
lemma finset_inf_mem_of_closed_subalg {ι : Type*} [DecidableEq ι] (s : Finset ι) (h_nonempty : s.Nonempty)
    (F : ι → C(Ω, ℝ)) (hF : ∀ i ∈ s, F i ∈ A) (hA : IsClosed (A : Set C(Ω, ℝ))) :
    (s.inf' h_nonempty F) ∈ A := by
  -- Induction for finite infimum. Same logic as supremum.
  induction s using Finset.induction_on with
  | empty => simp at h_nonempty -- Base case: empty set is impossible (Nonempty requirement)
  -- We assume it holds for s, and prove it holds for s ∪ {a}.
  | insert a s ha ih => -- "insert" is the insertion of a ∉ s, into s ∪ {a} (nonempty)
    rcases s.eq_empty_or_nonempty with rfl | h_s_ne
    · -- Case: {a}, i.e. inf(F_a) = F_a ∈ A by hypothesis.
      simp only [insert_empty_eq, Finset.inf'_singleton]
      exact hF a (Finset.mem_singleton_self a)

    · -- Case: {a} ∪ s, i.e. inf({a} ∪ s) → inf(F_a, inf(F_s)) ∈ A by pairwise max lemma.
      rw [Finset.inf'_insert h_s_ne]

      -- Head f is F_a as an element of A
      let f_head : A := ⟨F a, hF a (Finset.mem_insert_self a s)⟩

      -- Tail f is inf(F_i_1, ..., F_i_n) ∈ A by inductive hypothesis
      let f_tail : A := ⟨s.inf' h_s_ne F, ih h_s_ne (λ i hi => hF i (Finset.mem_insert_of_mem hi))⟩

      exact inf_mem_of_closed_subalg f_head f_tail hA -- Apply pairwise inf lemma above
  done


-- ===============================================================
--   PART 6: Seperation of points under Topological Closure
-- ===============================================================

/- Proof that if the Subalgebra separates points, then so does its Topological Closure -/
lemma separatesPoints_subalg_closure (h_sep : A.SeparatesPoints) :
    A.topologicalClosure.SeparatesPoints := by -- i.e. ∀ x ≠ y, ∃ f ∈ Closure(A) such that f(x) ≠ f(y).

  -- 1. Pick an f ∈ A that separates x and y.
  intro x y h_neq
  obtain ⟨f, hf_in_A, hf_sep⟩ := h_sep h_neq -- Since A separates points, there is some f ∈ A such that f(x) ≠ f(y).
  use f -- We use that function f ∈ A, as an element of Closure(A).

  -- 2. Show f ∈ Closure(A) and f separates x, y.
  constructor
  · -- f ∈ A implies f ∈ Closure(A) by definition.
    apply Set.image_mono A.le_topologicalClosure
    exact hf_in_A
  · -- f separates x and y by assumption.
    exact hf_sep
  done


-- ===============================================================
--   PART 7: Local Upper Bound Construction for f ∈ C(Ω, ℝ)
-- ===============================================================

/- Local Upper Bound construction -/
-- For a given function f ∈ C(Ω, ℝ) and a point x ∈ Ω, we want to find a function g ∈ A
-- that is bounded below by f - ε on Ω, and that f(x) = g(x).
lemma exists_mem_local_upper_bound (f : C(Ω, ℝ)) (x : Ω) (ε : ℝ) (hε : 0 < ε)
    (hA_sep : A.SeparatesPoints) (hA_closed : IsClosed (A : Set C(Ω, ℝ))) :
    ∃ g ∈ A, (g x = f x) ∧ (∀ z, f z - ε < g z) := by
  -- 1. Prove that for any target point y ∈ Ω, there exists a function g ∈ A that matches f at x and y.
  have h_exists : ∀ y : Ω, ∃ g ∈ A, (g x = f x) ∧ (g y = f y) := by
    intro y
    by_cases hxy : x = y -- Either x = y or x ≠ y
    · -- Case 1: x = y. Use the constant function g = f(x) ∈ A as A is unital
      rw [← hxy] -- Use that x = y
      use algebraMap ℝ C(Ω, ℝ) (f x) -- Use the constant function g = f(x)
      simp only [algebraMap_mem, algebraMap_apply, smul_eq_mul, mul_one, and_self]
    · -- Case 2: x ≠ y. Use the 2-point interpolation lemma from above
      obtain ⟨g, hg_in, hg_eq⟩ := exists_mem_subalg_interp_two hA_sep x y hxy
      use g -- Use the g found above

  -- 2. Axiom of Choice: Select one such function G_y for each y ∈ Ω.
  -- G_y is a function in A such that G_y(x) = f(x) and G_y(y) = f(y).
  choose G hG_in hG_vals using h_exists

  -- 3. Open Cover Construction
  -- For each y, define open set U_y where G_y(z) > f(z) - ε.
  -- This y ∈ U_y because G_y(y) = f(y) > f(y) - ε.
  let U := λ y => {z | f z - ε < (G y) z} -- These are the open sets

  -- 4. Verify Cover Ω ⊆ ⋃_y U (i.e. Ω is covered by the collection of open sets {U_y})
  have h_cover : univ ⊆ ⋃ y, U y := by
    intro z hz -- Show that any z ∈ Ω is in the union
    rw [mem_iUnion] -- Show that there is always a U that contains z
    use z -- z is covered by U_z
    simp only [mem_setOf_eq, U] -- Use the definition of U
    rw [(hG_vals z).2] -- G_z(z) = f(z)
    linarith -- f(z) > f(z) - ε holds since ε > 0.

  -- 5. Compactness Argument
  -- U_y is open because G_y and f are continuous.
  have h_open : ∀ y, IsOpen (U y) := λ y => isOpen_lt (f.continuous.sub continuous_const) (G y).continuous
  -- Extract a finite subcover U_{y_1}, ..., U_{y_n} of Ω, since Ω is compact.
  obtain ⟨s, hs_cover⟩ := isCompact_univ.elim_finite_subcover U h_open h_cover

  -- 6. Non-empty Cover
  -- Just to satisfy technical requirements of sup'.
  have hs_nonempty : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    by_contra h_empty -- Proof by contradiction that s is non-empty
    rw [h_empty] at hs_cover -- If s is empty, then the union is empty
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty] at hs_cover -- Convert the sattement to Ω ⊆ ∅
    exact Set.notMem_empty x (hs_cover (mem_univ x)) -- But Ω is not empty, so we have a contradiction

  -- Enable decidable equality for Finset operations
  -- This is required for the use of Finset.sup' and other Finset operations
  -- This allows us to check whether elements are unique, with law of excluded middle
  -- (Not entirely sure how this works but the LEAN infoView hinted that it was needed)
  letI : DecidableEq Ω := Classical.decEq Ω

  -- 7. Construct g_x
  -- Define g_x as the pointwise maximum of the finite family of functions {G_y | y ∈ s}.
  let g_x := s.sup' hs_nonempty G
  use g_x

  -- Having constructed our candidate g_x, we now have to show three things:
  -- 1. g_x ∈ A
  -- 2. g_x(x) = f(x)
  -- 3. g_x(z) > f(z) - ε for all z ∈ Ω

  constructor
  -- Proof g_x ∈ A.
  -- A is closed under finite maxima as shown above.
  · apply finset_sup_mem_of_closed_subalg s hs_nonempty G _ hA_closed
    intro y hy
    exact hG_in y

  constructor
  -- Proof g_x(x) = f(x).
  -- Every function in the max, G(y), takes value f(x) at x.
  -- So max(f(x), f(x), ...) = f(x).
  · dsimp [g_x] -- Apply the definition of g_x
    rw [sup'_apply hs_nonempty G x] -- Prove that (sup' G)(x) = sup' (G(x)).
    apply Finset.sup'_eq_of_forall -- Equivalence to the fact that G_y(x) = f(x) for all y
    intro y hy
    rw [(hG_vals y).1] -- Use that G_y(x) = f(x)

  -- Proof g_x(z) > f(z) - ε for all z.
  -- Since U_y covers Ω, for any z, there is some y ∈ s such that z ∈ U_y.
  -- z ∈ U_y implies G(y)(z) > f(z) - ε.
  -- g_x(z) is the max, so g_x(z) ≥ G(y)(z) > f(z) - ε.
  · intro z
    dsimp [g_x] -- Apply the definition of g_x
    rw [sup'_apply hs_nonempty G z] -- Prove that (sup' G)(z) = sup' (G(z)).
    have hz : z ∈ ⋃ y ∈ s, U y := hs_cover (mem_univ z) -- z is in the union of U_y for y ∈ s as its a cover of Ω
    rw [mem_iUnion₂] at hz -- Rewrite the statement to show that z is in U_y for some y
    obtain ⟨y, hy_s, hy_U⟩ := hz -- Extract y such that z ∈ U_y
    apply lt_of_lt_of_le hy_U -- Apply the inequality G(y)(z) > f(z) - ε
    apply Finset.le_sup' (fun i => G i z) hy_s -- Apply the fact that g_x(z) is the max
  done

-- ===============================================================
--   PART 8: Global Approximation / Stone Weierstrass Theorem
-- ===============================================================

/- Global Approximation construction -/
-- For a given function f ∈ C(Ω, ℝ) and ε > 0,
-- There exists a g ∈ A such that ‖g - f‖ < ε.
-- This is the a version of Stone Weierstrass Theorem.
-- This proof is very similar to above, but working with g(z) < f(z) + ε, and infima
lemma exists_mem_global_approx (f : C(Ω, ℝ)) (ε : ℝ) (hε : 0 < ε)
    (hA_sep : A.SeparatesPoints) (hA_closed : IsClosed (A : Set C(Ω, ℝ))) :
    ∃ g ∈ A, ‖g - f‖ < ε := by

  -- Either Ω is empty or non-empty.
  cases isEmpty_or_nonempty Ω with
  -- Edge case: Ω is empty. This is kind of a weird case where f is defined on an empty space.
  -- We have to have this to chose an x ∈ Ω later
  | inl h_empty => -- Have to prove ∃ g ∈ A, where ‖g - f‖ < ε.
    use 0 -- Use the zero function.
    constructor
    · exact A.zero_mem -- Zero is in A as its a closed subalgebra.
    · have h0 : ‖(0 : C(Ω, ℝ)) - f‖ = 0 := by -- Prove that the norm of the difference is 0
        rw [norm_eq_zero] -- ‖x‖ = 0 iff x = 0.
        simp only [zero_sub, neg_eq_zero]
        exact Subsingleton.eq_zero f -- Not too sure how this works but LEAN found it
      rw [h0]
      exact hε

  -- Normal case: Ω is non-empty.
  | inr h_nonempty =>
    -- 1. Construct local upper bounds for each x.
    -- From previous lemma ∀x, ∃ g_x ∈ A such that g_x(x) = f(x) and ∀z, g_x(z) > f(z) - ε
    have h_local_exists : ∀ x : Ω, ∃ g_x ∈ A, (g_x x = f x) ∧ (∀ z, f z - ε < g_x z) := by
      intro x
      exact exists_mem_local_upper_bound f x ε hε hA_sep hA_closed -- Apply the previous lemma

    -- 2. Choice: Select this family of functions G(x) for each x.
    choose G hG_in hG_vals using h_local_exists -- Obtain this family of functions

    -- 3. Open Cover Construction (Upper Bound)
    -- We want to force the upper bound g(z) < f(z) + ε.
    -- For fixed x, since G_x(x) = f(x) < f(x) + ε, by continuity, there is a neighborhood V_x where G_x(z) < f(z) + ε.
    let V := λ x => {z | (G x) z < f z + ε} -- These are the open sets

    -- 4. Verify Cover Ω ⊆ ⋃_x V (i.e. Ω is covered by the collection of open sets {V_x})
    -- (Like in the above lemma)
    have h_cover : univ ⊆ ⋃ x, V x := by
      intro z hz -- Show that any z ∈ Ω is in the union
      rw [mem_iUnion] -- Show that there is always a V that contains z
      use z -- z is covered by V_z
      simp only [mem_setOf_eq, V] -- Use the definition of V
      rw [(hG_vals z).1] -- G_z(z) = f(z)
      linarith -- f(z) < f(z) + ε holds since ε > 0.

    -- 5. Compactness Argument (Like in the above lemma)
    -- V_x is open because G_x and f are continuous.
    have h_open : ∀ x, IsOpen (V x) := λ x => isOpen_lt (G x).continuous (f.continuous.add continuous_const)
    -- Extract a finite subcover V_{x_1}, ..., V_{x_m} of Ω, since Ω is compact.
    obtain ⟨s, hs_cover⟩ := isCompact_univ.elim_finite_subcover V h_open h_cover

    -- 6. Non-empty check (As above)
    -- Just to satisfy technical requirements of sup'.
    have hs_nonempty : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      by_contra h_empty -- Proof by contradiction that s is non-empty
      rw [h_empty] at hs_cover -- If s is empty, then the union is empty
      simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty] at hs_cover -- Convert the sattement to Ω ⊆ ∅
      obtain ⟨x⟩ := h_nonempty -- Ω is not empty as assumed (This is where we pick an x)
      exact Set.notMem_empty x (hs_cover (mem_univ x)) -- We have a contradiction


    -- Enable decidable equality for Finset operations
    -- (Again, not entirely sure how this works)
    letI : DecidableEq Ω := Classical.decEq Ω

    -- 7. Construct g
    -- Define g as the pointwise minimum of the finite family of functions {G_x | x ∈ s}.
    let g := s.inf' hs_nonempty G
    use g

    -- Having constructed g, we now have to show two things:
    -- 1. g ∈ A
    -- 2. ‖g - f‖ < ε
    constructor
    -- Proof g ∈ A (closed under finite min).
    · apply finset_inf_mem_of_closed_subalg s hs_nonempty G _ hA_closed -- Apply the finite minima lemma from above
      -- Show that each G_x is in A
      intro x hx -- Select x in s
      exact hG_in x -- Use that G_x is in A

    -- Proof ‖g - f‖ < ε
    · rw [ContinuousMap.norm_lt_iff _ hε] -- We show that the inequality holds for all z ∈ Ω
      intro z
      dsimp [g] -- Apply the definition of g, being the infimum of G_x
      rw [inf'_apply]
      rw [abs_lt] -- Convert the norm to being - ε < g(z) - f(z) and g(z) - f(z) < ε (With g(z) = inf G_x(z))

      -- Show each of these inequalities seperately
      constructor
      -- Lower Bound: - ε < g(z) - f(z)
      -- For every x, G_x(z) - f(z) > -ε (from Step 1).
      -- So their min is also > f(z) - ε.
      · rw [lt_sub_iff_add_lt] -- Convert to -ε < g(z) - f(z)
        rw [Finset.lt_inf'_iff] -- Convert it to -ε < G_x(z) - f(z) for all x
        intro x hx
        rw [add_comm, ← sub_eq_add_neg] -- Convert it to f(z) - ε < G_x(z)
        exact (hG_vals x).2 z -- Apply the result from the previous lemma

      -- Upper Bound: g(z) - f(z) < ε.
      -- g(z) is the min. We just need inf G_x(z) < f(z) + ε.
      -- Since V covers Ω, z is in some V_x.
      -- By definition of V, inf G_x(z) ≤ G_x(z) < f(z) + ε.
      · have hz : z ∈ ⋃ x ∈ s, V x := hs_cover (mem_univ z) -- Use the cover property that z is in the union
        rw [mem_iUnion₂] at hz -- Therfore z is in some V_x
        obtain ⟨x, hx_s, hx_V⟩ := hz -- Extract x from the union
        rw [sub_lt_iff_lt_add, add_comm] -- Convert to inf G_x(z) < f(z) + ε
        apply lt_of_le_of_lt _ hx_V -- inf G_x(z) ≤ G_x(z) < f(z) + ε (Left to prove inf G_x(z) ≤ G_x(z))
        apply Finset.inf'_le _ hx_s -- Use that inf G_x(z) ≤ G_x(z)
  done


/- The Stone-Weierstrass Theorem -/
-- Note that the assumption that A separates points implied that Ω is Hausdorff.
-- Here we use the above lemma to show that A is dense in C(Ω, ℝ), i.e Closure(A) = C(Ω, ℝ).
theorem SWT_top (h_sep : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ := by
    -- 1. Let B be the topological closure of A
  let B := A.topologicalClosure

  -- 2. B is closed and separates points
  have hB_closed : IsClosed (B : Set C(Ω, ℝ)) := Subalgebra.isClosed_topologicalClosure A -- By def of topologicalClosure
  have hB_sep : B.SeparatesPoints := separatesPoints_subalg_closure h_sep -- By above lemma

  -- 3. Show B = ⊤, i.e. C(Ω, ℝ)
  -- We show that for all f ∈ ⊤ = C(Ω, ℝ), we have f ∈ B
  rw [eq_top_iff] -- Closure(B) = C(Ω, ℝ) ↔ C(Ω, ℝ) ⊆ Closure(B) as B is trivially less than ⊤
  intro f hf -- f is an arbitrary function in ⊤ = C(Ω, ℝ)
  rw [← SetLike.mem_coe, ← hB_closed.closure_eq, Metric.mem_closure_iff] -- f ∈ B ↔ ∀ ε > 0, ∃ g ∈ B, d(f, g) < ε
  intro ε hε -- Obtain the assumptions about ε

  -- 4. Apply our Global Approximation Lemma to B, i.e. that it can arbitrarily approximate any f ∈ C(Ω, ℝ)
  obtain ⟨g, hg_in, hg_dist⟩ := exists_mem_global_approx f ε hε hB_sep hB_closed
  use g -- Use the g we found in the previous lemma

  -- We now have to show that g ∈ B and that d(f, g) < ε
  constructor
  · exact hg_in -- g ∈ B (From previous lemma)
  · rw [dist_eq_norm, norm_sub_rev] -- d(f, g) = ‖g - f‖
    exact hg_dist -- Use the conclusion from the previous lemma
  done

-- Proof that ⊤ = C(Ω, ℝ) as above (i.e. the top of the lattice is C(Ω, ℝ))
example : ((⊤ : Subalgebra ℝ C(Ω, ℝ)) : Set C(Ω, ℝ)) = Set.univ := rfl

-- Proof that the closure of A is C(Ω, ℝ)
lemma SWT_cont (h_sep : A.SeparatesPoints) : (A.topologicalClosure : Set C(Ω, ℝ)) = Set.univ := by
  rw [SWT_top h_sep]
  rfl
  done

end SWT
