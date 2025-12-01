/- Imports -/
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.ContinuousMap.Weierstrass

/- Variable declaration (to be changed to remove extra assumptions)-/
variable {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
variable {A : Subalgebra ℝ C(Ω, ℝ)}
variable (hA_closed : IsClosed (A : Set C(Ω, ℝ)))

/- Linters -/
set_option diagnostics true
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

open ContinuousMap Set
namespace SWT

/- For a polynomial p and a function f ∈ A, p ∘ f ∈ A -/
lemma polynomial_comp_mem_subalg (p : Polynomial ℝ) (f : C(Ω, ℝ)) (hf : f ∈ A) :
    (p.toContinuousMap.comp f) ∈ A := by
  have h_eq : p.toContinuousMap.comp f = Polynomial.aeval f p := by
    ext x
    simp

  rw [h_eq]

  induction p using Polynomial.induction_on with
  | C r =>
    simp
  | monomial p hp =>
    simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    finiteness
  | add p q hp hq =>
    simp only [map_add]
    bound

  done


/- Proof that pointwise absolute value of a function can be arbitrarily approximated in the subalgebra-/
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

/- Proof that a Subalgebra is topologically closed under pointwise absolute value -/
lemma abs_mem_subalg (f : C(Ω, ℝ)) (hf : f ∈ A) (hA : IsClosed (A : Set C(Ω, ℝ))):
    |f| ∈ A := by
  rw [← SetLike.mem_coe]
  rw [← hA.closure_eq]
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a, ha, ha_dist⟩ := exists_mem_near_abs ε hε f hf

  use a
  constructor
  · exact ha
  · rw [dist_eq_norm]
    rw [← neg_sub a |f|]
    rw [norm_neg]
    exact ha_dist
  done

/- Proof of Max identity with absolute value for Reals -/
lemma max_id_abs (x y : ℝ) : max x y = 1/2 * (x + y + |x - y|) := by
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
lemma min_id_abs (x y : ℝ) : min x y = 1/2 * (x + y - |x - y|) := by
  cases le_total x y with
  | inl leq =>
    rw[min_eq_left leq]
    rw [abs_of_nonpos (sub_nonpos_of_le leq)]
    ring
    | inr geq =>
    rw[min_eq_right geq]
    rw [abs_of_nonneg (sub_nonneg_of_le geq)]
    ring
  done


/- Proof of pointwise Max identity with absolute value for Functions -/
lemma max_id_abs_func (f g : C(Ω, ℝ)) :
    f ⊔ g = (1/2 : ℝ) • (f + g + |f - g|) := by
  ext a
  rw [@smul_apply, sup_apply]
  rw [max_id_abs]
  simp
  done


/- Proof of pointwise Min identity with absolute value for Functions -/
lemma min_id_abs_func (f g : C(Ω, ℝ)) :
    f ⊓ g = (1/2 : ℝ) • (f + g - |f - g|) := by
  ext a
  rw [@smul_apply, inf_apply]
  rw [min_id_abs]
  simp
  done


/- Proof that a Subalgebra is topologically closed under pointwise maximum -/
lemma sup_mem_of_closed_subalg (f g : A) (hA : IsClosed (A : Set C(Ω, ℝ))) :
    ↑f ⊔ ↑g ∈ A := by
  rw [max_id_abs_func]
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
    ↑f ⊓ ↑g ∈ A := by
  rw [min_id_abs_func]
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


-- /- Definition of a Set of functions separating points -/
-- def SetSeparatesPoints {α β : Type*} (S : Set (α → β)) : Prop :=
--   ∀ {x y : α}, x ≠ y → ∃ f ∈ S, (f x ≠ f y)


-- /- Definition of what it means for a Subalgebra of C(Ω, ℝ) to separate points -/
-- abbrev SeparatesPoints (A : Subalgebra ℝ C(Ω, ℝ)) : Prop :=
--   Set.SeparatesPoints (A : Set C(Ω, ℝ))

-- /- Uryshon Lemma -/

-- lemma Urysohn () : F.SeparatesPoints


/- Proof that if the Subalgebra separates points, then so does its Topological Closure -/
lemma subalg_closure_sep_points (h_sep : A.SeparatesPoints) :
    A.topologicalClosure.SeparatesPoints := by
  intro x y h_neq
  obtain ⟨f, hf_in_A, hf_sep⟩ := h_sep h_neq
  use f
  constructor
  · apply Set.image_mono A.le_topologicalClosure
    exact hf_in_A
  · exact hf_sep

/- Proof that there exists a function in the Subalgebra that matches any function at 2 points -/
-- lemma SubAlgClosureMatchesAt2Points {f : C(Ω, ℝ)} {g_xy : A} (hF: F.SeparatesPoints) :
--     ∀ x y : Ω, x ≠ y → ∃ g_xy, (g_xy x = f x) ∧ (g_xy y = f y) := by
--   sorry


/- The Stone-Weierstrass Theorem -/
theorem stone_weierstrass (h1 : 1 ∈ A) (h_sep : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ := by
  sorry

end SWT
