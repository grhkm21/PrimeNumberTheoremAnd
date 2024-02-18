import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Meromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import EulerProducts.LSeries

open Complex BigOperators Nat Classical Real Topology Filter Set MeasureTheory


open scoped Interval

lemma Complex.abs_neg (z : ℂ) : Complex.abs (-z) = Complex.abs z :=
  AbsoluteValue.map_neg abs z

/-%%

In this section, we develop residue calculus on rectangles for \emph{simple} poles.

\begin{definition}\label{Rectangle}\lean{Rectangle}\leanok
A Rectangle has corners $z$ and $w \in \C$.
\end{definition}
%%-/
/-- A `Rectangle` has corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

lemma Rectangle.symm {z w : ℂ} : Rectangle z w = Rectangle w z := by
  simp_rw [Rectangle, Set.uIcc_comm]

lemma Rectangle.symm_re {z w : ℂ} :
    Rectangle (w.re + z.im * I) (z.re + w.im * I) = Rectangle z w := by
  simp [Rectangle, Set.uIcc_comm]

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)

lemma Square_apply (p : ℂ) {c : ℝ} (cpos : c > 0) :
    Square p c =
      Icc (-c + p.re) (c + p.re) ×ℂ Icc (-c + p.im) (c + p.im) := by
  rw [Square, Rectangle, uIcc_of_le (by simp; linarith), uIcc_of_le (by simp; linarith)]
  simp

/-%%
\begin{definition}[RectangleIntegral]\label{RectangleIntegral}\lean{RectangleIntegral}\leanok
A RectangleIntegral of a function $f$ is one over a rectangle determined by $z$ and $w$ in $\C$.
We will sometimes denote it by $\int_{z}^{w} f$. (There is also a primed version, which is $1/(2\pi i)$ times the original.)
\end{definition}
%%-/
/-- A `RectangleIntegral` of a function `f` is one over a rectangle determined by
  `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

noncomputable abbrev RectangleIntegral' (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    (1/(2 * π * I)) * RectangleIntegral f z w

/-%%
The border of a rectangle is the union of its four sides.
\begin{definition}[RectangleBorder]\label{RectangleBorder}\lean{RectangleBorder}\leanok
A Rectangle's border, given corners $z$ and $w$ is the union of the four sides.
\end{definition}
%%-/
/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]


/-%%
An UpperUIntegral is the integral of a function over a |\_| shape.
\begin{definition}\label{UpperUIntegral}\lean{UpperUIntegral}\leanok
An UpperUIntegral of a function $f$ comes from $\sigma+i\infty$ down to $\sigma+iT$, over to $\sigma'+iT$, and back up to $\sigma'+i\infty$.
\end{definition}
%%-/
noncomputable def UpperUIntegral (f : ℂ → ℂ) (σ σ' T : ℝ) : ℂ :=
    ((∫ x : ℝ in σ..σ', f (x + T * I))
     + I • (∫ y : ℝ in Ici T, f (σ' + y * I)) - I • ∫ y : ℝ in Ici T, f (σ + y * I))

/-%%
A LowerUIntegral is the integral of a function over a |-| shape.
\begin{definition}[LowerUIntegral]\label{LowerUIntegral}\lean{LowerUIntegral}\leanok
A LowerUIntegral of a function $f$ comes from $\sigma-i\infty$ up to $\sigma-iT$, over to $\sigma'-iT$, and back down to $\sigma'-i\infty$.
\end{definition}
%%-/
noncomputable def LowerUIntegral (f : ℂ → ℂ) (σ σ' T : ℝ) : ℂ :=
    ((∫ x : ℝ in σ..σ', f (x - T * I))
     - I • (∫ y : ℝ in Iic (-T), f (σ' + y * I)) + I • ∫ y : ℝ in Iic (-T), f (σ + y * I))


/-%%
It is very convenient to define integrals along vertical lines in the complex plane, as follows.
\begin{definition}[VerticalIntegral]\label{VerticalIntegral}\leanok
Let $f$ be a function from $\mathbb{C}$ to $\mathbb{C}$, and let $\sigma$ be a real number. Then we define
$$\int_{(\sigma)}f(s)ds = \int_{\sigma-i\infty}^{\sigma+i\infty}f(s)ds.$$
\end{definition}
%%-/

noncomputable def VerticalIntegral (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
  I • ∫ t : ℝ, f (σ + t * I)

--%% We also have a version with a factor of $1/(2\pi i)$.
noncomputable abbrev VerticalIntegral' (f : ℂ → ℂ) (σ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * VerticalIntegral f σ

lemma verticalIntegral_split_three {f : ℂ → ℂ} {σ : ℝ} (a b : ℝ) (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ = I • (∫ t in Iic (a), f (σ + t * I)) + I • (∫ t in a..b, f (σ + t * I))
    + I • ∫ t in Ici b, f (σ + t * I) := by
  simp_rw [VerticalIntegral, ← smul_add]
  congr
  rw [← intervalIntegral.integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel'_right,
    integral_Iic_eq_integral_Iio, intervalIntegral.integral_Iio_add_Ici hf.restrict hf.restrict]

-- From PR #9598
/-- The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`. -/
lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

-- From PR #9598
/-- The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`. -/
lemma reProdIm_subset_iff {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  simp_rw [← preimage_equivRealProd_prod, equivRealProd.preimage_subset]

-- From PR #9598
/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ :=
  reProdIm_subset_iff.trans prod_subset_prod_iff

/-- The axis-parallel complex rectangle with opposite corners `z` and `w` is complex product
  of two intervals, which is also the convex hull of the four corners. Golfed from mathlib4\#9598.-/
lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm, reProdIm]
  exact congrArg _ <| Set.ext <| by simpa [Complex.ext_iff] using by tauto

/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. Golfed from mathlib4\#9598.-/
lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  rw [Rectangle, segment_reProdIm_segment_eq_convexHull]
  exact convexHull_min (by simp_all [insert_subset_iff]) U_convex

lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔ z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc

-- Exists in Mathlib; need to update version
/-- The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
noncomputable def equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ :=
  equivRealProdLm.toContinuousLinearEquivOfBounds 1 (Real.sqrt 2) equivRealProd_apply_le' fun p =>
    abs_le_sqrt_two_mul_max (equivRealProd.symm p)

lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  simpa [Square] using Rectangle.symm

def Set.uIoo {α : Type*} [Lattice α] (a b : α) : Set α := Ioo (a ⊓ b) (a ⊔ b)

@[simp]
theorem uIoo_of_le {α : Type*} [Lattice α] {a b : α} (h : a ≤ b) : Set.uIoo a b = Ioo a b := by
  rw [uIoo, inf_eq_left.2 h, sup_eq_right.2 h]

lemma square_mem_nhds (p : ℂ) {c : ℝ} (hc : c ≠ 0) :
    Square p c ∈ 𝓝 p := by
  rw [Square, Rectangle, mem_nhds_iff]
  refine ⟨(uIoo (-c + p.re) (c + p.re)) ×ℂ (uIoo (-c + p.im) (c + p.im)), ?_, ?_, ?_⟩
  · refine reProdIm_subset_iff'.mpr (Or.inl ⟨?_, ?_⟩) <;> simpa using Ioo_subset_Icc_self
  · exact isOpen_Ioo.reProdIm isOpen_Ioo
  · exact ⟨by simp [uIoo, hc, hc.symm], by simp [uIoo, hc, hc.symm]⟩

lemma square_subset_closedBall (p : ℂ) (c : ℝ) :
    Square p c ⊆ Metric.closedBall p (|c| * Real.sqrt 2) := by
  wlog hc : c ≥ 0 with h
  · rw [← square_neg, ← _root_.abs_neg]
    exact h p (-c) (neg_nonneg.mpr (le_of_not_le hc))
  intro x hx
  unfold Square Rectangle at hx
  replace hx : x ∈ [[-c + p.re, c + p.re]] ×ℂ [[-c + p.im, c + p.im]] := by simpa using hx
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hx
  simp_rw [← sub_eq_neg_add, add_comm c, ← Real.closedBall_eq_Icc] at hx
  obtain ⟨hx_re : x.re ∈ Metric.closedBall p.re c, hx_im : x.im ∈ Metric.closedBall p.im c⟩ := hx
  rw [mem_closedBall_iff_norm] at hx_re hx_im ⊢
  rw [_root_.mul_self_le_mul_self_iff (norm_nonneg _) (by positivity),
    Complex.norm_eq_abs, ← sq, Complex.sq_abs, Complex.normSq_apply]
  simp_rw [← abs_mul_abs_self (x - p).re, ← abs_mul_abs_self (x - p).im, ← Real.norm_eq_abs]
  calc
    _ ≤ c * c + c * c := by gcongr <;> assumption
    _ = 2 * (‖c‖ * ‖c‖) := by rw [← two_mul]; congr 1; simp
    _ = (Real.sqrt 2) * (Real.sqrt 2) * (‖c‖ * ‖c‖) := by rw [mul_self_sqrt zero_le_two]
    _ = _ := by group

/-%%
\begin{lemma}[DiffVertRect_eq_UpperLowerUs]\label{DiffVertRect_eq_UpperLowerUs}\lean{DiffVertRect_eq_UpperLowerUs}\leanok
The difference of two vertical integrals and a rectangle is the difference of an upper and a lower U integrals.
\end{lemma}
%%-/
lemma DiffVertRect_eq_UpperLowerUs {f : ℂ → ℂ} {σ σ' T : ℝ}
    (f_int_σ : Integrable (fun (t : ℝ) ↦ f (σ + t * I)))
    (f_int_σ' : Integrable (fun (t : ℝ) ↦ f (σ' + t * I))) :
  (VerticalIntegral f σ') - (VerticalIntegral f σ) - (RectangleIntegral f (σ - I * T) (σ' + I * T)) = (UpperUIntegral f σ σ' T) - (LowerUIntegral f σ σ' T) := by
  rw[verticalIntegral_split_three (-T) T f_int_σ, verticalIntegral_split_three (-T) T f_int_σ',
    RectangleIntegral, UpperUIntegral, LowerUIntegral]
  norm_num
  have {a b c d e g h i : ℂ} :
    a + b + c - (d + e + g) - (h - i + b - e) = i + c - g - (h - a + d) := by ring
  convert this using 1

/-%%
\begin{proof}\uses{UpperUIntegral, LowerUIntegral}\leanok
Follows directly from the definitions.
\end{proof}
%%-/

/-- A function is `HolomorphicOn` a set if it is complex differentiable on that set. -/
abbrev HolomorphicOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (s : Set ℂ) :
    Prop := DifferentiableOn ℂ f s



/-%%
\begin{theorem}[existsDifferentiableOn_of_bddAbove]\label{existsDifferentiableOn_of_bddAbove}\lean{existsDifferentiableOn_of_bddAbove}\leanok
If $f$ is differentiable on a set $s$ except at $c\in s$, and $f$ is bounded above on $s\setminus\{c\}$, then there exists a differentiable function $g$ on $s$ such that $f$ and $g$ agree on $s\setminus\{c\}$.
\end{theorem}
%%-/
theorem existsDifferentiableOn_of_bddAbove {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E), HolomorphicOn g s ∧ (Set.EqOn f g (s \ {c})) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim else by simp [h]⟩
/-%%
\begin{proof}\leanok
This is the Reimann Removable Singularity Theorem, slightly rephrased from what's in Mathlib. (We don't care what the function $g$ is, just that it's holomorphic.)
\end{proof}
%%-/

/-%%
\begin{theorem}[HolomorphicOn.vanishesOnRectangle]\label{HolomorphicOn.vanishesOnRectangle}\lean{HolomorphicOn.vanishesOnRectangle}\leanok
If $f$ is holomorphic on a rectangle $z$ and $w$, then the integral of $f$ over the rectangle with corners $z$ and $w$ is $0$.
\end{theorem}
%%-/
theorem HolomorphicOn.vanishesOnRectangle {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (f_holo : HolomorphicOn f U) (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w (f_holo.mono hU)
/-%%
\begin{proof}\leanok
This is in a Mathlib PR.
\end{proof}
%%-/

-- ## Rectangle API ##

lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩

lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := ⟨right_mem_uIcc, right_mem_uIcc⟩

lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  use fun h ↦ ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  intro ⟨⟨⟨hz're_ge, hz're_le⟩, ⟨hz'im_ge, hz'im_le⟩⟩,
    ⟨⟨hw're_ge, hw're_le⟩, ⟨hw'im_ge, hw'im_le⟩⟩⟩ x ⟨⟨hxre_ge, hxre_le⟩, ⟨hxim_ge, hxim_le⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_inf hz're_ge hw're_ge).trans hxre_ge
  · exact (le_sup_iff.mp hxre_le).casesOn (fun h ↦ h.trans hz're_le) (fun h ↦ h.trans hw're_le)
  · exact (le_inf hz'im_ge hw'im_ge).trans hxim_ge
  · exact (le_sup_iff.mp hxim_le).casesOn (fun h ↦ h.trans hz'im_le) (fun h ↦ h.trans hw'im_le)

lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁) (x₁_le_x₂ : x₁ ≤ x₂)
    (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁) (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆ Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff, mem_Rect, mem_Rect]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simpa using by linarith

lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re) (x₁_le_x₂ : z₁.re ≤ z₂.re)
    (x₂_le_x₃ : z₂.re ≤ z₃.re) (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [← re_add_im z₀, ← re_add_im z₁, ← re_add_im z₂, ← re_add_im z₃]
  exact RectSubRect x₀_le_x₁ x₁_le_x₂ x₂_le_x₃ y₀_le_y₁ y₁_le_y₂ y₂_le_y₃

lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

/-- Note: try using `by simp` for `h`. -/
lemma rectangle_disjoint_singleton {z w p : ℂ}
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by
  refine disjoint_singleton_right.mpr (not_and_or.mpr ?_)
  obtain h | h | h | h := h
  · exact Or.inl (not_mem_uIcc_of_lt h.1 h.2)
  · exact Or.inr (not_mem_uIcc_of_lt h.1 h.2)
  · exact Or.inl (not_mem_uIcc_of_gt h.1 h.2)
  · exact Or.inr (not_mem_uIcc_of_gt h.1 h.2)

lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩, fun hc ↦ h.2.1 hc.1⟩

lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_diff.mpr ⟨by apply RectSubRect' <;> tauto, rectangle_disjoint_singleton hp⟩

lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_diff.mpr ⟨
    (rectangleBorder_subset_rectangle _ _).trans (by apply RectSubRect' <;> tauto),
    rectangleBorder_disjoint_singleton hp⟩

/-- A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment.
Golfed from mathlib\#9598.-/
lemma horizontalSegment_eq (a₁ a₂ b : ℝ) :
    (fun (x : ℝ) ↦ x + b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×ℂ {b} :=
  Set.ext fun _ => ⟨fun hx ↦ hx.casesOn fun _ ⟨_, hx⟩ ↦ by simpa [← hx, reProdIm],
    fun hx ↦ hx.casesOn (by simp_all [Complex.ext_iff])⟩

/-- A vertical segment `[b₁, b₂]` translated by `a` is the complex line segment.
Golfed from mathlib\#9598.-/
lemma verticalSegment_eq (a b₁ b₂ : ℝ) :
    (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] = {a} ×ℂ [[b₁, b₂]] :=
  Set.ext fun _ => ⟨fun hx ↦ hx.casesOn fun _ ⟨_, hx⟩ ↦ by simpa [← hx, reProdIm],
    fun hx ↦ hx.casesOn (by simp_all [Complex.ext_iff])⟩

theorem RectangleIntegral_congr {f g : ℂ → ℂ} {z w : ℂ} (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral
  congr 2; swap; congr 1; swap; congr 1
  all_goals refine intervalIntegral.integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr {f g : ℂ → ℂ} {z w : ℂ} (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

theorem rectangleIntegral_symm (f : ℂ → ℂ) (z w : ℂ) :
    RectangleIntegral f z w = RectangleIntegral f w z := by
  simp_rw [RectangleIntegral, intervalIntegral.integral_symm w.re,
    intervalIntegral.integral_symm w.im, smul_eq_mul]
  group

theorem rectangleIntegral_symm_re (f : ℂ → ℂ) (z w : ℂ) :
    RectangleIntegral f (w.re + z.im * I) (z.re + w.im * I) = - RectangleIntegral f z w := by
  simp? [RectangleIntegral, intervalIntegral.integral_symm w.re] says
    simp only [RectangleIntegral._eq_1, add_im, ofReal_im, mul_im, ofReal_re, I_im,
      mul_one, I_re, mul_zero, add_zero, zero_add, add_re, mul_re, sub_self, smul_eq_mul,
      intervalIntegral.integral_symm w.re, sub_neg_eq_add, neg_sub]
  group

def RectangleBorderIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → ℂ} {z w : ℂ} (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral]
  rw [intervalIntegral.integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1, intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem HolomorphicOn.rectangleBorderIntegrable' {f : ℂ → ℂ} {z w p : ℂ}
    (hf : HolomorphicOn f (Rectangle z w \ {p}))
    (pInInterior : Rectangle z w ∈ nhds p) : RectangleBorderIntegrable f z w := by
  sorry

theorem HolomorphicOn.rectangleBorderIntegrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : HolomorphicOn f (Rectangle z w))
    : RectangleBorderIntegrable f z w := by
  sorry

lemma mapsTo_rectangle_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_rectangle_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_rectangle_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_rectangle_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦ by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦ by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦ by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦ by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangle_left_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_left_re z w).mono_right (Set.subset_diff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_right_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_right_re z w).mono_right (Set.subset_diff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_left_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_left_im z w).mono_right (Set.subset_diff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_right_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_right_im z w).mono_right (Set.subset_diff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem ContinuousOn.rectangleBorder_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (RectangleBorder z w)) : RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

theorem ContinuousOn.rectangleBorderIntegrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  (hf.mono (rectangleBorder_subset_rectangle z w)).rectangleBorder_integrable

theorem ContinuousOn.rectangleBorderNoPIntegrable {f : ℂ → ℂ} {z w p : ℂ}
    (hf : ContinuousOn f (Rectangle z w \ {p}))
    (pNotOnBorder : p ∉ RectangleBorder z w) : RectangleBorderIntegrable f z w := by
  refine (hf.mono (Set.subset_diff.mpr ?_)).rectangleBorder_integrable
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma Real.Icc_mem_nhds_iff_mem_Ioo (a b : ℝ) (p : ℝ) : Set.Icc a b ∈ 𝓝 p ↔ p ∈ Set.Ioo a b := by
  rw [← mem_interior_iff_mem_nhds, interior_Icc]

lemma Complex.image_ball_re {p : ℂ} {ε : ℝ} :
    Complex.re '' Metric.ball p ε = Metric.ball p.re ε := by
  ext x; constructor <;> intro hx
  · obtain ⟨x', hx', hxx'⟩ := hx
    rw [mem_ball_iff_norm'] at hx' ⊢
    rw [← hxx', ← sub_re]
    exact (IsROrC.norm_re_le_norm (p - x')).trans_lt hx'
  · refine ⟨x + p.im * I, ?_, by simp⟩
    rw [mem_ball_iff_norm'] at hx ⊢
    simp_rw [show p - (↑x + ↑p.im * I) = ↑(p.re - x) by simp [Complex.ext_iff], norm_real, hx]

lemma Complex.image_ball_im {p : ℂ} {ε : ℝ} :
    Complex.im '' Metric.ball p ε = Metric.ball p.im ε := by
  ext x; constructor <;> intro hx
  · obtain ⟨x', hx', hxx'⟩ := hx
    rw [mem_ball_iff_norm'] at hx' ⊢
    rw [← hxx', ← sub_im]
    exact (IsROrC.norm_im_le_norm (p - x')).trans_lt hx'
  · refine ⟨p.re + x * I, ?_, by simp⟩
    rw [mem_ball_iff_norm'] at hx ⊢
    simp_rw [show p - (↑p.re + ↑x * I) = ↑(p.im - x) * I by simp [Complex.ext_iff], norm_mul,
      norm_I, mul_one, norm_real, hx]

lemma Complex.image_reProdIm_re {a b : Set ℝ} : Complex.re '' (a ×ℂ b) ⊆ a :=
  fun _ ↦ fun ⟨_, hx', hxx'⟩ ↦ hxx' ▸ hx'.1

lemma Complex.image_reProdIm_im {a b : Set ℝ} : Complex.im '' (a ×ℂ b) ⊆ b :=
  fun _ ↦ fun ⟨_, hx', hxx'⟩ ↦ hxx' ▸ hx'.2

lemma reProdIm_mem_nhds_iff {a b : Set ℝ} {p : ℂ} :
    a ×ℂ b ∈ 𝓝 p ↔ a ∈ 𝓝 p.re ∧ b ∈ 𝓝 p.im := by
  constructor <;> intro h
  · simp_rw [Metric.mem_nhds_iff] at h ⊢
    obtain ⟨ε, ε_pos, ε_subset⟩ := h
    constructor <;> use ε, ε_pos
    · exact Complex.image_ball_re ▸ (image_mono ε_subset).trans Complex.image_reProdIm_re
    · exact Complex.image_ball_im ▸ (image_mono ε_subset).trans Complex.image_reProdIm_im
  · simp_rw [mem_nhds_iff] at h ⊢
    obtain ⟨⟨a', ha', ha'_open, ha'p⟩, ⟨b', hb', hb'_open, hb'_p⟩⟩ := h
    use a' ×ℂ b', reProdIm_subset_iff'.mpr (Or.inl ⟨ha', hb'⟩), ha'_open.reProdIm hb'_open
    exact ⟨ha'p, hb'_p⟩

lemma rect_mem_nhds_iff {z w p : ℂ}:
    Rectangle z w ∈ 𝓝 p ↔ p ∈ uIoo z.re w.re ×ℂ uIoo z.im w.im := by
  simp_rw [Rectangle, reProdIm_mem_nhds_iff, uIcc, Real.Icc_mem_nhds_iff_mem_Ioo, uIoo]
  rfl

-- ## End Rectangle API ##

/--
Given `x₀ a x₁ : ℝ`, and `y₀ y₁ : ℝ` and a function `f : ℂ → ℂ` so that
both `(t : ℝ) ↦ f(t + y₀ * I)` and `(t : ℝ) ↦ f(t + y₁ * I)` are integrable over both
`t ∈ Icc x₀ a` and `t ∈ Icc a x₁`, we have that
`RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I)` is the sum of
`RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I)` and
`RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I)`.
-/
lemma RectangleIntegralHSplit {f : ℂ → ℂ} {a x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral]
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_self]
  rw [← intervalIntegral.integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot,
    ← intervalIntegral.integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top]
  ring

lemma RectangleIntegralHSplit' {f : ℂ → ℂ} {a x₀ x₁ y₀ y₁ : ℝ} (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) :=
  RectangleIntegralHSplit
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)

lemma RectangleIntegralVSplit {f : ℂ → ℂ} {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral]
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_self]
  rw [← intervalIntegral.integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left,
    ← intervalIntegral.integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right]
  ring

lemma RectangleIntegralVSplit' {f : ℂ → ℂ} {b x₀ x₁ y₀ y₁ : ℝ} (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) :=
  RectangleIntegralVSplit
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)

lemma SmallSquareInRectangle {z w p : ℂ} (pInRectInterior : Rectangle z w ∈ nhds p) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, Square p c ⊆ Rectangle z w := by
  obtain ⟨c₁, c₁Pos, c₁SubRect⟩ := Metric.mem_nhds_iff.mp pInRectInterior
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' (half_pos c₁Pos)]
  intro c ⟨cPos, cLt⟩
  refine subset_trans (square_subset_closedBall p c) <| subset_trans ?_ c₁SubRect
  have : Real.sqrt 2 < 2 := by refine (Real.sqrt_lt ?_ ?_).mpr ?_ <;> norm_num
  exact (abs_of_pos cPos).symm ▸ Metric.closedBall_subset_ball (by nlinarith)

lemma RectanglePullToNhdOfPole' {f : ℂ → ℂ} {z₀ z₁ z₂ z₃ p : ℂ}
    (h_orientation : z₀.re ≤ z₃.re ∧ z₀.im ≤ z₃.im ∧ z₁.re ≤ z₂.re ∧ z₁.im ≤ z₂.im)
    (hp : Rectangle z₁ z₂ ∈ 𝓝 p) (hz : Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃)
    (fHolo : HolomorphicOn f (Rectangle z₀ z₃ \ {p})) :
    RectangleIntegral f z₀ z₃ = RectangleIntegral f z₁ z₂ := by
  obtain ⟨hz₀_re, hz₀_im, hz₁_re, hz₁_im⟩ := h_orientation
  have := rect_subset_iff.mp hz
  rw [Rectangle, uIcc_of_le hz₀_re, uIcc_of_le hz₀_im] at this
  obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := this
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := (uIoo_of_le hz₁_re) ▸ (uIoo_of_le hz₁_im) ▸ rect_mem_nhds_iff.mp hp
  obtain ⟨_, _, _, _⟩ := show p.re < z₂.re ∧ p.re < z₃.re ∧ p.im < z₂.im ∧ p.im < z₃.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨_, _, _, _⟩ := show z₀.re < p.re ∧ z₁.re < p.re ∧ z₀.im < p.im ∧ z₁.im < p.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩

  have fCont := fHolo.continuousOn

  have hbot : RectangleBorderIntegrable f (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₃.im * I) := ?_
  have htop : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I) (↑z₃.re + ↑z₃.im * I) := ?_
  have hleft : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) := ?_
  have hright : RectangleBorderIntegrable f (↑z₁.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) := ?_
  all_goals try {
    refine (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_)).rectangleBorder_integrable
    · simp_all
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  }
  have hbot' : z₁.im ∈ [[z₀.im, z₃.im]] := ?_
  have htop' : z₂.im ∈ [[z₁.im, z₃.im]] := ?_
  have hleft' : z₁.re ∈ [[z₀.re, z₃.re]] := ?_
  have hright' : z₂.re ∈ [[z₁.re, z₃.re]] := ?_
  all_goals try { rw [Set.uIcc_of_le]; constructor; all_goals assumption }
  have hbot'' : Rectangle (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₁.im * I) ⊆ Rectangle z₀ z₃ \ {p} := ?_
  have htop'' : Rectangle (↑z₀.re + ↑z₂.im * I) (↑z₃.re + ↑z₃.im * I) ⊆ Rectangle z₀ z₃ \ {p} := ?_
  have hleft'' : Rectangle (↑z₀.re + ↑z₁.im * I) (↑z₁.re + ↑z₂.im * I) ⊆ Rectangle z₀ z₃ \ {p} := ?_
  have hright'' : Rectangle (↑z₂.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) ⊆ Rectangle z₀ z₃ \ {p} := ?_
  all_goals try { apply rectangle_subset_punctured_rect <;> simp_all }

  rw [← re_add_im z₀, ← re_add_im z₃,
    RectangleIntegralVSplit' hbot' hbot, fHolo.vanishesOnRectangle hbot'', zero_add,
    RectangleIntegralVSplit' htop' htop, fHolo.vanishesOnRectangle htop'', add_zero,
    RectangleIntegralHSplit' hleft' hleft, fHolo.vanishesOnRectangle hleft'', zero_add,
    RectangleIntegralHSplit' hright' hright, fHolo.vanishesOnRectangle hright'', add_zero,
    re_add_im, re_add_im]

/-%%
The next lemma allows to zoom a big rectangle down to a small square, centered at a pole.

\begin{lemma}[RectanglePullToNhdOfPole]\label{RectanglePullToNhdOfPole}\lean{RectanglePullToNhdOfPole}\leanok
If $f$ is holomorphic on a rectangle $z$ and $w$ except at a point $p$, then the integral of $f$
over the rectangle with corners $z$ and $w$ is the same as the integral of $f$ over a small square
centered at $p$.
\end{lemma}
%%-/
/-- Given `f` holomorphic on a rectangle `z` and `w` except at a point `p`, the integral of `f` over
the rectangle with corners `z` and `w` is the same as the integral of `f` over a small square
centered at `p`. -/
lemma RectanglePullToNhdOfPole {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re ≤ w.re)
    (zIm_lt_wIm : z.im ≤ w.im) (hp : Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
    RectangleIntegral f z w = RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
/-%%
\begin{proof}\uses{HolomorphicOn.vanishesOnRectangle}\leanok
Chop the big rectangle with two vertical cuts and two horizontal cuts into smaller rectangles,
the middle one being the desired square. The integral over each of the outer rectangles
vanishes, since $f$ is holomorphic there. (The constant $c$ being ``small enough'' here just means
that the inner square is strictly contained in the big rectangle.)
%%-/
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' zero_lt_one, SmallSquareInRectangle hp]
  intro c ⟨cpos, _⟩ hc
  simp_rw [mul_comm I]
  exact RectanglePullToNhdOfPole' (by simp_all [cpos.le])
    (square_mem_nhds p (ne_of_gt cpos)) hc fHolo
--%%\end{proof}

theorem ResidueTheoremAtOrigin_aux1a_aux1 (x : ℝ)
  : 1 / (1 + (ofReal' x) ^ 2) = ofReal' (1 / (1 + x ^ 2)) := by
  simp only [one_div, ofReal_inv, ofReal_add, ofReal_one, ofReal_pow]

theorem ResidueTheoremAtOrigin_aux1a_aux2 :
  ∫ (x : ℝ) in (-1)..1, (1 / (1 + x ^ 2) : ℂ) = ∫ (x : ℝ) in (-1)..1, (1 / (1 + x ^ 2) : ℝ) := by
  simp_rw [ResidueTheoremAtOrigin_aux1a_aux1]
  exact intervalIntegral.integral_ofReal (f := (fun x => 1 / (1 + x ^ 2)))

theorem ResidueTheoremAtOrigin_aux1a :
    ∫ (x : ℝ) in (-1)..1, ((1 + x ^ 2)⁻¹ : ℂ) = ↑(arctan 1) - ↑(arctan (-1)) := by
  norm_cast
  rw [intervalIntegral.integral_ofReal, integral_inv_one_add_sq]

theorem ResidueTheoremAtOrigin_aux1b (x : ℝ) :
    (x + -I)⁻¹ - (x + I)⁻¹ = (2 * I) * ↑((1 + x ^ 2)⁻¹ : ℝ) := by
  have hu₁ : IsUnit (x + -I) := Ne.isUnit (by simp [Complex.ext_iff])
  have hu₂ : IsUnit (x + I) := Ne.isUnit (by simp [Complex.ext_iff])
  apply hu₁.mul_left_cancel
  rw [mul_sub, hu₁.mul_inv_cancel]
  apply hu₂.mul_left_cancel
  calc
    _ = (x + I) * 1 - (x + I)⁻¹ * (x + I) * (x + -I) := by group
    _ = (1 : ℝ) * (2 * I) := by simp [hu₂.inv_mul_cancel, two_mul]
    _ = ((1 + x ^ 2)⁻¹ * (1 + x ^ 2) : ℝ) * (2 * I) := by
      congr 2
      exact (Ne.isUnit (by nlinarith)).inv_mul_cancel.symm
    _ = ((1 + x ^ 2 : ℂ)⁻¹ * ((x + I) * (x + -I))) * (2 * I) := by
      push_cast
      congr 2
      trans - I ^ 2 + x ^ 2; simp; group
    _ = _ := by norm_cast; group

theorem ResidueTheoremAtOrigin_aux1c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y + I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux1c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (↑y + -I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux1 :
    (∫ (x : ℝ) in (-1 - 0)..(1 + 0), 1 / (x + (-0 - 1 : ℝ) * I)) -
    ∫ (x : ℝ) in (-1 - 0)..(1 + 0), 1 / (x + (0 + 1 : ℝ) * I) = π * I := by
  suffices (∫ (x : ℝ) in (-1 : ℝ)..1, (x + -I)⁻¹) - ∫ (x : ℝ) in (-1 : ℝ)..1, (x + I)⁻¹ = π * I by
    simpa
  rw [← intervalIntegral.integral_sub
    (ResidueTheoremAtOrigin_aux1c' (-1) 1) (ResidueTheoremAtOrigin_aux1c (-1) 1)]
  trans 2 * I * (π / 4 + π / 4)
  · simp [ResidueTheoremAtOrigin_aux1b, ResidueTheoremAtOrigin_aux1a]
  · group

theorem ResidueTheoremAtOrigin_aux2b (y : ℝ) :
    (1 + y * I)⁻¹ - (-1 + y * I)⁻¹ = 2 * ((1 + y ^ 2)⁻¹ : ℝ) := by
  have hu₁ : IsUnit (1 + y * I) := Ne.isUnit (by simp [Complex.ext_iff])
  have hu₂ : IsUnit (-1 + y * I) := Ne.isUnit (by simp [Complex.ext_iff])
  apply hu₁.mul_left_cancel
  rw [mul_sub, hu₁.mul_inv_cancel]
  apply hu₂.mul_left_cancel
  calc
    _ = (-1 + ↑y * I) * 1 - (-1 + ↑y * I)⁻¹ * (-1 + ↑y * I) * (1 + ↑y * I) := by group
    _ = ((1 * -2) : ℝ) := by trans -1 - 1; simp [hu₂.inv_mul_cancel]; norm_num
    _ = (((1 + y ^ 2)⁻¹ * (1 + y ^ 2) : ℝ) * (-2) : ℝ) := by
      congr 2
      exact (Ne.isUnit (by nlinarith)).inv_mul_cancel.symm
    _ = (1 + (y : ℂ) ^ 2)⁻¹ * (1 + (y : ℂ) ^ 2) * (-2) := by norm_cast
    _ = (1 + (y : ℂ) ^ 2)⁻¹ * (-(1 + y * I) * (-1 + y * I)) * (-2) := by
      congr 2
      trans 1 - ↑y ^ 2 * I ^ 2; simp; group
    _ = _ := by push_cast; group

theorem ResidueTheoremAtOrigin_aux2c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (1 + ↑y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (-1 + ↑y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2 :
    (I * ∫ (y : ℝ) in (-0 - 1)..0 + 1, 1 / ((1 + 0 : ℝ) + y * I)) -
    I * ∫ (y : ℝ) in (-0 - 1)..0 + 1, 1 / ((-1 - 0 : ℝ) + y * I) = π * I := by
  rw [← mul_sub, mul_comm (π : ℂ) I]
  suffices (∫ y in (-1 : ℝ)..1, (1 + ↑y * I)⁻¹) - ∫ y in (-1 : ℝ)..1, (-1 + ↑y * I)⁻¹ = ↑π by simpa
  rw [← intervalIntegral.integral_sub
    (ResidueTheoremAtOrigin_aux2c (-1) 1) (ResidueTheoremAtOrigin_aux2c' (-1) 1)]
  trans 2 * (↑π / 4 + ↑π / 4)
  · simp [ResidueTheoremAtOrigin_aux2b, ResidueTheoremAtOrigin_aux1a]
  · group

/-%%
\begin{lemma}[ResidueTheoremAtOrigin]\label{ResidueTheoremAtOrigin}
\lean{ResidueTheoremAtOrigin}\leanok
The rectangle (square) integral of $f(s) = 1/s$ with corners $-1-i$ and $1+i$ is equal to $2\pi i$.
\end{lemma}
%%-/
lemma ResidueTheoremAtOrigin :
    RectangleIntegral' (fun s ↦ 1 / s) (-1 - I) (1 + I) = 1 := by
  dsimp [RectangleIntegral', RectangleIntegral]
  rw [ResidueTheoremAtOrigin_aux1, add_sub_assoc, ResidueTheoremAtOrigin_aux2]
  trans  1 / (2 * ↑π * I) * (2 * ↑π * I)
  · group
  · exact one_div_mul_cancel (by norm_num; exact pi_ne_zero)
/-%%
\begin{proof}\leanok
The bottom is:
$$
\frac1{2\pi i}
\int_{-1-i}^{1-i} \frac1z dz
=
\frac1{2\pi i}
\int_{-1}^1 \frac1{x-i} dx,
$$
and the top is the negative of:
$$
\frac1{2\pi i}
\int_{-1+i}^{1+i} \frac1z dz
=
\frac1{2\pi i}
\int_{-1}^1 \frac1{x+i} dx.
$$
The two together add up to:
$$
\frac1{2\pi i}
\int_{-1}^1
\left(\frac1{x-i}-\frac1{x+i} \right)dx
=
\frac1{\pi}
\int_{-1}^1
\frac{1}{x^2+1}dx,
$$
which is the arctan at $1$ (namely $\pi/4$) minus that at $-1$. In total, this contributes $1/2$ to the integral.

The vertical sides are:
$$
\frac1{2\pi i}
\int_{1-i}^{1+i} \frac1z dz
=
\frac1{2\pi}
\int_{-1}^1 \frac1{1+iy} dy
$$
and the negative of
$$
\frac1{2\pi i}
\int_{-1-i}^{-1+i} \frac1z dz
=
\frac1{2\pi}
\int_{-1}^1 \frac1{-1+iy} dy.
$$
This difference comes out to:
$$
\frac1{2\pi}
\int_{-1}^1 \left(\frac1{1+iy}-\frac1{-1+iy}\right) dy
=
\frac1{2\pi}
\int_{-1}^1 \left(\frac{-2}{-1-y^2}\right) dy,
$$
which contributes another factor of $1/2$. (Fun! Each of the vertical/horizontal sides contributes half of the winding.)
\end{proof}
%%-/

variable {f : ℂ → ℂ}

theorem ResidueTheoremOnRectangleWithSimplePole_aux1 {z w p z' w' : ℂ}
    (pInRectInterior : Rectangle z w ∈ nhds p)
    (fHolo : ContinuousOn f (Rectangle z w \ {p}))
    (principalPart : Set.EqOn (f) (fun s ↦ 1 / (s - p))
      (Rectangle z w \ {p}))
    :
    let L : ℂ → ℂ := fun s ↦ (s - z) / (w - z) * (w' - z') + z'
    let Linv : ℂ → ℂ := fun s' ↦ (s' - z') / (w' - z') * (w - z) + z
    let p' := L p
    let f' := fun s' ↦ f (Linv s')
    RectangleIntegral' f z w = RectangleIntegral' f' z' w' := by
  sorry

example {z w p : ℂ}
    (pInRectInterior : Rectangle z w ∈ nhds p)
    (fHolo : ContinuousOn f (Rectangle z w \ {p}))
    (principalPart : Set.EqOn (f) (fun s ↦ 1 / (s - p))
      (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = 1 := by
  sorry

theorem exists_of_eventually
  {P : ℝ → Prop}
  (this : ∀ᶠ (c : ℝ) in 𝓝[>] 0, P c)
  :
  ∃ c > 0, P c := by
  have h := Filter.eventually_iff.mp this
  have := (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (by linarith : (0 : ℝ) < 1)).mp h
  obtain ⟨a, ha₁, ha₂⟩ := this
  use a/2
  have : a > 0 := ha₁
  constructor
  · linarith
  have : (a / 2) ∈ Ioo 0 a := by
    simp
    constructor
    · linarith
    assumption
  exact ha₂ this

theorem exists_of_eventually_2
  {P Q : ℝ → Prop}
  (hP : ∀ᶠ (c : ℝ) in 𝓝[>] 0, P c)
  (hQ : ∀ᶠ (c : ℝ) in 𝓝[>] 0, Q c) :
  ∃ c > 0, P c ∧ Q c := exists_of_eventually (Filter.eventually_iff.mp (hP.and hQ))

lemma RectanglePullToNhdOfPole'_former {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    (zIm_lt_wIm : z.im < w.im) (pInRectInterior : Rectangle z w ∈ nhds p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, RectangleIntegral' f z w =
      RectangleIntegral' f (-c - I * c + p) (c + I * c + p) := by
  sorry

/-%%
\begin{lemma}[ResidueTheoremOnRectangleWithSimplePole]\label{ResidueTheoremOnRectangleWithSimplePole}
\lean{ResidueTheoremOnRectangleWithSimplePole}\leanok
Suppose that $f$ is a holomorphic function on a rectangle, except for a simple pole
at $p$. By the latter, we mean that there is a function $g$ holomorphic on the rectangle such that, $f = g + A/(s-p)$ for some $A\in\C$. Then the integral of $f$ over the
rectangle is $A$.
\end{lemma}
%%-/
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_lt_wRe : z.re < w.re)
    (zIm_lt_wIm : z.im < w.im)
    (pInRectInterior : Rectangle z w ∈ nhds p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) (g)
      (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have h₁ := RectanglePullToNhdOfPole'_former zRe_lt_wRe zIm_lt_wIm pInRectInterior fHolo
  have h₂ := SmallSquareInRectangle pInRectInterior
  obtain ⟨c, cpos, hc₁, hc₂⟩ := exists_of_eventually_2 h₁ h₂
  rw [hc₁]
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p)))
    (Rectangle z w \ {p}) := by
    intro s hs
    have := principalPart hs
    simp_all only [mul_eq_mul_left_iff, one_div, mul_inv_rev, inv_I, neg_mul, neg_eq_zero,
      _root_.mul_eq_zero, I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false,
      false_or, eventually_or_distrib_right, gt_iff_lt, mem_diff, mem_singleton_iff, Pi.sub_apply,
      Pi.add_apply]
    rw [← this]
    ring
  -- let's rewrite f using principalPart'
  have principalPart'' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder (-↑c - I * ↑c + p) (↑c + I * ↑c + p)) := by
    apply principalPart'.mono
    sorry
  rw [RectangleIntegral'_congr principalPart'']
  have hg : HolomorphicOn g (Rectangle (-↑c - I * ↑c + p) (↑c + I * ↑c + p)) := by
    sorry
  have hfun : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle (-↑c - I * ↑c + p) (↑c + I * ↑c + p) \ {p}) := by
    sorry
  have pInSquare : Rectangle (-↑c - I * ↑c + p) (↑c + I * ↑c + p) ∈ 𝓝 p := by
    sorry
  have hgInt := hg.rectangleBorderIntegrable
  have hfunInt := hfun.rectangleBorderIntegrable' pInSquare
  have hgInt' := hgInt.add hfunInt
  dsimp [RectangleIntegral']
  rw [hgInt']
  rw [hg.vanishesOnRectangle (fun ⦃a⦄ a => a)]

  sorry

  -- have := exists_of_eventually h₁
  -- obtain ⟨c, cpos, hc⟩ := this
  -- rw [hc]

  -- simp_all
  -- sorry

/-%%
\begin{proof}\uses{ResidueTheoremAtOrigin, RectanglePullToNhdOfPole, HolomorphicOn.vanishesOnRectangle}
Replace $f$ with $g + A/(s-p)$ in the integral.
The integral of $g$ vanishes by Lemma \ref{HolomorphicOn.vanishesOnRectangle}.
 To evaluate the integral of $1/(s-p)$,
pull everything to a square about the origin using Lemma \ref{RectanglePullToNhdOfPole},
and rescale by $c$;
what remains is handled by Lemma \ref{ResidueTheoremAtOrigin}.
\end{proof}
%%-/
