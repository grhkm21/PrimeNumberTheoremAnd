import Mathlib.NumberTheory.VonMangoldt

variable {R : Type*}

/- TODO: Relax this (it should be defined in each section/lemma) -/
variable [hR : CommRing R]
/- This is needed because `isUnit_zero_iff` exists -/
variable [NeZero (1 : R)]
/- This is needed for all invertibility results -/
variable [DecidablePred (@IsUnit R _)]

namespace ArithmeticFunction

/- ------------------------------------------------------------ -/

section missing

open BigOperators Nat Finset

/- This and a few more are missing. I'm just following Apostol. -/
@[simp]
def totient : ArithmeticFunction R := ⟨fun d ↦ φ d, by simp⟩

theorem totient_apply {n : ℕ} : (totient : ArithmeticFunction R) n = φ n := rfl

theorem isMultiplicative_totient : IsMultiplicative (totient : ArithmeticFunction R) :=
  ⟨by simp, fun h ↦ by simp [totient_mul h]⟩

scoped[ArithmeticFunction] notation "φ" => totient

scoped[ArithmeticFunction.Totient] notation "φ" => totient

/- theorem coe_moebius_mul_coe_id : (μ : ArithmeticFunction R) * id = (φ : ArithmeticFunction R) := by -/
/-   ext n -/
/-   induction n using Nat.recOnPosPrimePosCoprime with -/
/-   | hp p k hp_prime hk_pos => -/
/-     rw [totient_apply, totient_prime_pow hp_prime hk_pos, mul_apply, -/
/-       sum_divisorsAntidiagonal ((μ : ArithmeticFunction R) · * (id : ArithmeticFunction R) ·), -/
/-       divisors_prime_pow hp_prime, sum_map] -/
/-     simp -/
/-     rw [cast_sub hp_prime.one_le, cast_one, mul_sub, mul_one, mul_comm, ← _root_.pow_succ, -/
/-       Nat.sub_add_cancel hk_pos] -/
/-     calc ∑ x in range (k + 1), (μ (p ^ x) : R) * (p ^ k / p ^ x : R) -/
/-       _ = (μ (p ^ 0) : R) * (p ^ (k - 0) : R) + (μ (p ^ 1) : R) * (p ^ (k - 1) : R) + -/
/-           ∑ x in Icc 2 k, (μ (p ^ x) : R) * (p ^ k / p ^ x : R) := by -/
/-         rw [range_eq_Ico, ← Ico_insert_succ_left, sum_insert, ← Ico_insert_succ_left, sum_insert, -/
/-           Ico_succ_right] -/
/-         · simp [add_assoc] -/
/-           nth_rw 1 [← Nat.sub_add_cancel hk_pos, pow_add, pow_one, -/
/-             Nat.mul_div_cancel _ hp_prime.pos, cast_pow] -/
/-         all_goals simp [mem_Ico, hk_pos] -/
/-       _ = (μ (p ^ 0) : R) * (p ^ (k - 0) : R) + (μ (p ^ 1) : R) * (p ^ (k - 1) : R) := by -/
/-         rw [add_right_eq_self] -/
/-         refine sum_eq_zero fun d hd ↦ ?_ -/
/-         rw [mem_Icc] at hd -/
/-         simp [moebius_apply_prime_pow hp_prime (by omega : d ≠ 0)] -/
/-         exact fun hd' ↦ by omega -/
/-       _ = p ^ k - p ^ (k - 1) := by -/
/-         simp [moebius_apply_prime hp_prime, ← sub_eq_add_neg] -/
/-   | h0 => simp -/
/-   | h1 => simp -/
/-   | h m n _ _ hmn hm' hn' => -/
/-     have : IsMultiplicative ((μ : ArithmeticFunction R) * (id : ArithmeticFunction R)) := by -/
/-       arith_mult -/
/-     rw [this.right hmn, hm', hn', isMultiplicative_totient.right hmn] -/
/-  -/
end missing

/- ------------------------------------------------------------ -/

section defining_inverse

open Nat Finset BigOperators

variable {f : ArithmeticFunction R}

noncomputable def inv_leading (f : ArithmeticFunction R) : R :=
  if hf : IsUnit (f 1) then (hf.unit⁻¹ :) else 0

theorem inv_leading_def (f : ArithmeticFunction R) :
    f.inv_leading = if hf : IsUnit (f 1) then ((hf.unit⁻¹ : Rˣ) : R) else 0 := by
  rfl

theorem inv_leading_isUnit (hf : IsUnit (f 1)) : f.inv_leading = hf.unit⁻¹ := by
  simp [inv_leading, hf]

theorem inv_leading_not_isUnit (hf : ¬IsUnit (f 1)) : f.inv_leading = 0 := by
  simp [inv_leading, hf]

noncomputable def invFun (f : ArithmeticFunction R) : ℕ → R
| 0 => 0
| 1 => f.inv_leading
| n => -f.inv_leading * ∑ d in n.properDivisors.attach,
    have := Nat.mem_properDivisors.mp d.prop; f (n / d) * invFun f d
decreasing_by simp_wf; exact this.right

@[simp]
theorem invFun_map_zero : f.invFun 0 = 0 := rfl

@[simp]
theorem invFun_map_one : f.invFun 1 = f.inv_leading := rfl

theorem invFun_map {n : ℕ} : f.invFun n = if n = 0 then 0 else if n = 1 then f.inv_leading else
    -f.inv_leading * ∑ d in n.properDivisors, f (n / d) * f.invFun d := by
  split_ifs with hn₀ hn₁
  · subst hn₀; rfl
  · subst hn₁; rfl
  · simp [invFun, sum_attach _ fun x ↦ f (n / x) * f.invFun x]

noncomputable instance : Inv (ArithmeticFunction R) where
  inv := fun f ↦ ⟨f.invFun, rfl⟩

@[simp]
theorem inv_def : f⁻¹ = ⟨f.invFun, rfl⟩ := by rfl

/- We prove this as early as possible, then use `IsUnit` from here on -/
/- This is also why we don't mark this as @[simp] -/
theorem isUnit_iff : IsUnit f ↔ IsUnit (f 1) := by
  constructor <;> intro hf
  · obtain ⟨⟨f, f_inv, mul_inv, inv_mul⟩, rfl⟩ := hf
    have : (f * f_inv) 1 = 1 := by simp [mul_inv]
    simp [mul_apply, sum_divisorsAntidiagonal (f · * f_inv ·)] at this
    have : IsUnit (f 1 * f_inv 1) := by rw [this]; exact isUnit_one
    simp [((Commute.all _ _).isUnit_mul_iff.mp this).left]
  · have : f * f⁻¹ = 1 := by
      ext n
      match n with
      | 0 => simp
      | 1 => simp [inv_leading, inv_def, hf]
      | .succ (.succ n) =>
        rw [mul_apply, sum_divisorsAntidiagonal' (f · * f⁻¹ ·), ← cons_self_properDivisors,
          Finset.sum_cons, Nat.div_self, f.inv_def, coe_mk, invFun, ← mul_assoc, mul_neg,
          sum_attach (n + 2).properDivisors fun d ↦ f (_ / d) * f.invFun d]
        all_goals simp [inv_leading, hf]
    exact ⟨⟨f, f⁻¹, this, (mul_comm _ _).trans this⟩, by rfl⟩

instance [Decidable (IsUnit (f 1))] : Decidable (IsUnit f) := by rw [isUnit_iff]; infer_instance

/- We mark this as simp instead of inv_leading_def because IsUnit is more useful -/
@[simp]
theorem inv_leading_def' (f : ArithmeticFunction R) :
    f.inv_leading = if hf : IsUnit f then (((isUnit_iff.mp hf).unit⁻¹ : Rˣ) : R) else 0 := by
  simp_rw [isUnit_iff]
  rfl

/- We duplicate lemmas from above to use IsUnit instead -/
theorem inv_leading_isUnit' (hf : IsUnit f) : f.inv_leading = (isUnit_iff.mp hf).unit⁻¹ := by
  simp [inv_leading, hf]

theorem inv_leading_not_isUnit' (hf : ¬IsUnit f) : f.inv_leading = 0 := by
  simp [inv_leading, hf]


end defining_inverse

/- ------------------------------------------------------------ -/

section invertible_lemmas

variable {f : ArithmeticFunction R} (hf : IsUnit f)

open Nat Finset BigOperators ArithmeticFunction

@[simp]
theorem inv_map_one : f⁻¹ 1 = f.inv_leading := by simp [hf]

theorem inv_map_two_le {n : ℕ} (hn : 2 ≤ n) :
    f⁻¹ n = -f.inv_leading * ∑ d in n.properDivisors, f (n / d) * f⁻¹ d := by
  simp [hf]
  rw [invFun, sum_attach _ fun x ↦ f (n / x) * f.invFun x, neg_mul, inv_leading_isUnit]
  all_goals intro hn'; subst hn'; trivial


theorem inv_map_def_two_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ d in n.divisors, f (n / d) * f⁻¹ d = 0 := by
  rw [← cons_self_properDivisors, Finset.sum_cons, Nat.div_self, f.inv_map_two_le hf hn,
    ← mul_assoc, mul_neg]
  simp [inv_leading_isUnit', hf]
  all_goals omega

@[simp]
/- How to name this -/
theorem inv_mul_inv_invertible {g : ArithmeticFunction R} :
    (f * g)⁻¹ = f⁻¹ * g⁻¹ := by
  sorry

end invertible_lemmas

/- ------------------------------------------------------------ -/
/- ----------------EVERYTHING BELOW IS NOT FIXED--------------- -/
/- ------------------------------------------------------------ -/

/- Everything here applies for any ArithmeticFunction -/
section general_lemmas

variable {f : ArithmeticFunction R} [DecidablePred (@IsUnit R _)]

open Nat Finset BigOperators ArithmeticFunction

@[simp]
theorem inv_inv : f⁻¹⁻¹ = f := by
  by_cases hf : invertible f
  · rw [inv_eq_iff (invertible_inv_iff.mp hf), inv_mul hf]
  · simp [hf]

/- This is false when f or g are not both invertible or both non invertible -/
/- theorem inv_mul_inv {g : ArithmeticFunction R} : -/
/-     (f * g)⁻¹ = f⁻¹ * g⁻¹ := by -/
/-   by_cases hf : invertible f <;> by_cases hg : invertible g -/
/-   · rw [inv_eq_iff $ invertible_mul_iff.mp ⟨hf, hg⟩, ← mul_assoc, mul_assoc f, mul_comm g, -/
/-       ← mul_assoc, mul_inv hf, one_mul, mul_inv hg] -/
/-   all_goals -/
/-     have h : ¬invertible (f * g) := invertible_mul_iff.not.mp (by tauto) -/
/-     rw [inv_def_not_invertible h] -/

end general_lemmas

/- ------------------------------------------------------------ -/

section section_dedicated_to_Yael

open Nat ArithmeticFunction

variable [DecidablePred (@IsUnit R _)]

/- Proving Yaël's bonus point, which is False as stated -/
instance : DivisionMonoid (ArithmeticFunction R) where
  inv := (·)⁻¹
  inv_inv := fun _ ↦ inv_inv
  mul_inv_rev := fun f g ↦ by
    by_cases hf : invertible f <;> by_cases hg : invertible g
    · rw [inv_eq_iff $ invertible_mul_iff.mp ⟨hf, hg⟩, mul_assoc, ← mul_assoc g, mul_inv hg,
        one_mul, mul_inv hf]
    · sorry -- this case is false
    · sorry -- this case is false
    · have : ¬invertible (g * f) := invertible_mul_iff.not.mp (by tauto)
      rw [mul_comm]
      iterate 3 rw [inv_def_not_invertible (by tauto)]
  inv_eq_of_mul := fun f g h ↦ by
    by_cases hf : invertible f
    · rwa [inv_eq_iff hf]
    · sorry -- this case is false

end section_dedicated_to_Yael

/- ------------------------------------------------------------ -/

section mkUnit_IsMultiplicative

variable (f : ArithmeticFunction R)

namespace IsMultiplicative

theorem isUnit (hf : IsMultiplicative f) : IsUnit f := by
  rw [isUnit_iff]

/- This fails because of the TODO above -/
def mkUnit (hf' : IsMultiplicative f) : (ArithmeticFunction R)ˣ :=
  ArithmeticFunction.mkUnit hf

end IsMultiplicative

end mkUnit_IsMultiplicative

/- ------------------------------------------------------------ -/

section invertible_instances

theorem invertible_zeta : invertible ζ := by
  sorry
instance : Invertible ((ζ : ArithmeticFunction R) 1) := by
  simp
  exact invertibleOne

instance : Invertible ((id : ArithmeticFunction R) 1) := by
  simp
  exact invertibleOne

instance {k : ℕ} : Invertible ((pow k : ArithmeticFunction R) 1) := by
  simp
  exact invertibleOne

instance {k : ℕ} : Invertible ((σ k : ArithmeticFunction R) 1) := by
  simp [sigma_apply]
  exact invertibleOne

instance : Invertible ((μ : ArithmeticFunction R) 1) := by
  simp [sigma_apply]
  exact invertibleOne

instance : Invertible ((φ : ArithmeticFunction R) 1) := by
  simp [totient_apply]
  exact invertibleOne

end invertible_instances

/- ------------------------------------------------------------ -/

section IsCompletelyMultiplicative_defn

variable (f : ArithmeticFunction R)

def IsCompletelyMultiplicative := f 1 = 1 ∧ ∀ m n, f (m * n) = f m * f n

instance [hf : Fact (IsCompletelyMultiplicative f)] : Invertible (f 1) := by
  rw [hf.out.left]
  exact invertibleOne

end IsCompletelyMultiplicative_defn

/- ------------------------------------------------------------ -/

section IsCompletelyMultiplicative_lemmas

namespace IsCompletelyMultiplicative

open Nat Finset BigOperators ArithmeticFunction IsMultiplicative

variable {f : ArithmeticFunction R} (hf : IsCompletelyMultiplicative f)

theorem isMultiplicative : IsMultiplicative f := by
  refine ⟨hf.left, @fun m n _ ↦ hf.right m n⟩

theorem map_one : f 1 = 1 := hf.left

theorem map_mul (m n : ℕ) : f (m * n) = f m * f n := hf.right m n

def mkUnit : (ArithmeticFunction R)ˣ :=
  have := Fact.mk hf; ArithmeticFunction.mkUnit f

/- Important theorem that I don't know where to put -/
/- Actually this is an if and only if, but we can use a magic word: -/
/- TODO: Prove ↔ directions -/
theorem mkUnit_eq : hf.mkUnit⁻¹ = pmul (μ : ArithmeticFunction R) f := by
  have := Fact.mk hf
  rw [mkUnit, mkUnit_inv_eq_inv, inv_eq_iff, mul_comm]
  ext n
  rw [mul_apply, sum_divisorsAntidiagonal ((pmul (μ : ArithmeticFunction R) f) · * f ·)]
  trans ∑ d in n.divisors, (μ d) * f n
  · apply sum_congr rfl fun d hd ↦ ?_
    rw [pmul_apply, mul_assoc, ← hf.right, ← Nat.mul_div_assoc _ (mem_divisors.mp hd).left,
      Nat.mul_div_cancel_left, intCoe_apply]
    rw [mem_divisors] at hd
    exact Nat.pos_of_ne_zero $ ne_zero_of_dvd_ne_zero hd.right hd.left
  · rw [← sum_mul, ← Int.cast_sum, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply, one_apply]
    split_ifs with hn <;> simp [hn, hf.left]

end IsCompletelyMultiplicative

end IsCompletelyMultiplicative_lemmas

/- ------------------------------------------------------------ -/

section IsCompletelyMultiplicative_examples

namespace IsCompletelyMultiplicative

/- Wow so exciting!!! -/
theorem isCompletelyMultiplicative_id : IsCompletelyMultiplicative (id : ArithmeticFunction R) :=
  ⟨by simp, by simp⟩

end IsCompletelyMultiplicative

end IsCompletelyMultiplicative_examples

/- ------------------------------------------------------------ -/

section inv_examples

open ArithmeticFunction IsCompletelyMultiplicative

lemma inv_zeta : (ζ : ArithmeticFunction R).inv = (μ : ArithmeticFunction R) := by
  rw [inv_eq_iff, coe_zeta_mul_coe_moebius]

lemma inv_moebius : (μ : ArithmeticFunction R).inv = (ζ : ArithmeticFunction R) := by
  rw [inv_eq_iff, coe_moebius_mul_coe_zeta]

/- New result 1!! -/
lemma inv_id : (id : ArithmeticFunction R).inv = pmul (μ : ArithmeticFunction R) id := by
  rw [← isCompletelyMultiplicative_id.mkUnit_eq, ← mkUnit_inv_eq_inv]
  rfl

/- New result 2!! -/
lemma inv_toeitn :
    (φ : ArithmeticFunction R).inv
      = (ζ : ArithmeticFunction R) * (pmul (μ : ArithmeticFunction R) id) := by
  have h₁ := coe_moebius_mul_coe_id (R := R)
  have h₂ := inv_mul_inv (μ : ArithmeticFunction R) id
  /- Not sure why I can't rw [h₁] at h₂, I get motive errors... -/
  have : (φ).inv = (μ : ArithmeticFunction R).inv * (id : ArithmeticFunction R).inv := by
    convert h₂
    convert h₁.symm
  convert this
  · exact inv_moebius.symm
  · convert inv_id.symm

end inv_examples

/- ------------------------------------------------------------ -/

section deriv

variable (f g h : ArithmeticFunction ℝ)

@[simp] noncomputable def deriv : ArithmeticFunction ℝ := pmul f log

theorem deriv_add : (f + g).deriv = f.deriv + g.deriv := by ext n; simp; ring

theorem deriv_mul : (f * g).deriv = f.deriv * g + f * g.deriv := by
  simp
