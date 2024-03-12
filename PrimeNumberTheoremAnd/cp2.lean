import Mathlib.NumberTheory.VonMangoldt

namespace ArithmeticFunction

/- TODO: Is CommRing necessary -/
variable {R : Type*} [CommRing R]

/- ------------------------------------------------------------ -/

section missing

open Nat

/- This and a few more are missing. I'm just following Apostol. -/
@[simp]
def totient : ArithmeticFunction R := ⟨fun d ↦ φ d, by simp⟩

theorem totient_apply {n : ℕ} : (totient : ArithmeticFunction R) n = φ n := rfl

theorem isMultiplicative_totient : IsMultiplicative (totient : ArithmeticFunction R) :=
  ⟨by simp, fun h ↦ by simp [totient_mul h]⟩

scoped[ArithmeticFunction] notation "φ" => totient

scoped[ArithmeticFunction.Totient] notation "φ" => totient

theorem coe_moebius_mul_coe_id : (μ : ArithmeticFunction R) * id = (φ : ArithmeticFunction R) := by
  sorry

end missing

/- ------------------------------------------------------------ -/

section mkUnit


open Nat Finset BigOperators

instance {f g : ArithmeticFunction R}
    [Invertible (f 1)] [Invertible (g 1)] : Invertible ((f * g) 1) := by
  simp [mul_apply]
  apply invertibleMul

variable (f : ArithmeticFunction R) [hf : Invertible (f 1)]

@[simp]
def invFun : ℕ → R
| 0 => 0
| 1 => ⅟(f 1)
| n => -⅟(f 1) * ∑ d in n.properDivisors.attach,
    have := Nat.mem_properDivisors.mp d.prop; f (n / d) * invFun d
decreasing_by simp_wf; exact this.right

@[simp]
def inv : ArithmeticFunction R := ⟨f.invFun, rfl⟩

@[simp]
theorem inv_map_one : f.inv 1 = ⅟(f 1) := by simp

theorem inv_map_two_le {n : ℕ} (hn : 2 ≤ n) :
    f.inv n = -⅟(f 1) * ∑ d in n.properDivisors, f (n / d) * f.inv d := by
  rw [inv, coe_mk, invFun, sum_attach _ fun x ↦ f (n / x) * f.invFun x]
  all_goals intro hn'; subst hn'; trivial

theorem inv_map {n : ℕ} :
    f.inv n = if n = 0 then 0 else if n = 1 then ⅟(f 1) else
      -⅟(f 1) * ∑ d in n.properDivisors, f (n / d) * f.inv d := by
  split_ifs with hn₀ hn₁
  · subst hn₀; rfl
  · subst hn₁; rfl
  · rw [inv, coe_mk, invFun, sum_attach _ fun x ↦ f (n / x) * f.invFun x]
    all_goals intro hn'; tauto

theorem inv_map_def_two_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ d in n.divisors, f (n / d) * f.inv d = 0 := by
  rw [← cons_self_properDivisors, Finset.sum_cons, Nat.div_self, f.inv_map_two_le hn, ← mul_assoc,
    mul_neg, mul_invOf_self, neg_one_mul, neg_add_self]
  all_goals omega

theorem mul_inv : f * f.inv = 1 := by
  ext n
  by_cases hn₀ : n = 0
  · subst hn₀; rfl
  · rw [mul_apply, sum_divisorsAntidiagonal' (f · * f.inv ·), ← cons_self_properDivisors,
      Finset.sum_cons, Nat.div_self, f.inv_map]
    simp only [hn₀, if_false]
    split_ifs with hn₁
    · subst hn₁; simp
    · simp [hn₀, one_apply, hn₁]
    all_goals omega

theorem inv_mul : f.inv * f = 1 := (mul_comm _ _).trans f.mul_inv

/- This is to help prove that a defined function *is* an inverse -/
theorem inv_eq_iff {g : ArithmeticFunction R} : f.inv = g ↔ f * g = 1 := by
  constructor <;> intro h
  · rw [← h, mul_inv]
  · apply_fun (f.inv * ·) at h
    rwa [mul_one, ← mul_assoc, inv_mul, one_mul, eq_comm] at h

theorem inv_mul_inv (g : ArithmeticFunction R) [Invertible (g 1)] :
    (f * g).inv = f.inv * g.inv := by
  sorry

def mkUnit : (ArithmeticFunction R)ˣ := ⟨f, f.inv, f.mul_inv, f.inv_mul⟩

theorem mkUnit_inv_eq_inv : f.mkUnit⁻¹ = f.inv := rfl

end mkUnit

/- ------------------------------------------------------------ -/

section mkUnit_IsMultiplicative

variable (f : ArithmeticFunction R)

namespace IsMultiplicative

instance [hf : Fact (IsMultiplicative f)] : Invertible (f 1) := by
  rw [hf.out.map_one]
  exact invertibleOne

def mkUnit (hf' : IsMultiplicative f) : (ArithmeticFunction R)ˣ :=
  have := Fact.mk hf'; ArithmeticFunction.mkUnit f

end IsMultiplicative

end mkUnit_IsMultiplicative

/- ------------------------------------------------------------ -/

section invertible_instances

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
/- Actually this is an if and only iff, but we can use a magic word: -/
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

example : IsMultiplicative (ζ : ArithmeticFunction R) :=
  ⟨by simp, @fun m n h ↦ by
    simp only [natCoe_apply]; rw [isMultiplicative_zeta.right h, Nat.cast_mul]⟩
