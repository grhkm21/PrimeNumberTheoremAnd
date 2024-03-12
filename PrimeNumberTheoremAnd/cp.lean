import PrimeNumberTheoremAnd.Std.Data.Nat.Gcd
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.VonMangoldt

set_option autoImplicit false

open Nat hiding log
open BigOperators Squarefree ArithmeticFunction Finset IsPrimePow

def Nat.Coprime.mul_divisors_equiv {m n : ℕ} (h : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n).divisors ≃ m.divisors ×ˢ n.divisors where
  toFun := fun ⟨d, _⟩ ↦ by
    /- A nicer to work with version of `prod_dvd_and_dvd_of_dvd_prod` -/
    refine ⟨⟨d.gcd m, d.gcd n⟩, ?_⟩
    simp only [mem_product, mem_divisors, gcd_dvd_right, true_and]
    exact ⟨hm, hn⟩
  invFun := fun ⟨⟨dm, dn⟩, hd⟩ ↦ by
    refine ⟨dm * dn, ?_⟩
    rw [mem_product, mem_divisors, mem_divisors] at hd
    rw [mem_divisors, mul_ne_zero_iff]
    exact ⟨mul_dvd_mul hd.left.left hd.right.left, hm, hn⟩
  left_inv := fun d ↦ by
    simp [← Coprime.gcd_mul _ h, gcd_eq_left $ (mem_divisors.mp d.prop).left]
  right_inv := fun d ↦ by
    have hm' := dvd_of_mem_divisors (mem_product.mp d.prop).left
    have hn' := dvd_of_mem_divisors (mem_product.mp d.prop).right
    have := Coprime.coprime_dvd_left_dvd_right hm' hn' h
    ext <;> simp
    · rw [gcd_comm, Coprime.gcd_mul _ this]
      rw [gcd_eq_right hm', h.coprime_dvd_right hn', mul_one]
    · rw [gcd_comm, Coprime.gcd_mul _ this]
      rw [h.symm.coprime_dvd_right hm', gcd_eq_right hn', one_mul]

theorem IsPrimePow.eq_of_dvd_dvd {p q n : ℕ}
    (hn : IsPrimePow n) (hp' : p.Prime) (hq' : q.Prime) (hp : p ∣ n) (hq : q ∣ n) : p = q := by
  obtain ⟨r, k, hr, hk, rfl⟩ := hn
  rw [← prime_iff] at hr
  rw [dvd_prime_pow hr] at hp hq
  have : p = r := by obtain ⟨k', _, rfl⟩ := hp; exact hr.pow_eq_iff.mpr ⟨rfl, hp'.eq_one_of_pow⟩
  have : q = r := by obtain ⟨k', _, rfl⟩ := hq; exact hr.pow_eq_iff.mpr ⟨rfl, hq'.eq_one_of_pow⟩
  simp [*]

lemma not_isPrimePow_iff_exists_primes_dvd {n : ℕ} (hn : 1 < n) :
    ¬IsPrimePow n ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n := by
  constructor
  · intro h
    rw [isPrimePow_iff_minFac_pow_factorization_eq (by linarith)] at h
    let p := n.minFac
    have hp₁ := minFac_prime hn.ne.symm
    have hp₂ := minFac_dvd n
    let v := n.factorization p
    have hv : p ^ v ∣ n := ord_proj_dvd n _
    let q := (ord_compl[p] n).minFac
    have : ord_compl[p] n ≠ 1 := fun h' ↦ h (eq_of_dvd_of_div_eq_one hv h')
    have hq₁ := minFac_prime this
    have hq₂ := minFac_dvd (n / p)
    use p, q, hp₁, hq₁, ?_, hp₂, (n / q)
    · refine Nat.eq_mul_of_div_eq_right ?_ rfl
      trans ord_compl[p] n
      · exact minFac_dvd _
      · exact ord_compl_dvd n p
    · by_contra!
      simp only at this hq₂
      have : n.minFac ∣ n / n.minFac ^ n.factorization n.minFac := by
        nth_rw 1 [this]
        apply minFac_dvd
      exact (pow_succ_factorization_not_dvd (by linarith) hp₁) $ mul_dvd_of_dvd_div hv this
  · intro ⟨p, q, hp_prime, hq_prime, hpq, hp, hq⟩
    by_contra!
    exact hpq $ this.eq_of_dvd_dvd hp_prime hq_prime hp hq

lemma Squarefree.dvd_self_div_of_sq_dvd {p n d : ℕ}
    (hd : Squarefree d) (hp : p ^ 2 ∣ n) (hd' : d ∣ n) : p ∣ n / d := by
  by_cases hp' : p = 1
  /- Simple case -/
  · simp only [hp', one_dvd]
  /- The other case -/
  obtain ⟨n', hn'⟩ := hp
  subst hn'
  by_cases hd' : d ∣ p * n'
  · use (p * n' / d)
    rw [← Nat.mul_div_assoc _ hd', ← mul_assoc, sq]
  · exfalso
    apply hd'; clear hd'
    obtain ⟨d1, d2, h1, h2, rfl⟩:= Nat.dvd_mul.mp hd'
    apply mul_dvd_mul ?_ h2
    rwa [← Squarefree.dvd_pow_iff_dvd hd.of_mul_left two_ne_zero]

/- TODO: Name this properly -/
lemma IsPrimePow.isPrimePow_mul_asdf {a b : ℕ}
    (h : IsPrimePow (a * b)) (h' : Coprime a b) : a = 1 ∨ b = 1 := by
  by_contra!
  obtain ⟨p, k, hp_prime, hk_pos, h⟩ := h
  rw [← prime_iff] at hp_prime
  obtain ⟨ka, _, rfl⟩ := (Nat.dvd_prime_pow hp_prime).mp ⟨b, h⟩
  obtain ⟨kb, _, rfl⟩ := (Nat.dvd_prime_pow hp_prime).mp $ dvd_iff_exists_eq_mul_left.mpr ⟨_, h⟩
  rw [coprime_pow_left_iff, coprime_pow_right_iff, coprime_self] at h'
  · exact hp_prime.ne_one h'
  · have := this.right
    contrapose! this
    rw [nonpos_iff_eq_zero.mp this, Nat.pow_zero]
  · have := this.left
    contrapose! this
    rw [nonpos_iff_eq_zero.mp this, Nat.pow_zero]


lemma ArithmeticFunction.mul_prime_pow_apply {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (f * g) (p ^ n) = ∑ k in Finset.Icc 0 n, f (p ^ k) * g (p ^ (n - k)) := by
  simp [sum_divisorsAntidiagonal (f · * g ·), divisors_prime_pow hp]
  rw [range_eq_Ico, Ico_succ_right]
  exact sum_congr rfl fun d hd ↦ by rw [Nat.pow_div (mem_Icc.mp hd).right hp.pos]

lemma Nat.Coprime.divisors_inter_eq {m n : ℕ} (hmn : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
    m.divisors ∩ n.divisors = {1} := by
  ext d
  simp only [mem_inter, mem_divisors, ne_eq, mem_singleton]
  constructor
  · rintro ⟨⟨hdm, _⟩, hdn, _⟩
    exact Nat.eq_one_of_dvd_coprimes hmn hdm hdn
  · rintro rfl
    exact ⟨⟨one_dvd _, hm⟩, ⟨one_dvd _, hn⟩⟩

lemma not_isPrimePow {m n d : ℕ} (hmn : m.Coprime n) (hd : d ∣ m * n) (hdm : ¬d ∣ m) (hdn : ¬d ∣ n) :
    ¬IsPrimePow d := by
  by_contra! hd_pp
  obtain ⟨p, k, hp_prime, hk_pos, rfl⟩ := hd_pp
  rw [← prime_iff] at hp_prime
  have hm : m ≠ 0 := by contrapose! hdm; subst hdm; exact dvd_zero _
  have hn : n ≠ 0 := by contrapose! hdn; subst hdn; exact dvd_zero _
  rw [hp_prime.pow_dvd_iff_le_factorization] at hdm hdn <;> try assumption
  have h : m.factorization p = 0 ∨ n.factorization p = 0 := by
    by_contra!
    have : p ∣ m.gcd n := dvd_gcd_iff.mpr ⟨?_, ?_⟩
    rw [hmn, dvd_one] at this
    exact hp_prime.ne_one this
    all_goals apply dvd_of_factorization_pos; tauto
  rw [hp_prime.pow_dvd_iff_le_factorization $ mul_ne_zero_iff.mpr ⟨hm, hn⟩,
    Nat.factorization_mul hm hn, Finsupp.coe_add, Pi.add_apply] at hd
  cases h <;> linarith

example {n : ℕ} : (Λ * μ) n = -μ n * log n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | hp p n hp_prime hn_pos =>
    simp_rw [mul_comm Λ _, mul_prime_pow_apply _ _ _ hp_prime, intCoe_apply]
    by_cases hn : n = 1
    · simp [show Icc 0 1 = {0, 1} by rfl, hn, Nat.div_self hp_prime.pos,
        moebius_apply_prime hp_prime, vonMangoldt_apply_prime hp_prime]
    · trans ∑ x in Finset.range 2, μ (p ^ x) * Λ (p ^ (n - x))
      · refine (sum_subset (fun d hd ↦ ?_) fun d _ hd ↦ ?_).symm
        · simp at hd ⊢; omega
        · have : 2 ≤ d := le_of_not_lt $ mem_range.not.mp hd
          rw [moebius_apply_prime_pow hp_prime (by omega)]
          simp [show d ≠ 1 by omega]
      · simp [sum_range, moebius_apply_prime hp_prime]
        rw [vonMangoldt_apply_pow, vonMangoldt_apply_pow, add_neg_self,
          moebius_apply_prime_pow hp_prime]
        all_goals simp [hn]; try omega
  | h0 => simp
  | h1 => simp
  | h a b ha hb hab ha' hb' =>
    have ha₀ : a ≠ 0 := by omega
    have hb₀ : b ≠ 0 := by omega
    calc (Λ * μ) (a * b)
    _ = ∑ d in (a * b).divisors, Λ d * μ (a * b / d) := by
      erw [mul_apply, sum_divisorsAntidiagonal (Λ · * μ ·)]
    _ = ∑ d in a.divisors ∪ b.divisors, Λ d * μ (a * b / d)
        + ∑ d in a.divisors ∩ b.divisors, Λ d * μ (a * b / d) := by
      simp [hab.divisors_inter_eq ha₀ hb₀]
      refine (sum_subset ?_ fun d hd hd' ↦ ?_).symm
      · apply union_subset <;> apply divisors_subset_of_dvd (mul_ne_zero ha₀ hb₀) (by simp)
      · simp [mem_divisors] at hd hd'
        apply mul_eq_zero_of_left (vonMangoldt_eq_zero_iff.mpr $ not_isPrimePow hab ?_ ?_ ?_)
        all_goals tauto
    _ = μ b * ∑ d in a.divisors, Λ d * μ (a / d) + μ a * ∑ d in b.divisors, Λ d * μ (b / d) := by
      rw [sum_union_inter, mul_sum, mul_sum]
      congr 1 <;> apply sum_congr rfl fun d hd ↦ ?_
      · have hd_dvd := (mem_divisors.mp hd).left
        rw [mul_comm a b, Nat.mul_div_assoc _ hd_dvd, isMultiplicative_moebius.right, Int.cast_mul]
        ring_nf
        exact hab.symm.coprime_dvd_right ⟨d, (Nat.div_mul_cancel hd_dvd).symm⟩
      · have hd_dvd := (mem_divisors.mp hd).left
        rw [Nat.mul_div_assoc _ hd_dvd, isMultiplicative_moebius.right, Int.cast_mul]
        ring_nf
        exact hab.coprime_dvd_right ⟨d, (Nat.div_mul_cancel hd_dvd).symm⟩
    _ = μ b * (Λ * μ) a + μ a * (Λ * μ) b := by
      simp_rw [mul_apply, intCoe_apply, sum_divisorsAntidiagonal (Λ · * μ ·)]
    _ = -μ (a * b) * log (a * b) := by
      rw [ha', hb', ← mul_assoc, ← mul_assoc, mul_neg, mul_neg,
        isMultiplicative_moebius.right hab, mul_comm (μ b : ℝ) (μ a : ℝ), ← mul_add,
        @log_apply (a * b), cast_mul, Real.log_mul]
      norm_cast
      all_goals exact cast_ne_zero.mpr (by omega)
