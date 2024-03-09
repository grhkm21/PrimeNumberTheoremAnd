import PrimeNumberTheoremAnd.Std.Data.Nat.Gcd
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.VonMangoldt

open Nat hiding log
open BigOperators Squarefree ArithmeticFunction Finset

lemma mul_coprime_divisors_equiv {m n : ℕ} (h : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n).divisors ≃ m.divisors ×ˢ n.divisors where
  toFun := fun ⟨d, _⟩ ↦ by
    /- A nicer to work with version of `prod_dvd_and_dvd_of_dvd_prod` -/
    refine ⟨⟨d.gcd m, d.gcd n⟩, ?_⟩
    simp only [mem_product, mem_divisors, Nat.gcd_dvd_right, true_and]
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
    · rw [Nat.gcd_comm, Coprime.gcd_mul _ this]
      rw [Nat.gcd_eq_right hm', h.coprime_dvd_right hn', mul_one]
    · rw [Nat.gcd_comm, Coprime.gcd_mul _ this]
      rw [h.symm.coprime_dvd_right hm', Nat.gcd_eq_right hn', one_mul]

lemma IsPrimePow.eq_of_dvd_dvd {p q n : ℕ}
    (hn : IsPrimePow n) (hp' : p.Prime) (hq' : q.Prime) (hp : p ∣ n) (hq : q ∣ n) : p = q := by
  obtain ⟨r, k, hr, hk, rfl⟩ := hn
  rw [← prime_iff] at hr
  rw [Nat.dvd_prime_pow hr] at hp hq
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

set_option push_neg.use_distrib true
example {n : ℕ} : (μ * Λ) n = -μ n * log n := by
  /- case on n = 0 -/
  rcases Nat.eq_zero_or_pos n with rfl | hn₀
  · simp only [ArithmeticFunction.map_zero, mul_zero]
  /- remaining case -/
  by_cases hn : Squarefree n
  · sorry
  /- · have h_id₁ {d : ℕ} (hd : d ∈ n.divisors) : μ n = μ d * μ (n / d) := by -/
  /-     have := Nat.mul_div_cancel' $ dvd_of_mem_divisors hd -/
  /-     rw [← (isMultiplicative_moebius).right, this] -/
  /-     exact Nat.coprime_of_squarefree_mul (this.symm ▸ hn) -/
  /-   have h_id₂ {d : ℕ} (hd : d ∈ n.divisors) : μ d * Λ d = -Λ d := by -/
  /-     by_cases hd : IsPrimePow d -/
  /-     · obtain ⟨p, k, ⟨hp, hd'⟩⟩ := hd -/
  /-       rw [← Nat.prime_iff] at hp -/
  /-       rw [← hd'.right, moebius_apply_prime_pow hp $ Nat.pos_iff_ne_zero.mp hd'.left] -/
  /-       split_ifs with hk -/
  /-       · norm_num -/
  /-       · have : Squarefree _ := hd'.right.symm ▸ squarefree_of_dvd (dvd_of_mem_divisors hd) hn -/
  /-         have : k = 0 ∨ k = 1 := eq_zero_or_one_of_pow_of_not_isUnit this hp.not_unit -/
  /-         omega -/
  /-     · simp only [vonMangoldt_apply, hd, if_false, mul_zero, neg_zero] -/
  /-   symm -/
  /-   rw [neg_mul, neg_eq_iff_eq_neg] -/
  /-   /- My first long calc proof! -/ -/
  /-   calc μ n * log n -/
  /-     _ = ∑ d in n.divisors, Λ d * μ n := by -/
  /-       rw [← sum_mul, vonMangoldt_sum, mul_comm] ; rfl -/
  /-     _ = ∑ d in n.divisors, Λ (n / d) * μ n := by -/
  /-       rw [← sum_div_divisors] -/
  /-     _ = ∑ d in n.divisors, Λ (n / d) * μ (n / d) * μ d := by -/
  /-       refine sum_congr rfl (fun d hd ↦ ?_) -/
  /-       rw [h_id₁ hd, mul_assoc, mul_comm (μ d)] -/
  /-       norm_cast -/
  /-     _ = -∑ d in n.divisors, Λ (n / d) * μ d := by -/
  /-       rw [← sum_neg_distrib] -/
  /-       refine sum_congr rfl (fun d hd ↦ ?_) -/
  /-       have hd' : n / d ∈ n.divisors := by -/
  /-         rw [mem_divisors] at hd ⊢ -/
  /-         exact ⟨div_dvd_of_dvd hd.left, hd.right⟩ -/
  /-       rw [mul_comm (Λ _), h_id₂ hd', neg_mul] -/
  /-     _ = -∑ d in n.divisors, μ d * Λ (n / d) := by -/
  /-       simp_rw [mul_comm] -/
  /-     _ = -(μ * Λ) n := by -/
  /-       rw [mul_apply, ← map_div_right_divisors, sum_map, Function.Embedding.coeFn_mk] -/
  /-       rfl -/
  · simp only [mul_apply, ← map_div_right_divisors, sum_map, Function.Embedding.coeFn_mk]
    rw [moebius_eq_zero_of_not_squarefree hn, Int.cast_zero, neg_zero, zero_mul]
    trans ∑ d in n.divisors.filter fun d ↦ Squarefree d ∧ IsPrimePow (n / d), μ d * Λ (n / d)
    · rw [← sum_filter_ne_zero]
      refine sum_congr ?_ (fun _ _ ↦ rfl)
      congr ; ext d
      rw [mul_ne_zero_iff]
      simp [moebius_ne_zero_iff_squarefree, vonMangoldt_eq_zero_iff]
    · obtain ⟨a, b, ha, hb, rfl, ha'⟩ := sq_mul_squarefree_of_pos hn₀
      replace hb : 1 < b := by
        contrapose! hn
        rcases (show b = 1 by omega) with rfl
        rwa [one_pow, one_mul]
      clear hn
      by_cases hb' : IsPrimePow b
      · sorry
      · apply sum_congr (s₂ := ∅) ?_ (fun _ _ ↦ rfl)
        ext d
        simp only [not_mem_empty, iff_false, mem_filter, not_and, mem_divisors]
        intro hd_dvd hd_sqf
        obtain ⟨p, q, hp, hq, hpq, hpb, hqb⟩ := (not_isPrimePow_iff_exists_primes_dvd hb).mp hb'
        obtain ⟨b', rfl⟩ := Prime.dvd_mul_of_dvd_ne hpq hp hq hpb hqb
        have : ¬(p * q) ^ 2 ∣ d := by
          contrapose! hd_sqf
          simp [Squarefree]
          use p * q, sq (p * q) ▸ hd_sqf
          linarith only [one_lt_mul'' hp.one_lt hq.one_lt]
        have : p * q ∣ (p * q * b') ^ 2 * a / d := by
          have hp' : p ∣ (p * q * b') ^ 2 * a / d :=
             Squarefree.dvd_self_div_of_sq_dvd hd_sqf ⟨(q * b') ^ 2 * a, by ring⟩ hd_dvd.left
          have hq' : q ∣ (p * q * b') ^ 2 * a / d :=
             Squarefree.dvd_self_div_of_sq_dvd hd_sqf ⟨(p * b') ^ 2 * a, by ring⟩ hd_dvd.left
          exact Prime.dvd_mul_of_dvd_ne hpq hp hq hp' hq'
        rw [not_isPrimePow_iff_exists_primes_dvd]
        use p, q, hp, hq, hpq
        exact ⟨(dvd_mul_right _ _).trans this, (dvd_mul_left _ _).trans this⟩
        set X := (p * q * b') ^ 2 * a / d with hX
        have hX₀ : X ≠ 0 := by
          have : 0 < d := by by_contra!; simp only [le_zero.mp this, not_squarefree_zero] at hd_sqf
          rw [Nat.ne_zero_iff_zero_lt]
          exact (Nat.lt_div_iff_mul_lt hd_dvd.left 0).mpr hn₀
        have hX₁ : X ≠ 1 := by
          contrapose! hd_sqf
          obtain ⟨rfl⟩ := eq_of_dvd_of_div_eq_one hd_dvd.left hd_sqf
          simp [Squarefree]
          use p, (by use (q * b') ^ 2 * a, by ring), hp.ne_one
        exact one_lt_iff_ne_zero_and_ne_one.mpr ⟨hX₀, hX₁⟩

/- rwa [← hn.of_mul_left.dvd_pow_iff_dvd two_ne_zero] -/
