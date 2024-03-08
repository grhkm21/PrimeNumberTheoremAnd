import PrimeNumberTheoremAnd.Std.Data.Nat.Gcd
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

example {n : ℕ} : (μ * Λ) n = -μ n * log n := by
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
    · by_cases hn' : ∃ p q, p ≠ q ∧ p.Prime ∧ q.Prime ∧ p ^ 2 ∣ n ∧ q ^ 2 ∣ n
      /- If n is divisible by two prime squares, then n / p^k is never squarefree -/
      · convert sum_empty
        refine eq_empty_iff_forall_not_mem.mpr (fun d hd ↦ ?_)
        rw [mem_filter] at hd
      /- Otherwise, we can still evaluate the sum :) -/
      · have : ∃ p n₀, p.Prime ∧ Squarefree n₀ ∧ p.Coprime n₀ ∧ ∃ m, n = p ^ m * n₀ := by
          sorry
        obtain ⟨p, n₀, h⟩ := this
        obtain ⟨m, hm⟩ := h.right.right.right
        save
        have : n.divisors ≃ (p ^ m).divisors ×ˢ n₀.divisors := by
          rw [hm]
          apply mul_coprime_divisors_equiv
          · exact Coprime.pow_left _ h.right.right.left
          · apply IsPrimePow.ne_zero
            use p, m, prime_iff.mp h.left, ?_
            by_contra! hm'
            rw [nonpos_iff_eq_zero.mp hm', Nat.pow_zero, one_mul] at hm
            rw [hm] at hn
            tauto
          · exact fun hn₀ ↦ not_squarefree_zero (hn₀ ▸ h.right.left)

example : ¬Squarefree 0 := by exact?
