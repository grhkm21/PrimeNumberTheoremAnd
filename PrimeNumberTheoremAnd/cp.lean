import PrimeNumberTheoremAnd.Std.Data.Nat.Gcd
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.VonMangoldt

set_option autoImplicit false

section aux

namespace Nat
namespace Coprime

open Finset

def mul_divisors_equiv {m n : ℕ} (h : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
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

theorem mul_divisors_equiv_prop {m n d} (h : Coprime m n) (hm hn) :
    (mul_divisors_equiv h hm hn d).val.fst * (mul_divisors_equiv h hm hn d).val.snd = d := by
  nth_rw 3 [← (mul_divisors_equiv h hm hn).left_inv d]
  rfl

end Coprime
end Nat

section actualStuff

open Nat hiding log
open BigOperators Squarefree ArithmeticFunction Finset IsPrimePow

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
    trans ∑ d in n.divisors.filter fun d ↦ IsPrimePow d ∧ Squarefree (n / d), Λ d * μ (n / d)
    /- · rw [← sum_div_divisors] -/
    /-   rw [sum_congr rfl (g := fun d ↦ Λ d * μ (n / d)) (fun d hd ↦ by -/
    /-     rw [Nat.div_div_self ?_ hn₀.ne.symm, mul_comm] -/
    /-     rfl; exact (mem_divisors.mp hd).left -/
    /-   )] -/
    /-   rw [← sum_filter_ne_zero] -/
    /-   refine sum_congr ?_ (fun _ _ ↦ rfl) -/
    /-   congr ; ext d -/
    /-   rw [mul_ne_zero_iff] -/
    /-   simp [moebius_ne_zero_iff_squarefree, vonMangoldt_eq_zero_iff] -/
    · sorry
    · obtain ⟨a, b, ha, hb, rfl, ha'⟩ := sq_mul_squarefree_of_pos hn₀
      replace hb : 1 < b := by
        contrapose! hn
        rcases (show b = 1 by omega) with rfl
        rwa [one_pow, one_mul]
      clear hn
      by_cases hb' : IsPrimePow b
      · obtain ⟨p, k, hp_prime, hk_pos, rfl⟩ := hb'
        rw [← prime_iff] at hp_prime
        have : ∃ k' a', (p ^ k) ^ 2 * a = p ^ k' * a' ∧ 2 ≤ k' ∧ Coprime p a' := by
          use 2 * k + a.factorization p, ord_compl[p] a, ?_, by linarith, ?_
          · ring_nf; rw [mul_assoc, ord_proj_mul_ord_compl_eq_self]
          · exact coprime_ord_compl hp_prime ha.ne.symm
        obtain ⟨k, a, hhhh, hk_two_le, ha_coprime⟩ := this; simp only [hhhh] at *; clear hhhh
        have ha_coprime' := ha_coprime.pow_left k
        have ha_dvd : ¬p ∣ a := by
          contrapose! ha_coprime
          obtain ⟨k, rfl⟩ := ha_coprime
          simp [hp_prime.ne_one]
        have : ∀ d ∈ (p ^ k * a).divisors.filter fun d ↦ IsPrimePow d ∧ Squarefree (p ^ k * a / d),
            p ∣ d := by
          /- intro d hd -/
          /- obtain ⟨hd, hd_pp, hd_sqf⟩ := mem_filter.mp hd -/
          /- obtain ⟨hd_dvd, hd_ne_zero⟩ := mem_divisors.mp hd -/
          /- obtain ⟨q, k', hq_prime, hk'_pos, rfl⟩ := hd_pp -/
          /- rw [← prime_iff] at hq_prime -/
          /- suffices p = q by subst this; apply dvd_pow dvd_rfl hk'_pos.ne.symm -/
          /- have hq_dvd := hq_prime.dvd_mul.mp $ (dvd_pow dvd_rfl hk'_pos.ne.symm).trans hd_dvd -/
          /- cases' hq_dvd with hq_dvd hq_dvd -/
          /- · refine ((Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp ?_).symm -/
          /-   exact hq_prime.dvd_of_dvd_pow hq_dvd -/
          /- · have : ¬p ∣ q := by -/
          /-     contrapose! ha_coprime with hpq -/
          /-     obtain ⟨k, rfl⟩ := hpq.trans hq_dvd -/
          /-     simp [hp_prime.ne_one] -/
          /-   have : p ^ k ∣ p ^ k * a / q ^ k' := by -/
          /-     rw [Nat.mul_div_assoc] -/
          /-     · apply dvd_mul_right -/
          /-     · have h' := pow hq_prime.isPrimePow hk'_pos.ne.symm -/
          /-       have h' := (ha_coprime'.isPrimePow_dvd_mul h').mp hd_dvd -/
          /-       cases' h' with h' -/
          /-       · exfalso -/
          /-         replace h' := hq_prime.dvd_of_dvd_pow $ (dvd_pow dvd_rfl hk'_pos.ne.symm).trans h' -/
          /-         replace h' := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp h' -/
          /-         exact (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).not.mp this h'.symm -/
          /-       · assumption -/
          /-   absurd hd_sqf -/
          /-   simp [Squarefree] -/
          /-   use p, (sq p ▸ Nat.pow_dvd_pow p hk_two_le).trans this, hp_prime.ne_one -/
          sorry
        sorry
      · apply sum_congr (s₂ := ∅) ?_ (fun _ _ ↦ rfl)
        ext d
        simp only [not_mem_empty, iff_false, mem_filter, mem_divisors, not_and]
        sorry
