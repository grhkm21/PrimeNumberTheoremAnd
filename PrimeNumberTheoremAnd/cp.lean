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
  · have h_id₁ {d : ℕ} (hd : d ∈ n.divisors) : μ n = μ d * μ (n / d) := by
      have := Nat.mul_div_cancel' $ dvd_of_mem_divisors hd
      rw [← (isMultiplicative_moebius).right, this]
      exact Nat.coprime_of_squarefree_mul (this.symm ▸ hn)
    have h_id₂ {d : ℕ} (hd : d ∈ n.divisors) : μ d * Λ d = -Λ d := by
      by_cases hd : IsPrimePow d
      · obtain ⟨p, k, ⟨hp, hd'⟩⟩ := hd
        rw [← Nat.prime_iff] at hp
        rw [← hd'.right, moebius_apply_prime_pow hp $ Nat.pos_iff_ne_zero.mp hd'.left]
        split_ifs with hk
        · norm_num
        · have : Squarefree _ := hd'.right.symm ▸ squarefree_of_dvd (dvd_of_mem_divisors hd) hn
          have : k = 0 ∨ k = 1 := eq_zero_or_one_of_pow_of_not_isUnit this hp.not_unit
          omega
      · simp only [vonMangoldt_apply, hd, if_false, mul_zero, neg_zero]
    symm
    rw [neg_mul, neg_eq_iff_eq_neg]
    /- My first long calc proof! -/
    calc μ n * log n
      _ = ∑ d in n.divisors, Λ d * μ n := by
        rw [← sum_mul, vonMangoldt_sum, mul_comm] ; rfl
      _ = ∑ d in n.divisors, Λ (n / d) * μ n := by
        rw [← sum_div_divisors]
      _ = ∑ d in n.divisors, Λ (n / d) * μ (n / d) * μ d := by
        refine sum_congr rfl (fun d hd ↦ ?_)
        rw [h_id₁ hd, mul_assoc, mul_comm (μ d)]
        norm_cast
      _ = -∑ d in n.divisors, Λ (n / d) * μ d := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl (fun d hd ↦ ?_)
        have hd' : n / d ∈ n.divisors := by
          rw [mem_divisors] at hd ⊢
          exact ⟨div_dvd_of_dvd hd.left, hd.right⟩
        rw [mul_comm (Λ _), h_id₂ hd', neg_mul]
      _ = -∑ d in n.divisors, μ d * Λ (n / d) := by
        simp_rw [mul_comm]
      _ = -(μ * Λ) n := by
        rw [mul_apply, ← map_div_right_divisors, sum_map, Function.Embedding.coeFn_mk]
        rfl
  · simp only [mul_apply, ← map_div_right_divisors, sum_map, Function.Embedding.coeFn_mk]
    rw [moebius_eq_zero_of_not_squarefree hn, Int.cast_zero, neg_zero, zero_mul]
    trans ∑ d in n.divisors.filter fun d ↦ IsPrimePow d ∧ Squarefree (n / d), Λ d * μ (n / d)
    · rw [← sum_div_divisors]
      rw [sum_congr rfl (g := fun d ↦ Λ d * μ (n / d)) (fun d hd ↦ by
        rw [Nat.div_div_self ?_ hn₀.ne.symm, mul_comm]
        rfl; exact (mem_divisors.mp hd).left
      )]
      rw [← sum_filter_ne_zero]
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
      · obtain ⟨p, k, hp_prime, hk_pos, rfl⟩ := hb'
        rw [← prime_iff] at hp_prime
        have : ∃ k' a',
            (p ^ k) ^ 2 * a = p ^ k'.succ * a' ∧ 1 ≤ k' ∧ Coprime p a' ∧ Squarefree a' := by
          use 2 * k + a.factorization p - 1, ord_compl[p] a, ?_, by omega, ?_
          · exact ha'.squarefree_of_dvd $ ord_compl_dvd a p
          · rw [succ_eq_add_one, Nat.sub_add_cancel (by omega), pow_add, mul_assoc,
              ord_proj_mul_ord_compl_eq_self]
            ring_nf
          · exact coprime_ord_compl hp_prime ha.ne.symm
        obtain ⟨k, a, hhhh, hk_one_le, ha_coprime, ha_sqf⟩ := this
        simp only [hhhh] at *; clear hhhh
        have ha_coprime' := ha_coprime.pow_left k.succ
        have ha_dvd : ¬p ∣ a := by
          contrapose! ha_coprime
          obtain ⟨k, rfl⟩ := ha_coprime
          simp [hp_prime.ne_one]
        have : ∀ d ∈ (p ^ k.succ * a).divisors.filter fun d ↦
            IsPrimePow d ∧ Squarefree (p ^ k.succ * a / d), p ^ k ∣ d := by
          intro d hd
          obtain ⟨hd, hd_pp, hd_sqf⟩ := mem_filter.mp hd
          obtain ⟨hd_dvd, hd_ne_zero⟩ := mem_divisors.mp hd
          obtain ⟨q, k', hq_prime, hk'_pos, rfl⟩ := hd_pp
          rw [← prime_iff] at hq_prime
          have : p = q := by
            have hdvd_pow {x : ℕ} := dvd_pow (dvd_rfl (a := x)) hk'_pos.ne.symm
            have hq_dvd := hq_prime.dvd_mul.mp $ hdvd_pow.trans hd_dvd
            cases' hq_dvd with hq_dvd hq_dvd
            · refine ((Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp ?_).symm
              exact hq_prime.dvd_of_dvd_pow hq_dvd
            · have : ¬p ∣ q := by
                contrapose! ha_coprime with hpq
                obtain ⟨k, rfl⟩ := hpq.trans hq_dvd
                simp [hp_prime.ne_one]
              have : p ^ k.succ ∣ p ^ k.succ * a / q ^ k' := by
                rw [Nat.mul_div_assoc]
                · apply dvd_mul_right
                · have h' := pow hq_prime.isPrimePow hk'_pos.ne.symm
                  have h' := (ha_coprime'.isPrimePow_dvd_mul h').mp hd_dvd
                  cases' h' with h'
                  · exfalso
                    replace h' := hq_prime.dvd_of_dvd_pow $ hdvd_pow.trans h'
                    replace h' := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp h'
                    exact (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).not.mp this h'.symm
                  · assumption
              absurd hd_sqf
              simp [Squarefree]
              use p, (sq p ▸ pow_dvd_pow _ (show 2 ≤ k.succ by omega)).trans this, hp_prime.ne_one
          subst this
          rw [pow_dvd_pow_iff_le_right hp_prime.one_lt]
          have hd_fact := hd_sqf.natFactorization_le_one p
          have h := mul_ne_zero_iff.mp hd_ne_zero
          rw [Nat.factorization_div hd_dvd, Nat.factorization_mul h.left h.right] at hd_fact
          simp [hp_prime.factorization_self, factorization_eq_zero_of_not_dvd ha_dvd] at hd_fact
          omega
        have : (p ^ k.succ * a).divisors.filter (fun d ↦
            IsPrimePow d ∧ Squarefree (p ^ k.succ * a / d)) = ({p ^ k, p ^ k.succ} : Finset ℕ) := by
          ext d
          constructor <;> intro hd
          · have hd₁ := this d hd
            rw [mem_filter, mem_divisors] at hd
            have hd₂ : d ∣ p ^ k.succ := by
              have := (dvd_pow dvd_rfl (by omega)).trans hd₁
              have := fun h'' ↦ ha_dvd $ this.trans h''
              have := (ha_coprime'.isPrimePow_dvd_mul hd.right.left).mp hd.left.left
              tauto
            obtain ⟨k', rfl⟩ := hd₁
            have : k' ∣ p := by
              convert dvd_div_of_mul_dvd hd₂
              rw [Nat.pow_div _ hp_prime.pos, succ_sub, Nat.sub_self, pow_one]
              all_goals omega
            have : k' = 1 ∨ k' = p := (dvd_prime hp_prime).mp this
            rcases this with rfl | rfl
            · simp
            · have : succ (k - 1) = k := by omega
              simp [← Nat.pow_succ, this]
          · simp at hd ⊢
            rcases hd with rfl | rfl
            <;> simp [hp_prime.ne_zero, (mul_ne_zero_iff.mp hn₀.ne.symm).right]
            · simp [Nat.pow_succ, mul_assoc, dvd_mul_right]
              constructor
              · use p, k, prime_iff.mp hp_prime, hk_one_le
              · rw [mul_div_right]
                · exact (squarefree_mul ha_coprime).mpr ⟨hp_prime.squarefree, ha_sqf⟩
                · exact pow_pos hp_prime.pos _
            · constructor
              · use p, k.succ, prime_iff.mp hp_prime, succ_pos _
              · rwa [mul_div_right]
                exact pow_pos hp_prime.pos _
        rw [this, sum_insert, sum_singleton, vonMangoldt_apply_pow, vonMangoldt_apply_pow]
        · save
          rw [Nat.mul_div_cancel_left, Nat.pow_succ, mul_assoc, Nat.mul_div_cancel_left]
          · rw [isMultiplicative_moebius.map_mul_of_coprime ha_coprime,
              moebius_apply_prime hp_prime]
            simp
          · exact pow_pos hp_prime.pos _
          · exact pow_pos hp_prime.pos _
        · simp
        · omega
        · simp
          have := Nat.pow_right_injective hp_prime.two_le
          specialize @this k k.succ
          simpa [(Nat.succ_ne_self k).symm, this]
      · /- It suffices to prove the filtered set is empty -/
        apply sum_congr (s₂ := ∅) ?_ fun _ _ ↦ rfl
        ext d
        simp [not_or]
        obtain ⟨p, q, hp_prime, hq_prime, hpq, hp_dvd, hq_dvd⟩ :=
          (not_isPrimePow_iff_exists_primes_dvd hb).mp hb'
        /- If p^2q^2 | b, then b / d cannot be a prime power for a squarefree d -/
        intro hd_dvd hb_zero ha_zero hd_pp h_sqf
        have hp₁ : 2 ≤ (b ^ 2 * a).factorization p := by
          rw [Nat.factorization_mul (pow_ne_zero _ hb_zero) ha_zero, Nat.factorization_pow]
          simp
          have := (hp_prime.dvd_iff_one_le_factorization hb_zero).mp hp_dvd
          omega
        have hq₁ : 2 ≤ (b ^ 2 * a).factorization q := by
          rw [Nat.factorization_mul (pow_ne_zero _ hb_zero) ha_zero, Nat.factorization_pow]
          simp
          have := (hq_prime.dvd_iff_one_le_factorization hb_zero).mp hq_dvd
          omega
        have hp₂ : (b ^ 2 * a / d).factorization p ≤ 1 := h_sqf.natFactorization_le_one p
        have hq₂ : (b ^ 2 * a / d).factorization q ≤ 1 := h_sqf.natFactorization_le_one q
        simp [factorization_div hd_dvd] at hp₂ hq₂
        have hp_dvd' := (hp_prime.dvd_iff_one_le_factorization hd_pp.ne_zero).mpr (by linarith)
        have hq_dvd' := (hq_prime.dvd_iff_one_le_factorization hd_pp.ne_zero).mpr (by linarith)
        exact hpq $ hd_pp.eq_of_dvd_dvd hp_prime hq_prime hp_dvd' hq_dvd'
