import Std.Data.Nat.Gcd

open Nat

/- This should be in Std, but we all know that won't happen. -/
theorem Coprime.coprime_dvd_left_dvd_right {a b c d : Nat}
    (hc : c ∣ a) (hd : d ∣ b) (h : Coprime a b) : Coprime c d := by
  obtain ⟨c', hc'⟩ := hc
  obtain ⟨d', hd'⟩ := hd
  subst hc' hd'
  apply Coprime.coprime_dvd_right (Nat.dvd_mul_right d d') ?_
  apply Coprime.coprime_dvd_left (Nat.dvd_mul_right _ _) h
