import Lean.Elab.Tactic.Decide
import Init.WF
import Lean.Elab.Tactic.Omega

namespace A099649

def sqDigitSum (n : Nat) : Nat :=
  if n = 0 then 0 else (n % 10)^2 + sqDigitSum (n / 10)
termination_by n

theorem sqDigitSum_eq (n : Nat) (h : n ≠ 0) :
    sqDigitSum n = (n % 10)^2 + sqDigitSum (n / 10) := by
  rw [sqDigitSum]
  simp [h]

theorem digit_square_bound (d : Nat) (h : d < 10) : d^2 ≤ 81 := by
  have hd : d ≤ 9 := by omega
  have hm := Nat.mul_le_mul hd hd
  simpa [Nat.pow_succ] using hm

set_option maxRecDepth 100000 in
theorem baseFin : ∀ i : Fin 1305, sqDigitSum (145 + i.val) < 145 + i.val := by
  native_decide

theorem base_bound (n : Nat) (h1 : 145 ≤ n) (h2 : n < 1450) : sqDigitSum n < n := by
  let i : Fin 1305 := ⟨n - 145, by omega⟩
  have h := baseFin i
  have he : 145 + i.val = n := by simp [i]; omega
  rw [he] at h
  exact h

theorem descent : ∀ n : Nat, 145 ≤ n → sqDigitSum n < n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hs : n < 1450
    · exact base_bound n hn hs
    · have hn0 : n ≠ 0 := by omega
      rw [sqDigitSum_eq n hn0]
      have hq : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have hq244 : 145 ≤ n / 10 := by omega
      have hi := ih (n / 10) hq hq244
      have hr : n % 10 < 10 := Nat.mod_lt n (by omega)
      have hd := digit_square_bound (n % 10) hr
      omega

def iter : Nat → Nat → Nat
  | 0, n => n
  | k+1, n => iter k (sqDigitSum n)

set_option maxRecDepth 100000 in
theorem bounded_step : ∀ i : Fin 164, sqDigitSum i.val < 164 := by
  native_decide

theorem step_lt_164 (n : Nat) (hn : n < 164) : sqDigitSum n < 164 := by
  let i : Fin 164 := ⟨n, hn⟩
  exact bounded_step i

theorem orbit_lt_164 (n k : Nat) (hn : n < 164) : iter k n < 164 := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (sqDigitSum n) (step_lt_164 n hn)

set_option maxRecDepth 100000 in
theorem base_orbit : ∀ i : Fin 19, ∀ k : Fin 164,
    iter k.val (145 + i.val) ≤ 145 + i.val := by
  native_decide

theorem global_bound : ∀ n k : Nat, iter k n ≤ max n 163 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k
    by_cases hn : n < 164
    · have h := orbit_lt_164 n k hn
      omega
    · have hn164 : 164 ≤ n := by omega
      cases k with
      | zero => simp [iter, Nat.le_max_left]
      | succ k =>
        have hs : sqDigitSum n < n := descent n (by omega)
        have hrec := ih (sqDigitSum n) hs k
        simp [iter]
        omega

theorem no_late_term (n k : Nat) (hn : 164 ≤ n) : iter k n ≤ n := by
  have h := global_bound n k
  omega

theorem iter_add (a b n : Nat) : iter (a+b) n = iter a (iter b n) := by
  induction b generalizing n with
  | zero => simp [iter]
  | succ b ih => simp [iter, ih]

set_option maxRecDepth 100000 in
theorem middle_base : ∀ i : Fin 19, ∀ k : Fin 20,
    iter k.val (145 + i.val) ≤ 145 + i.val := by
  native_decide

set_option maxRecDepth 100000 in
theorem middle_cycle : ∀ i : Fin 19,
    iter 20 (145 + i.val) = iter 12 (145 + i.val) := by
  native_decide

theorem middle_no_term (i : Fin 19) : ∀ k : Nat,
    iter k (145 + i.val) ≤ 145 + i.val := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k < 20
    · exact middle_base i ⟨k, hk⟩
    · have hk8 : k - 8 < k := by omega
      have hsplit20 : k = (k-20)+20 := by omega
      have hsplit12 : k-8 = (k-20)+12 := by omega
      rw [hsplit20, iter_add, middle_cycle i, ← iter_add, ← hsplit12]
      exact ih (k-8) hk8

theorem finality (n k : Nat) (hn : 145 ≤ n) : iter k n ≤ n := by
  by_cases hmid : n < 164
  · let i : Fin 19 := ⟨n-145, by omega⟩
    have h := middle_no_term i k
    have he : 145 + i.val = n := by simp [i]; omega
    rw [he] at h
    exact h
  · exact no_late_term n k (by omega)

set_option maxRecDepth 100000 in
theorem term_144 : 144 < iter 8 144 := by native_decide

end A099649
