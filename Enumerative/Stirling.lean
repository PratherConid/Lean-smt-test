import Mathlib.Combinatorics.Enumerative.Stirling
import Smt
import Auto.Tactic
import Duper.Tactic
open Lean Auto in
def Auto.duperRaw (lemmas : Array Lemma) (inhs : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList [] 0

set_option auto.mono.ignoreNonQuasiHigherOrder true
attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option auto.native true
set_option auto.smt false
set_option auto.tptp false

open Nat

namespace Nat
-- incorrect number of universe levels Nat.cast
theorem stirlingSecond_eq_zero_of_lt' : ∀ {n k : ℕ}, n < k → stirlingSecond n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [stirlingSecond]
  | n + 1, k + 1, hk => by
    simp only [stirlingSecond_succ_succ, stirlingSecond_eq_zero_of_lt (Nat.lt_of_succ_lt_succ hk),
      stirlingSecond_eq_zero_of_lt (Nat.lt_of_succ_lt hk), mul_zero]
theorem stirlingSecond_eq_zero_of_lt'' : ∀ {n k : ℕ}, n < k → stirlingSecond n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [stirlingSecond]
  | n + 1, k + 1, hk => by
    smt +mono [stirlingSecond_succ_succ, stirlingSecond_eq_zero_of_lt (Nat.lt_of_succ_lt_succ hk)]

-- incorrect number of universe levels Nat.cast
theorem stirlingSecond_self' (n : ℕ) : stirlingSecond n n = 1 := by
  induction n <;> simp only [*, stirlingSecond, stirlingSecond_eq_zero_of_lt (lt_succ_self _),
    mul_zero]
theorem stirlingSecond_self'' (n : ℕ) : stirlingSecond n n = 1 := by
  induction n with
  | zero =>
    smt [stirlingSecond]
  | succ n ih =>
    smt [stirlingSecond_succ_succ, stirlingSecond_eq_zero_of_lt, ih]
theorem stirlingSecond_self''' (n : ℕ) : stirlingSecond n n = 1 := by
  induction n with
  | zero =>
    auto
  | succ n ih =>
    auto [stirlingSecond_succ_succ, stirlingSecond_eq_zero_of_lt, ih]
