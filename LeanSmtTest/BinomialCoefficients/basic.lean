import Mathlib.Data.Nat.Choose.Basic
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

namespace Nat
theorem choose_succ_left' (n k : ℕ) (hk : 0 < k) :
    choose (n + 1) k = choose n (k - 1) + choose n k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl
theorem choose_succ_left'' (n k : ℕ) (hk : 0 < k) :
    choose (n + 1) k = choose n (k - 1) + choose n k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  smt +mono [rfl]
theorem choose_succ_left''' (n k : ℕ) (hk : 0 < k) :
    choose (n + 1) k = choose n (k - 1) + choose n k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  auto [rfl,hk,Nat.exists_eq_add_of_le']


theorem choose_zero_succ' (k : ℕ) : choose 0 (succ k) = 0 :=
  rfl
theorem choose_zero_succ'' (k : ℕ) : choose 0 (succ k) = 0 := by
  smt +mono []
theorem choose_zero_succ''' (k : ℕ) : choose 0 (succ k) = 0 := by
  auto

theorem choose_zero_right' (n : ℕ) : choose n 0 = 1 := by cases n <;> rfl
theorem choose_zero_right'' (n : ℕ) : choose n 0 = 1 := by
  cases n
  smt []
theorem choose_zero_right''' (n : ℕ) : choose n 0 = 1 := by
  cases n
  auto
  auto
