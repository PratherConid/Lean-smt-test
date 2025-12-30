import Mathlib.Data.Nat.Fib.Basic
import Smt
import Mathlib.Data.Nat.Basic
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

theorem fib_add_two' {n : ℕ} : fib (n + 2) = fib n + fib (n + 1) := by
  simp [fib, Function.iterate_succ_apply']
theorem fib_add_two'' {n : ℕ} : fib (n + 2) = fib n + fib (n + 1) := by
  smt +mono [Function.iterate_succ_apply']
theorem fib_add_two''' {n : ℕ} : fib (n + 2) = fib n + fib (n + 1) := by
  auto [Function.iterate_succ_apply',fib]
