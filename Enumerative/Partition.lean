import Mathlib.Combinatorics.Enumerative.Partition
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


assert_not_exists Field

open Multiset

namespace Nat

namespace Partition

-- 证明重构的问题
theorem ofComposition_surj' {n : ℕ} : Function.Surjective (ofComposition n) := by
  rintro ⟨b, hb₁, hb₂⟩
  induction b using Quotient.inductionOn with | _ b => ?_
  exact ⟨⟨b, hb₁, by simpa using hb₂⟩, Partition.ext rfl⟩
theorem ofComposition_surj'' {n : ℕ} : Function.Surjective (ofComposition n) := by
  rintro ⟨b, hb₁, hb₂⟩
  induction b using Quotient.inductionOn with | _ b => ?_
  smt +mono [*]
theorem ofComposition_surj''' {n : ℕ} : Function.Surjective (ofComposition n) := by
  rintro ⟨b, hb₁, hb₂⟩
  induction b using Quotient.inductionOn with | _ b => ?_
  auto [hb₁,hb₂,Partition.ext,rfl]

-- 证明重构的问题
theorem count_ofSums_of_ne_zero' {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
    (ofSums n l hl).parts.count i = l.count i :=
  count_filter_of_pos hi
theorem count_ofSums_of_ne_zero'' {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
    (ofSums n l hl).parts.count i = l.count i := by
  smt +mono [hi,count_filter_of_pos]
theorem count_ofSums_of_ne_zero''' {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
    (ofSums n l hl).parts.count i = l.count i := by
  auto [hi,count_filter_of_pos]
