import Mathlib.Combinatorics.Enumerative.Catalan
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


open Finset

open Finset.antidiagonal (fst_le snd_le)

theorem catalan_succ'' (n : ℕ) :
    catalan (n + 1) = ∑ ij ∈ antidiagonal n, catalan ij.1 * catalan ij.2 := by
  rw [catalan_succ, Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n,
    sum_range]
-- 无法单态化
set_option auto.mono.ignoreNonQuasiHigherOrder true
set_option auto.mono.mode "fol"
theorem catalan_succ''' (n : ℕ) :
    catalan (n + 1) = ∑ ij ∈ antidiagonal n, catalan ij.1 * catalan ij.2 := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n]
  smt +mono [catalan_succ,sum_range]

theorem catalan_succ'''' (n : ℕ) :
    catalan (n + 1) = ∑ ij ∈ antidiagonal n, catalan ij.1 * catalan ij.2 := by
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n]
  auto [catalan_succ,sum_range]


private def gosperCatalan (n j : ℕ) : ℚ :=
  Nat.centralBinom j * Nat.centralBinom (n - j) * (2 * j - n) / (2 * n * (n + 1))
-- 以下两个private用lean-smt解决都不行。问题出在没有降级incorrect number of universe levels Nat.cast
private theorem gosper_trick {n i : ℕ} (h : i ≤ n) :
    gosperCatalan (n + 1) (i + 1) - gosperCatalan (n + 1) i =
      Nat.centralBinom i / (i + 1) * Nat.centralBinom (n - i) / (n - i + 1) := by sorry
private theorem gosper_catalan_sub_eq_central_binom_div (n : ℕ) : gosperCatalan (n + 1) (n + 1) -
    gosperCatalan (n + 1) 0 = Nat.centralBinom (n + 1) / (n + 2) := by sorry
-- incorrect number of universe levels Nat.cast
set_option pp.rawOnError true
theorem catalan_eq_centralBinom_div' (n : ℕ) : catalan n = n.centralBinom / (n + 1) := by
  suffices (catalan n : ℚ) = Nat.centralBinom n / (n + 1) by
    have h := Nat.succ_dvd_centralBinom n
    auto [mod_cast]
  induction n using Nat.caseStrongRecOn with
  | zero => simp
  | ind d hd =>
    simp_rw [catalan_succ, Nat.cast_sum, Nat.cast_mul]
    trans (∑ i : Fin d.succ, Nat.centralBinom i / (i + 1) *
                            (Nat.centralBinom (d - i) / (d - i + 1)) : ℚ)
    · congr
      ext1 x
      have m_le_d : x.val ≤ d := by omega
      have d_minus_x_le_d : (d - x.val) ≤ d := tsub_le_self
      rw [hd _ m_le_d, hd _ d_minus_x_le_d]
      norm_cast
    · trans (∑ i : Fin d.succ, (gosperCatalan (d + 1) (i + 1) - gosperCatalan (d + 1) i))
      · refine sum_congr rfl fun i _ => ?_
        rw [gosper_trick i.is_le, mul_div]
      · rw [← sum_range fun i => gosperCatalan (d + 1) (i + 1) - gosperCatalan (d + 1) i,
            sum_range_sub, Nat.succ_eq_add_one]
        rw [gosper_catalan_sub_eq_central_binom_div d]
        norm_cast
