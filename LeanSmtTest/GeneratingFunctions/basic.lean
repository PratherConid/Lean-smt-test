import Mathlib.RingTheory.PowerSeries.Basic
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

open PowerSeries

variable {R : Type*} [Semiring R]
open Finset (antidiagonal mem_antidiagonal)

theorem ext {φ ψ : R⟦X⟧} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
    rfl
theorem ext' {φ ψ : R⟦X⟧} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
  smt +mono [PowerSeries.coeff_def,h]
theorem ext'' {φ ψ : R⟦X⟧} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
  auto [PowerSeries.coeff_def,h]


theorem coeff_def {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) :
    coeff (R := R) n = MvPowerSeries.coeff s := by
  rw [coeff, ← h, ← Finsupp.unique_single s]
theorem coeff_def' {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) :
    coeff (R := R) n = MvPowerSeries.coeff s := by
  smt +mono [h,Finsupp.unique_single]
theorem coeff_def'' {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) :
    coeff (R := R) n = MvPowerSeries.coeff s := by
  auto [h,Finsupp.unique_single]



theorem coeff_zero_eq_constantCoeff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ := by
  rw [coeff_zero_eq_constantCoeff]
theorem coeff_zero_eq_constantCoeff_apply' (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ := by
  smt +mono [coeff_zero_eq_constantCoeff]
theorem coeff_zero_eq_constantCoeff_apply'' (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ := by
  auto [coeff_zero_eq_constantCoeff]


theorem coeff_zero_eq_constantCoeff : ⇑(coeff (R := R) 0) = constantCoeff := by
  rw [coeff, Finsupp.single_zero]
  rfl
theorem coeff_zero_eq_constantCoeff' : ⇑(coeff (R := R) 0) = constantCoeff := by
  smt +mono [coeff_zero_eq_constantCoeff_apply']
theorem coeff_zero_eq_constantCoeff'' : ⇑(coeff (R := R) 0) = constantCoeff := by
  auto [coeff_zero_eq_constantCoeff_apply']


theorem coeff_C (n : ℕ) (a : R) : coeff n (C a : R⟦X⟧) = if n = 0 then a else 0 := by
  rw [← monomial_zero_eq_C_apply, coeff_monomial]
theorem coeff_C' (n : ℕ) (a : R) : coeff n (C a : R⟦X⟧) = if n = 0 then a else 0 := by
  smt +mono [monomial_zero_eq_C_apply,coeff_monomial]
theorem coeff_C'' (n : ℕ) (a : R) : coeff n (C a : R⟦X⟧) = if n = 0 then a else 0 := by
  auto [monomial_zero_eq_C_apply,coeff_monomial]


theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff n (C x * X ^ k : R⟦X⟧) = if n = k then x else 0 := by
  simp [X_pow_eq, coeff_monomial]
theorem coeff_C_mul_X_pow' (x : R) (k n : ℕ) :
    coeff n (C x * X ^ k : R⟦X⟧) = if n = k then x else 0 := by
  smt +mono [X_pow_eq, coeff_monomial]
theorem coeff_C_mul_X_pow'' (x : R) (k n : ℕ) :
    coeff n (C x * X ^ k : R⟦X⟧) = if n = k then x else 0 := by
  auto [X_pow_eq, coeff_monomial]
