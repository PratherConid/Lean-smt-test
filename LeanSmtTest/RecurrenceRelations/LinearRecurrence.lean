import Mathlib.Algebra.LinearRecurrence
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

-- 线性递推关系
open Finset

open Polynomial

namespace LinearRecurrence

variable {R : Type*} [CommSemiring R]
variable (E : LinearRecurrence R)

set_option auto.mono.ignoreNonQuasiHigherOrder true
set_option auto.mono.mode "fol"
theorem is_sol_mkSol' (init : Fin E.order → R) : E.IsSolution (E.mkSol init) := by
  intro n
  rw [mkSol]
  simp
theorem is_sol_mkSol'' (init : Fin E.order → R) : E.IsSolution (E.mkSol init) := by
  intro n
  smt +mono [mkSol]
theorem is_sol_mkSol''' (init : Fin E.order → R) : E.IsSolution (E.mkSol init) := by
  auto [mkSol]


theorem mkSol_eq_init' (init : Fin E.order → R) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  intro n
  rw [mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val]
theorem mkSol_eq_init'' (init : Fin E.order → R) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  intro n
  smt +mono [is_sol_mkSol',mkSol,dif_pos, Fin.mk_val,n.is_lt]
theorem mkSol_eq_init''' (init : Fin E.order → R) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  intro n
  auto [is_sol_mkSol',mkSol,Fin.mk_val]
