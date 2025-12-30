import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Smt
import Auto.Tactic
import Duper.Tactic

open Lean Auto in
def Auto.duperRaw (lemmas : Array Lemma) (inhs : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList [] 0

set_option auto.mono.ignoreNonQuasiHigherOrder true
set_option auto.mono.mode "fol"
attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option auto.native true
set_option auto.smt false
set_option auto.tptp false

open IncidenceAlgebra Finset

namespace MyPractice

variable {𝕜 α : Type*} [DecidableEq α]

-- test1  Zeta 函数的平方
lemma zeta_mul_zeta' [NonAssocSemiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableLE α]
    (a b : α) : (zeta 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) a b = (Icc a b).card := by
  smt +mono [Nat.cast_sum,Nat.cast_one,List.Perm.length_eq]  -- 单态化翻译问题。
  -- List.Perm.length_eq（置换不改变列表长度）这个引理，或者它依赖的某个定义，使用了复杂的依赖类型，lean-auto无法翻译
-- lemma zeta_mul_zeta'' [NonAssocSemiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableLE α]
--     (a b : α) : (zeta 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) a b = (Icc a b).card := by
--   auto [Nat.cast_sum,Nat.cast_one,List.Perm.length_eq]

-- test2
variable {𝕜 α : Type*} [DecidableEq α] [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α]
variable {a b : α}
-- rw [mu_apply, if_neg hab]
lemma mu_eq_neg_sum_Ico_of_ne' (hab : a ≠ b) :
    mu 𝕜 a b = -∑ x ∈ Ico a b, mu 𝕜 a x := by smt +mono [mu_apply,if_neg,hab]
-- ∑ x ∈ Ico a b, mu 𝕜 a x，实际上是 Finset.sum (Ico a b) (fun x => mu 𝕜 a x)，fun x => ... 就是一个 Lambda 函数，无法翻译。
lemma mu_eq_neg_sum_Ico_of_ne'' (hab : a ≠ b) :
    mu 𝕜 a b = -∑ x ∈ Ico a b, mu 𝕜 a x := by
  auto [mu_apply,if_neg,hab]

-- test3
variable {𝕜 α : Type*} [DecidableEq α] [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [OrderBot α]
-- lemma moebius_inversion_bot' (f g : α → 𝕜) (h : ∀ x, g x = ∑ y ∈ Iic x, f y) (x : α) :
--     f x = ∑ y ∈ Iic x, mu 𝕜 y x * g y := by
--   smt +mono [moebius_inversion_top,mu_toDual] -- 单态化失败
lemma moebius_inversion_bot'' (f g : α → 𝕜) (h : ∀ x, g x = ∑ y ∈ Iic x, f y) (x : α) :
    f x = ∑ y ∈ Iic x, mu 𝕜 y x * g y := by
    auto [moebius_inversion_top,mu_toDual,h]

-- test4
variable (𝕜) [Ring 𝕜] [PartialOrder α] [PartialOrder β] [LocallyFiniteOrder α]
  [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β] [DecidableLE α] [DecidableLE β]
lemma mu_prod_mu : (mu 𝕜).prod (mu 𝕜) = (mu 𝕜 : IncidenceAlgebra 𝕜 (α × β)) := by
  -- smt +mono [left_inv_eq_right_inv,zeta_mul_mu,zeta_prod_zeta,prod_mul_prod',mu_mul_zeta,one_prod_one]
  -- 超时
  -- auto [left_inv_eq_right_inv,zeta_mul_mu,zeta_prod_zeta,prod_mul_prod',mu_mul_zeta,one_prod_one]
