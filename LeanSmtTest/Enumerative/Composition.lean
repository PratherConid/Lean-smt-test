import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.List.Basic
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

open List

variable {n : ℕ}

namespace Composition

variable (c : Composition n)


--  SMT 没证出来
theorem length_le' : c.length ≤ n := by
  conv_rhs => rw [← c.blocks_sum]
  exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi
set_option auto.mono.ignoreNonQuasiHigherOrder true
set_option auto.mono.mode "fol"
theorem length_le'' : c.length ≤ n := by
  smt +mono [one_le_blocks, blocks_sum,blocks_length,List.length_le_sum_of_one_le]
theorem length_le''' : c.length ≤ n := by
  auto [one_le_blocks, blocks_sum,blocks_length,List.length_le_sum_of_one_le]


theorem blocksFun_congr' {n₁ n₂ : ℕ} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Fin c₁.length)
    (i₂ : Fin c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
    c₁.blocksFun i₁ = c₂.blocksFun i₂ := by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  congr
  rwa [Fin.ext_iff]
theorem blocksFun_congr'' {n₁ n₂ : ℕ} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Fin c₁.length)
    (i₂ : Fin c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
    c₁.blocksFun i₁ = c₂.blocksFun i₂ := by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  auto [hi,Fin.ext_iff]
theorem blocksFun_congr''' {n₁ n₂ : ℕ} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Fin c₁.length)
    (i₂ : Fin c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
    c₁.blocksFun i₁ = c₂.blocksFun i₂ := by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  smt +mono [hi,Fin.ext_iff]


theorem eq_ones_iff_length' {c : Composition n} : c = ones n ↔ c.length = n := by
  constructor
  · rintro rfl
    exact ones_length n
  · contrapose
    intro H length_n
    apply lt_irrefl n
    calc
      n = ∑ i : Fin c.length, 1 := by simp [length_n]
      _ < ∑ i : Fin c.length, c.blocksFun i := by
        {
        obtain ⟨i, hi, i_blocks⟩ : ∃ i ∈ c.blocks, 1 < i := ne_ones_iff.1 H
        rw [← ofFn_blocksFun, mem_ofFn' c.blocksFun, Set.mem_range] at hi
        obtain ⟨j : Fin c.length, hj : c.blocksFun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact Finset.sum_lt_sum (fun i _ => one_le_blocksFun c i) ⟨j, Finset.mem_univ _, i_blocks⟩
        }
      _ = n := c.sum_blocksFun
set_option auto.mono.ignoreNonQuasiHigherOrder true
theorem eq_ones_iff_length'' {c : Composition n} : c = ones n ↔ c.length = n := by
  constructor
  · rintro rfl
    exact ones_length n
  · contrapose
    intro H length_n
    apply lt_irrefl n
    calc
      n = ∑ i : Fin c.length, 1 := by simp [length_n]
      _ < ∑ i : Fin c.length, c.blocksFun i := by
        {
        obtain ⟨i, hi, i_blocks⟩ : ∃ i ∈ c.blocks, 1 < i := ne_ones_iff.1 H
        auto [ofFn_blocksFun,mem_ofFn',c.blocksFun,Set.mem_range,hi]
        obtain ⟨j : Fin c.length, hj : c.blocksFun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact Finset.sum_lt_sum (fun i _ => one_le_blocksFun c i) ⟨j, Finset.mem_univ _, i_blocks⟩
        }
      _ = n := c.sum_blocksFun
