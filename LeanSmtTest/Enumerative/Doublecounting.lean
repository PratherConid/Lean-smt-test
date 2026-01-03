import Mathlib.Combinatorics.Enumerative.DoubleCounting
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

open Finset Function Relator

variable {R α β : Type*}

namespace Finset

section Bipartite

variable (r : α → β → Prop) (s : Finset α) (t : Finset β) (a : α) (b : β)
  [DecidablePred (r a)] [∀ a, Decidable (r a b)] {m n : ℕ}

variable {s t a b}

-- auto单态化失败
-- bipartiteAbove 和 bipartiteBelow 的定义中使用了 {x ∈ s | r x y}，这在 Lean 内部被转换为 Finset.filter (λ x => r x y) s
theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow' [∀ a b, Decidable (r a b)] :
    (∑ a ∈ s, #(t.bipartiteAbove r a)) = ∑ b ∈ t, #(s.bipartiteBelow r b) := by
  simp_rw [card_eq_sum_ones, sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow]

set_option auto.mono.ignoreNonQuasiHigherOrder true
set_option auto.mono.mode "fol"
theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow'' [∀ a b, Decidable (r a b)] :
    (∑ a ∈ s, #(t.bipartiteAbove r a)) = ∑ b ∈ t, #(s.bipartiteBelow r b) := by
  simp_rw [card_eq_sum_ones]
  simp_rw [bipartiteAbove, bipartiteBelow, sum_filter]
  smt +mono [*]
theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow''' [∀ a b, Decidable (r a b)] :
    (∑ a ∈ s, #(t.bipartiteAbove r a)) = ∑ b ∈ t, #(s.bipartiteBelow r b) := by
  auto [card_eq_sum_ones, bipartiteAbove, bipartiteBelow, sum_filter]


-- 单态化失败
theorem card_mul_le_card_mul'' [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) ≤ n) : #s * m ≤ #t * n :=
  card_nsmul_le_card_nsmul _ hm hn
theorem card_mul_le_card_mul''' [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) ≤ n) : #s * m ≤ #t * n := by
  smt +mono [card_nsmul_le_card_nsmul,hm,hn]
theorem card_mul_le_card_mul'''' [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) ≤ n) : #s * m ≤ #t * n := by
  auto [card_nsmul_le_card_nsmul,hm,hn]

-- 依旧翻译问题，问题出在λ表达式{ a ∈ s | r a b }
theorem card_le_card_of_forall_subsingleton'' (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ({ a ∈ s | r a b } : Set α).Subsingleton) : #s ≤ #t := by
  classical
    rw [← mul_one #s, ← mul_one #t]
    exact card_mul_le_card_mul r
      (fun a h ↦ card_pos.2 (by
        rw [← coe_nonempty, coe_bipartiteAbove]
        exact hs _ h : (t.bipartiteAbove r a).Nonempty))
      (fun b h ↦ card_le_one.2 (by
        simp_rw [mem_bipartiteBelow]
        exact ht _ h))
set_option auto.mono.ignoreNonQuasiHigherOrder true
set_option auto.mono.mode "fol"
theorem card_le_card_of_forall_subsingleton''' (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ({ a ∈ s | r a b } : Set α).Subsingleton) : #s ≤ #t := by
  classical
  rw [← mul_one #s, ← mul_one #t]
  smt +mono [coe_nonempty,coe_bipartiteAbove,mem_bipartiteBelow,hs,ht]
theorem card_le_card_of_forall_subsingleton'''' (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ({ a ∈ s | r a b } : Set α).Subsingleton) : #s ≤ #t := by
  classical
  rw [← mul_one #s, ← mul_one #t]
  auto [coe_nonempty,coe_bipartiteAbove,mem_bipartiteBelow,hs,ht]


theorem card_le_card_of_forall_subsingleton''''' (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ({ a ∈ s | r a b } : Set α).Subsingleton) : #s ≤ #t := by
  classical
  rw [← mul_one #s, ← mul_one #t]
  apply card_mul_le_card_mul r
  · intro a ha
    -- 这里处理 hm：每个 a 的邻居数 >= 1
    auto []
  · intro b hb
    -- 这里处理 hn：每个 b 的邻居数 <= 1
    specialize ht b hb
