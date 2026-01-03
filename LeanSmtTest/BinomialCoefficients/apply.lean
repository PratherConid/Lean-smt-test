import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Combinatorics.SetFamily.AhlswedeZhang
import Mathlib.Combinatorics.SetFamily.KruskalKatona
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


open Finset Nat
open scoped FinsetFamily


section Bell
namespace Multiset
private theorem bell_mul_eq_lemma {x : ℕ} (hx : x ≠ 0) :
    ∀ c, x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)!
  | 0 => by simp
  | c + 1 => calc
      x ! ^ (c + 1) * (c + 1)! * ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1)
        = x ! * (c + 1) * x ! ^ c * c ! *
            ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1) := by
        rw [factorial_succ, pow_succ]; ring
      _ = (x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1)) *
            (c * x + x - 1).choose (x - 1) * x ! * (c + 1)  := by
        rw [Finset.prod_range_succ]; ring
      _ = (c + 1) * (c * x + x - 1).choose (x - 1) * (x * c)! * x ! := by
        rw [bell_mul_eq_lemma hx]; ring
      _ = (x * (c + 1))! := by
        rw [← Nat.choose_mul_add hx, mul_comm c x, Nat.add_choose_mul_factorial_mul_factorial]
        ring_nf
-- lean-smt不能处理这个：∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1)这是一个λ表达式
-- 通过congr 1去除掉等式两边的λ表达式之后，还是行不通
-- incorrect number of universe levels Nat.cast
theorem bell_mul_eq_lemma' {x : ℕ} (hx : x ≠ 0) :
    ∀ c, x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)!
  | 0 => by simp
  | c + 1 => calc
      x ! ^ (c + 1) * (c + 1)! * ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1)
        = x ! * (c + 1) * x ! ^ c * c ! *
            ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1) := by
          congr 1
          norm_cast
          smt +mono []

theorem bell_mul_eq_lemma'' {x : ℕ} (hx : x ≠ 0) :
    ∀ c, x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)!
  | 0 => by simp
  | c + 1 => calc
      x ! ^ (c + 1) * (c + 1)! * ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1)
        = x ! * (c + 1) * x ! ^ c * c ! *
            ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1) := by
        congr 1
        norm_cast
        auto [factorial_succ, pow_succ]

-- uniformBell里面用到了bell，bell中有λ表达式，无法翻译
theorem uniformBell_eq (m n : ℕ) : m.uniformBell n =
    ∏ p ∈ (Finset.range m), Nat.choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp  [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]
set_option auto.mono.mode "fol"
theorem uniformBell_eq' (m n : ℕ) : m.uniformBell n =
    ∏ p ∈ (Finset.range m), Nat.choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp [hm]
  · by_cases hn : n = 0
    · smt +mono [hn]
theorem uniformBell_eq'' (m n : ℕ) : m.uniformBell n =
    ∏ p ∈ (Finset.range m), Nat.choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp [hm]
  · by_cases hn : n = 0
    · auto [hn]



-- 同上
theorem uniformBell_succ_left (m n : ℕ) :
    uniformBell (m+1) n = Nat.choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]
set_option auto.mono.mode "fol"
theorem uniformBell_succ_left' (m n : ℕ) :
    uniformBell (m+1) n = Nat.choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  smt +mono []
theorem uniformBell_succ_left'' (m n : ℕ) :
    uniformBell (m+1) n = Nat.choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  auto [uniformBell_eq, Finset.prod_range_succ, mul_comm]



end Multiset
end Bell

section Stirling
open Multiset
namespace Nat
-- incorrect number of universe levels Nat.cast
theorem stirlingFirst_succ_self_left' (n : ℕ) : stirlingFirst (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => simp only [zero_add, stirlingFirst_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingFirst_succ_succ, ih, stirlingFirst_self, mul_one, Nat.choose_succ_succ (n + 1),
      Nat.choose_one_right]
theorem stirlingFirst_succ_self_left'' (n : ℕ) : stirlingFirst (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => simp only [zero_add, stirlingFirst_succ_zero, choose_succ_self]
  | succ n ih =>
    smt +mono []
theorem stirlingFirst_succ_self_left''' (n : ℕ) : stirlingFirst (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => simp only [zero_add, stirlingFirst_succ_zero, choose_succ_self]
  | succ n ih =>
    auto [stirlingFirst_succ_succ, ih, stirlingFirst_self, mul_one, Nat.choose_succ_succ (n + 1),
      Nat.choose_one_right]



theorem stirlingSecond_succ_self_left' (n : ℕ) :
    stirlingSecond (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => simp only [zero_add, stirlingSecond_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingSecond_succ_succ, ih, stirlingSecond_self, mul_one,
      Nat.choose_succ_succ (n + 1), Nat.choose_one_right]
theorem stirlingSecond_succ_self_left'' (n : ℕ) :
    stirlingSecond (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => smt +mono []
  | succ n ih => smt []
theorem stirlingSecond_succ_self_left''' (n : ℕ) :
    stirlingSecond (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => auto
  | succ n ih => auto [stirlingSecond_succ_succ, ih, stirlingSecond_self, mul_one,
      Nat.choose_succ_succ (n + 1), Nat.choose_one_right]


end Nat
end Stirling

section AhlswedeZhang
variable (α : Type*) [Fintype α] [Nonempty α] {m n : ℕ}
open Finset Fintype Nat
private lemma binomial_sum_eq (h : n < m) :
    ∑ i ∈ range (n + 1), (n.choose i * (m - n) / ((m - i) * m.choose i) : ℚ) = 1 := by
  set f : ℕ → ℚ := fun i ↦ n.choose i * (m.choose i : ℚ)⁻¹ with hf
  suffices ∀ i ∈ range (n + 1), f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i) by
    rw [← sum_congr rfl this, sum_range_sub', hf]
    simp [choose_zero_right]
  intro i h₁
  rw [mem_range] at h₁
  have h₁ := le_of_lt_succ h₁
  have h₂ := h₁.trans_lt h
  have h₃ := h₂.le
  have hi₄ : (i + 1 : ℚ) ≠ 0 := i.cast_add_one_ne_zero
  have := congr_arg ((↑) : ℕ → ℚ) (choose_succ_right_eq m i)
  push_cast at this
  dsimp [f, hf]
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have := congr_arg ((↑) : ℕ → ℚ) (choose_succ_right_eq n i)
  push_cast at this
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have : (m - i : ℚ) ≠ 0 := sub_ne_zero_of_ne (cast_lt.mpr h₂).ne'
  have : (m.choose i : ℚ) ≠ 0 := cast_ne_zero.2 (choose_pos h₂.le).ne'
  simp [field, *]
lemma binomial_sum_eq' (h : n < m) :
    ∑ i ∈ range (n + 1), (n.choose i * (m - n) / ((m - i) * m.choose i) : ℚ) = 1 := by
  set f : ℕ → ℚ := fun i ↦ n.choose i * (m.choose i : ℚ)⁻¹ with hf
  suffices ∀ i ∈ range (n + 1), f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i) by
    rw [← sum_congr rfl this, sum_range_sub', hf]
    simp [choose_zero_right]
  intro i h₁
  rw [mem_range] at h₁
  have h₁ := le_of_lt_succ h₁
  have h₂ := h₁.trans_lt h
  have h₃ := h₂.le
  have hi₄ : (i + 1 : ℚ) ≠ 0 := by smt +mono [cast_add_one_ne_zero]
  have := by smt +mono [congr_arg,choose_succ_right_eq] -- incorrect number of universe levels Nat.cast
lemma binomial_sum_eq'' (h : n < m) :
    ∑ i ∈ range (n + 1), (n.choose i * (m - n) / ((m - i) * m.choose i) : ℚ) = 1 := by
  set f : ℕ → ℚ := fun i ↦ n.choose i * (m.choose i : ℚ)⁻¹ with hf
  suffices ∀ i ∈ range (n + 1), f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i) by
    rw [← sum_congr rfl this, sum_range_sub', hf]
    simp [choose_zero_right]
  intro i h₁
  rw [mem_range] at h₁
  have h₁ := le_of_lt_succ h₁
  have h₂ := h₁.trans_lt h
  have h₃ := h₂.le
  have hi₄ : (i + 1 : ℚ) ≠ 0 := by smt +mono [cast_add_one_ne_zero]
  have := by auto [congr_arg,choose_succ_right_eq]







end AhlswedeZhang

section KruskalKatona
attribute [-instance] instDecidableEqFin
open Nat
open scoped FinsetFamily
namespace Finset
namespace Colex
variable {r k i : ℕ} {𝒜 𝒞 : Finset <| Finset <| Fin n}
theorem kruskal_katona_lovasz_form' (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  set range'k : Finset (Fin n) :=
    attachFin (range k) fun m ↦ by rw [mem_range]; apply forall_lt_iff_le.2 hkn
  set 𝒞 : Finset (Finset (Fin n)) := powersetCard r range'k
  have : (𝒞 : Set (Finset (Fin n))).Sized r := Set.sized_powersetCard _ _
  calc
    k.choose (r - i)
    _ = #(powersetCard (r - i) range'k) := by rw [card_powersetCard, card_attachFin, card_range]
    _ = #(∂^[i] 𝒞) := by
      congr!
      ext B
      rw [mem_powersetCard, mem_shadow_iterate_iff_exists_sdiff]
      constructor
      · rintro ⟨hBk, hB⟩
        have := exists_subsuperset_card_eq hBk (Nat.le_add_left _ i) <| by
          rwa [hB, card_attachFin, card_range, ← Nat.add_sub_assoc hir, Nat.add_sub_cancel_left]
        obtain ⟨C, BsubC, hCrange, hcard⟩ := this
        rw [hB, ← Nat.add_sub_assoc hir, Nat.add_sub_cancel_left] at hcard
        refine ⟨C, mem_powersetCard.2 ⟨hCrange, hcard⟩, BsubC, ?_⟩
        rw [card_sdiff_of_subset BsubC, hcard, hB, Nat.sub_sub_self hir]
      · rintro ⟨A, Ah, hBA, card_sdiff_i⟩
        rw [mem_powersetCard] at Ah
        refine ⟨hBA.trans Ah.1, eq_tsub_of_add_eq ?_⟩
        rw [← Ah.2, ← card_sdiff_i, add_comm, card_sdiff_add_card_eq_card hBA]
    _ ≤ #(∂ ^[i] 𝒜) := by
      refine iterated_kk h₁ ?_ ⟨‹_›, ?_⟩
      · rwa [card_powersetCard, card_attachFin, card_range]
      simp_rw [𝒞, mem_powersetCard]
      rintro A B hA ⟨HB₁, HB₂⟩
      refine ⟨fun t ht ↦ ?_, ‹_›⟩
      rw [mem_attachFin, mem_range]
      have : toColex (image Fin.val B) < toColex (image Fin.val A) := by
        rwa [toColex_image_lt_toColex_image Fin.val_strictMono]
      apply Colex.forall_lt_mono this.le _ t (mem_image.2 ⟨t, ht, rfl⟩)
      simp_rw [mem_image]
      rintro _ ⟨a, ha, hab⟩
      simpa [range'k, hab] using hA.1 ha
theorem kruskal_katona_lovasz_form'' (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  set range'k : Finset (Fin n) :=
    attachFin (range k) fun m ↦ by rw [mem_range]; apply forall_lt_iff_le.2 hkn
  set 𝒞 : Finset (Finset (Fin n)) := powersetCard r range'k --单态化失败，存在绑定变量
  have : (𝒞 : Set (Finset (Fin n))).Sized r := by smt +mono [Set.sized_powersetCard _ _]
theorem kruskal_katona_lovasz_form''' (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  set range'k : Finset (Fin n) :=
    attachFin (range k) fun m ↦ by rw [mem_range]; apply forall_lt_iff_le.2 hkn
  set 𝒞 : Finset (Finset (Fin n)) := powersetCard r range'k --单态化失败，存在绑定变量
  have : (𝒞 : Set (Finset (Fin n))).Sized r := by auto [Set.sized_powersetCard _ _]




end Colex
end Finset
end KruskalKatona

section LYM
open Finset Nat
open scoped FinsetFamily

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

namespace Finset
variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {r : ℕ}

theorem local_lubell_yamamoto_meshalkin_inequality_div' (hr : r ≠ 0)
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) : (#𝒜 : 𝕜) / (Fintype.card α).choose r
    ≤ #(∂ 𝒜) / (Fintype.card α).choose (r - 1) := by
  obtain hr' | hr' := lt_or_ge (Fintype.card α) r
  · rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
  replace h𝒜 := local_lubell_yamamoto_meshalkin_inequality_mul h𝒜
  rw [div_le_div_iff₀] <;> norm_cast
  · rcases r with - | r
    · exact (hr rfl).elim
    rw [tsub_add_eq_add_tsub hr', add_tsub_add_eq_tsub_right] at h𝒜
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    convert Nat.mul_le_mul_right ((Fintype.card α).choose r) h𝒜 using 1
    · simpa [mul_assoc, Nat.choose_succ_right_eq] using Or.inl (mul_comm _ _)
    · simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff]
      exact Or.inl (mul_comm _ _)
  · exact Nat.choose_pos hr'
  · exact Nat.choose_pos (r.pred_le.trans hr')
theorem local_lubell_yamamoto_meshalkin_inequality_div'' (hr : r ≠ 0)
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) : (#𝒜 : 𝕜) / (Fintype.card α).choose r
    ≤ #(∂ 𝒜) / (Fintype.card α).choose (r - 1) := by
  obtain hr' | hr' := lt_or_ge (Fintype.card α) r
  · smt +mono [choose_eq_zero_of_lt,cast_zero,div_zero]  -- 单态化失败

theorem local_lubell_yamamoto_meshalkin_inequality_div''' (hr : r ≠ 0)
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) : (#𝒜 : 𝕜) / (Fintype.card α).choose r
    ≤ #(∂ 𝒜) / (Fintype.card α).choose (r - 1) := by
  obtain hr' | hr' := lt_or_ge (Fintype.card α) r
  · auto [choose_eq_zero_of_lt,cast_zero,div_zero]



end Finset
end LYM
