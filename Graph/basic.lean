import Mathlib.Data.Set.Basic
import Mathlib.Data.Sym.Sym2
import Smt
import Auto.Tactic
import Duper.Tactic

open Lean Auto in
def Auto.duperRaw (lemmas : Array Lemma) (inhs : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList [] 0

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option auto.native true
set_option auto.mono.ignoreNonQuasiHigherOrder true
set_option auto.mono.mode "fol"

variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

structure Graph' (α β : Type*) where
  vertexSet : Set α
  IsLink : β → α → α → Prop
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet

namespace Graph'
variable {G : Graph' α β}
scoped notation "V(" G ")" => Graph'.vertexSet G
scoped notation "E(" G ")" => Graph'.edgeSet G

lemma IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩
lemma IsLink.edge_mem' (h : G.IsLink e x y) : e ∈ E(G) := by
  smt +mono [edge_mem_iff_exists_isLink,h]
lemma IsLink.edge_mem'' (h : G.IsLink e x y) : e ∈ E(G) := by
  auto [edge_mem_iff_exists_isLink,h]



protected lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
  G.isLink_symm h.edge_mem h
protected lemma IsLink.symm'' (h : G.IsLink e x y) : G.IsLink e y x := by
  apply G.isLink_symm
  · smt +mono [IsLink.edge_mem,h]
  · smt +mono [h]
protected lemma IsLink.symm''' (h : G.IsLink e x y) : G.IsLink e y x := by
  apply G.isLink_symm
  auto [h.edge_mem]
  auto


-- set option auto.mono.ignoreNonQuasiHigherOrder true

lemma IsLink.left_mem (h : G.IsLink e x y) : x ∈ V(G) :=
  G.left_mem_of_isLink h
lemma IsLink.left_mem' (h : G.IsLink e x y) : x ∈ V(G) := by
  smt +mono [G.left_mem_of_isLink,h]
lemma IsLink.left_mem'' (h : G.IsLink e x y) : x ∈ V(G) := by
  auto [G.left_mem_of_isLink,h]


lemma IsLink.right_mem (h : G.IsLink e x y) : y ∈ V(G) :=
  h.symm.left_mem
lemma IsLink.right_mem' (h : G.IsLink e x y) : y ∈ V(G) := by
  smt +mono [IsLink.left_mem]
set_option auto.mono.ignoreNonQuasiHigherOrder true
lemma IsLink.right_mem'' (h : G.IsLink e x y) : y ∈ V(G) := by
  auto [IsLink.left_mem,h]


lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x :=
  ⟨.symm, .symm⟩
lemma isLink_comm' : G.IsLink e x y ↔ G.IsLink e y x := by
  smt +mono [IsLink.symm]
lemma isLink_comm'' : G.IsLink e x y ↔ G.IsLink e y x := by
  auto [IsLink.symm]


lemma exists_isLink_of_mem_edgeSet (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y :=
  (edge_mem_iff_exists_isLink ..).1 h
lemma exists_isLink_of_mem_edgeSet' (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y := by
  smt +mono [edge_mem_iff_exists_isLink,h]
lemma exists_isLink_of_mem_edgeSet'' (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y := by
  auto [edge_mem_iff_exists_isLink,h]


lemma edgeSet_eq_setOf_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
  Set.ext G.edge_mem_iff_exists_isLink
lemma edgeSet_eq_setOf_exists_isLink' : E(G) = {e | ∃ x y, G.IsLink e x y} := by
  smt +mono [edge_mem_iff_exists_isLink,exists_isLink_of_mem_edgeSet,ext]
lemma edgeSet_eq_setOf_exists_isLink'' : E(G) = {e | ∃ x y, G.IsLink e x y} := by
  auto [edge_mem_iff_exists_isLink,exists_isLink_of_mem_edgeSet]


lemma IsLink.left_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : x = z ∨ x = w :=
  G.eq_or_eq_of_isLink_of_isLink h h'
lemma IsLink.left_eq_or_eq' (h : G.IsLink e x y) (h' : G.IsLink e z w) : x = z ∨ x = w := by
  smt +mono [eq_or_eq_of_isLink_of_isLink,h,h']
lemma IsLink.left_eq_or_eq'' (h : G.IsLink e x y) (h' : G.IsLink e z w) : x = z ∨ x = w := by
  auto [eq_or_eq_of_isLink_of_isLink,h,h']


lemma IsLink.right_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : y = z ∨ y = w :=
  h.symm.left_eq_or_eq h'
lemma IsLink.right_eq_or_eq' (h : G.IsLink e x y) (h' : G.IsLink e z w) : y = z ∨ y = w := by
  smt +mono [IsLink.symm,IsLink.left_eq_or_eq,h,h']
lemma IsLink.right_eq_or_eq'' (h : G.IsLink e x y) (h' : G.IsLink e z w) : y = z ∨ y = w := by
  auto [IsLink.symm,IsLink.left_eq_or_eq,h,h']


lemma IsLink.left_eq_of_right_ne (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x ≠ z) :
    x = w :=
  (h.left_eq_or_eq h').elim (False.elim ∘ hzx) id
lemma IsLink.left_eq_of_right_ne' (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x ≠ z) :
    x = w := by
  smt +mono [IsLink.left_eq_or_eq,h,h',hzx]
lemma IsLink.left_eq_of_right_ne'' (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x ≠ z) :
    x = w := by
  auto [IsLink.left_eq_or_eq,h,h',hzx]


lemma IsLink.right_unique (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z := by
  obtain rfl | rfl := h.right_eq_or_eq h'.symm
  · rfl
  obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl
lemma IsLink.right_unique' (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z := by
  smt +mono [IsLink.right_eq_or_eq,h,h']
lemma IsLink.right_unique'' (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z := by
  auto [IsLink.right_eq_or_eq,h,h']


lemma IsLink.left_unique (h : G.IsLink e x z) (h' : G.IsLink e y z) : x = y :=
  h.symm.right_unique h'.symm
lemma IsLink.left_unique' (h : G.IsLink e x z) (h' : G.IsLink e y z) : x = y := by
  smt +mono [IsLink.symm,IsLink.right_unique,h,h']
lemma IsLink.left_unique'' (h : G.IsLink e x z) (h' : G.IsLink e y z) : x = y := by
  auto [IsLink.symm,IsLink.right_unique,h,h']


lemma IsLink.eq_and_eq_or_eq_and_eq {x' y' : α} (h : G.IsLink e x y)
    (h' : G.IsLink e x' y') : (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  simp [h'.symm.right_unique h]
lemma IsLink.eq_and_eq_or_eq_and_eq' {x' y' : α} (h : G.IsLink e x y)
    (h' : G.IsLink e x' y') : (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  smt +mono [IsLink.left_eq_or_eq,IsLink.right_unique,h,h']
lemma IsLink.eq_and_eq_or_eq_and_eq'' {x' y' : α} (h : G.IsLink e x y)
    (h' : G.IsLink e x' y') : (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  auto [IsLink.left_eq_or_eq,IsLink.right_unique,h,h']


lemma IsLink.isLink_iff (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl,rfl⟩)
  · assumption
  exact h.symm
lemma IsLink.isLink_iff' (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  smt +mono [IsLink.eq_and_eq_or_eq_and_eq,h,IsLink.symm]
lemma IsLink.isLink_iff'' (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  auto [IsLink.eq_and_eq_or_eq_and_eq,h,IsLink.symm]


lemma IsLink.isLink_iff_sym2_eq (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ s(x,y) = s(x',y') := by
  rw [h.isLink_iff, Sym2.eq_iff]
lemma IsLink.isLink_iff_sym2_eq' (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ s(x,y) = s(x',y') := by
  smt +mono [IsLink.isLink_iff,Sym2.eq_iff,h]
lemma IsLink.isLink_iff_sym2_eq'' (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ s(x,y) = s(x',y') := by
  auto [h.isLink_iff, Sym2.eq_iff]


def Inc (G : Graph' α β) (e : β) (x : α) : Prop := ∃ y, G.IsLink e x y

lemma Inc.edge_mem (h : G.Inc e x) : e ∈ E(G) :=
  h.choose_spec.edge_mem
lemma Inc.edge_mem' (h : G.Inc e x) : e ∈ E(G) := by
  smt +mono [edge_mem_iff_exists_isLink,h]
lemma Inc.edge_mem'' (h : G.Inc e x) : e ∈ E(G) := by
  auto [edge_mem_iff_exists_isLink,h]

-- 17
lemma Inc.vertex_mem (h : G.Inc e x) : x ∈ V(G) :=
  h.choose_spec.left_mem
lemma Inc.vertex_mem' (h : G.Inc e x) : x ∈ V(G) := by
  smt +mono [Exists.choose_spec,IsLink.left_mem,h]
lemma Inc.vertex_mem'' (h : G.Inc e x) : x ∈ V(G) := by
  auto [Exists.choose_spec,IsLink.left_mem,h]

lemma IsLink.inc_left (h : G.IsLink e x y) : G.Inc e x :=
  ⟨y, h⟩
lemma IsLink.inc_left' (h : G.IsLink e x y) : G.Inc e x := by
  smt +mono [Inc.edge_mem,Inc.vertex_mem,h]
lemma IsLink.inc_left'' (h : G.IsLink e x y) : G.Inc e x := by
  auto [Inc.edge_mem,Inc.vertex_mem,h]



lemma IsLink.inc_right (h : G.IsLink e x y) : G.Inc e y :=
  ⟨x, h.symm⟩
lemma IsLink.inc_right' (h : G.IsLink e x y) : G.Inc e y := by
  smt +mono [IsLink.inc_left, IsLink.symm, h]
lemma IsLink.inc_right'' (h : G.IsLink e x y) : G.Inc e y := by
  auto [IsLink.inc_left, IsLink.symm, h]



lemma Inc.eq_or_eq_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq h'
lemma Inc.eq_or_eq_of_isLink' (h : G.Inc e x) (h' : G.IsLink e y z) : x = y ∨ x = z := by
  smt +mono [IsLink.left_eq_or_eq, Inc.vertex_mem, h]
lemma Inc.eq_or_eq_of_isLink'' (h : G.Inc e x) (h' : G.IsLink e y z) : x = y ∨ x = z := by
  auto [IsLink.left_eq_or_eq, Inc.vertex_mem, h]


lemma Inc.eq_of_isLink_of_ne_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id
lemma Inc.eq_of_isLink_of_ne_left' (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x ≠ y) : x = z := by
  smt +mono [Inc.eq_or_eq_of_isLink,h,h',hxy]
lemma Inc.eq_of_isLink_of_ne_left'' (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x ≠ y) : x = z := by
  auto [Inc.eq_or_eq_of_isLink,h,h',hxy]


lemma IsLink.isLink_iff_eq (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y :=
  ⟨fun h' ↦ h'.right_unique h, fun h' ↦ h' ▸ h⟩
lemma IsLink.isLink_iff_eq' (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y := by
  smt +mono [IsLink.right_unique,h]
lemma IsLink.isLink_iff_eq'' (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y := by
  auto [IsLink.right_unique,h]


lemma isLink_iff_inc : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq hy'
    · assumption
    exact hy'.symm
  assumption
lemma isLink_iff_inc' : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  smt +mono [IsLink.isLink_iff_eq, Inc.eq_or_eq_of_isLink, Inc.vertex_mem]
lemma isLink_iff_inc'' : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  auto [IsLink.isLink_iff_eq, Inc.eq_or_eq_of_isLink, Inc.vertex_mem]


protected noncomputable def Inc.other (h : G.Inc e x) : α := h.choose
lemma Inc.isLink_other (h : G.Inc e x) : G.IsLink e x h.other :=
  h.choose_spec
lemma Inc.isLink_other' (h : G.Inc e x) : G.IsLink e x h.other := by
  smt +mono [h]
lemma Inc.isLink_other'' (h : G.Inc e x) : G.IsLink e x h.other := by
  auto [h.choose_spec]


lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other :=
  h.isLink_other.inc_right
lemma Inc.inc_other' (h : G.Inc e x) : G.Inc e h.other := by
  smt +mono [Inc.isLink_other]
lemma Inc.inc_other'' (h : G.Inc e x) : G.Inc e h.other := by
  auto [h.isLink_other.inc_right]


lemma Inc.eq_or_eq_or_eq (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! hcon
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hcon.1.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hcon.2.1.symm
  exact hcon.2.2 rfl
lemma Inc.eq_or_eq_or_eq' (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  smt +mono [Inc.eq_of_isLink_of_ne_left, Inc.eq_or_eq_of_isLink, Inc.vertex_mem, hx]
lemma Inc.eq_or_eq_or_eq'' (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  auto [Inc.eq_of_isLink_of_ne_left, Inc.eq_or_eq_of_isLink, Inc.vertex_mem, hx]


def IsLoopAt (G : Graph' α β) (e : β) (x : α) : Prop := G.IsLink e x x
--26
lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl
lemma isLink_self_iff' : G.IsLink e x x ↔ G.IsLoopAt e x := by smt +mono [Iff.rfl]
lemma isLink_self_iff'' : G.IsLink e x x ↔ G.IsLoopAt e x := by auto [Iff.rfl]


lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  IsLink.inc_left h
lemma IsLoopAt.inc' (h : G.IsLoopAt e x) : G.Inc e x := by
  smt +mono [IsLink.inc_left, h]
lemma IsLoopAt.inc'' (h : G.IsLoopAt e x) : G.Inc e x := by
  auto [IsLink.inc_left, h]


lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl
lemma IsLoopAt.eq_of_inc' (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  smt +mono [Inc.eq_or_eq_of_isLink, h, h']
lemma IsLoopAt.eq_of_inc'' (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  auto [Inc.eq_or_eq_of_isLink, h, h']


lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem
lemma IsLoopAt.edge_mem' (h : G.IsLoopAt e x) : e ∈ E(G) := by
  smt +mono [Inc.edge_mem, IsLoopAt.inc, h]
lemma IsLoopAt.edge_mem'' (h : G.IsLoopAt e x) : e ∈ E(G) := by
  auto [Inc.edge_mem, IsLoopAt.inc, h]


lemma IsLoopAt.vertex_mem (h : G.IsLoopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem
lemma IsLoopAt.vertex_mem' (h : G.IsLoopAt e x) : x ∈ V(G) := by
  smt +mono [Inc.vertex_mem, IsLoopAt.inc]
lemma IsLoopAt.vertex_mem'' (h : G.IsLoopAt e x) : x ∈ V(G) := by
  auto [Inc.vertex_mem, IsLoopAt.inc]


def IsNonloopAt (G : Graph' α β) (e : β) (x : α) : Prop := ∃ y ≠ x, G.IsLink e x y
lemma IsNonloopAt.inc (h : G.IsNonloopAt e x) : G.Inc e x :=
  h.choose_spec.2.inc_left
lemma IsNonloopAt.inc' (h : G.IsNonloopAt e x) : G.Inc e x := by
  smt +mono [Exists.choose_spec,IsLink.inc_left,h,Inc.vertex_mem]
lemma IsNonloopAt.inc'' (h : G.IsNonloopAt e x) : G.Inc e x := by
  auto [Exists.choose_spec,IsLink.inc_left,h,Inc.vertex_mem]


lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem
lemma IsNonloopAt.edge_mem' (h : G.IsNonloopAt e x) : e ∈ E(G) := by
  smt +mono [Inc.edge_mem, IsNonloopAt.inc, h]
lemma IsNonloopAt.edge_mem'' (h : G.IsNonloopAt e x) : e ∈ E(G) := by
  auto [Inc.edge_mem, IsNonloopAt.inc, h]


lemma IsNonloopAt.vertex_mem (h : G.IsNonloopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem
lemma IsNonloopAt.vertex_mem' (h : G.IsNonloopAt e x) : x ∈ V(G) := by
  smt +mono [Inc.vertex_mem, IsNonloopAt.inc, h]
lemma IsNonloopAt.vertex_mem'' (h : G.IsNonloopAt e x) : x ∈ V(G) := by
  auto [Inc.vertex_mem, IsNonloopAt.inc, h]


lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  rintro ⟨z, hyz, hy⟩
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl
lemma IsLoopAt.not_isNonloopAt' (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  smt +mono [IsLoopAt.eq_of_inc, IsLink.inc_left, IsLink.inc_right, Inc.vertex_mem, h]
lemma IsLoopAt.not_isNonloopAt'' (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  auto [IsLoopAt.eq_of_inc, IsLink.inc_left, IsLink.inc_right, Inc.vertex_mem, h]



lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloopAt x h
lemma IsNonloopAt.not_isLoopAt' (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y := by
  smt +mono [IsLoopAt.not_isNonloopAt, h]
lemma IsNonloopAt.not_isLoopAt'' (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y := by
  auto [IsLoopAt.not_isNonloopAt, h]


lemma isNonloopAt_iff_inc_not_isLoopAt : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsLoopAt e x :=
  ⟨fun h ↦ ⟨h.inc, h.not_isLoopAt _⟩, fun ⟨⟨y, hy⟩, hn⟩ ↦ ⟨y, mt (fun h ↦ h ▸ hy) hn, hy⟩⟩
lemma isNonloopAt_iff_inc_not_isLoopAt' : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsLoopAt e x := by
  smt +mono [IsNonloopAt.inc, IsLoopAt.not_isNonloopAt, IsNonloopAt.not_isLoopAt,IsNonloopAt.vertex_mem]
lemma isNonloopAt_iff_inc_not_isLoopAt'' : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsLoopAt e x := by
  auto [IsNonloopAt.inc, IsLoopAt.not_isNonloopAt, IsNonloopAt.not_isLoopAt,IsNonloopAt.vertex_mem]



lemma isLoopAt_iff_inc_not_isNonloopAt : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x := by
  simp +contextual [isNonloopAt_iff_inc_not_isLoopAt, iff_def, IsLoopAt.inc]
lemma isLoopAt_iff_inc_not_isNonloopAt' : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x := by
  smt +mono [isNonloopAt_iff_inc_not_isLoopAt, IsLoopAt.inc]
lemma isLoopAt_iff_inc_not_isNonloopAt'' : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x := by
  auto [isNonloopAt_iff_inc_not_isLoopAt, IsLoopAt.inc]


lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  simp [isNonloopAt_iff_inc_not_isLoopAt, h, em]
lemma Inc.isLoopAt_or_isNonloopAt' (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  smt +mono [isNonloopAt_iff_inc_not_isLoopAt, h]
lemma Inc.isLoopAt_or_isNonloopAt'' (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  auto [isNonloopAt_iff_inc_not_isLoopAt, h]


def Adj (G : Graph' α β) (x y : α) : Prop := ∃ e, G.IsLink e x y

protected lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩
protected lemma Adj.symm' (h : G.Adj x y) : G.Adj y x := by
  smt +mono [IsLink.symm, Exists.intro, h]
protected lemma Adj.symm'' (h : G.Adj x y) : G.Adj y x := by
  auto [IsLink.symm, Exists.intro, h]


lemma adj_comm (x y) : G.Adj x y ↔ G.Adj y x :=
  ⟨.symm, .symm⟩
lemma adj_comm' (x y) : G.Adj x y ↔ G.Adj y x := by
  smt +mono [Adj.symm]
lemma adj_comm'' (x y) : G.Adj x y ↔ G.Adj y x := by
  auto [Adj.symm]


lemma Adj.left_mem (h : G.Adj x y) : x ∈ V(G) :=
  h.choose_spec.left_mem
lemma Adj.left_mem' (h : G.Adj x y) : x ∈ V(G) := by
  smt +mono [IsLink.left_mem, Exists.choose_spec, h]
lemma Adj.left_mem'' (h : G.Adj x y) : x ∈ V(G) := by
  auto [IsLink.left_mem, Exists.choose_spec, h]


lemma Adj.right_mem (h : G.Adj x y) : y ∈ V(G) :=
  h.symm.left_mem
lemma Adj.right_mem' (h : G.Adj x y) : y ∈ V(G) := by
  smt +mono [Adj.symm, Adj.left_mem, h]
lemma Adj.right_mem'' (h : G.Adj x y) : y ∈ V(G) := by
  auto [Adj.symm, Adj.left_mem, h]


lemma IsLink.adj (h : G.IsLink e x y) : G.Adj x y :=
  ⟨e, h⟩
lemma IsLink.adj' (h : G.IsLink e x y) : G.Adj x y := by
  smt +mono [Exists.intro, h]
lemma IsLink.adj'' (h : G.IsLink e x y) : G.Adj x y := by
  auto [Exists.intro, h]


lemma mk_eq_self (G : Graph' α β) {E : Set β} (hE : ∀ e, e ∈ E ↔ ∃ x y, G.IsLink e x y) :
    Graph'.mk V(G) G.IsLink E
    (by simpa [show E = E(G) by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]]
      using G.isLink_symm)
    (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq h') hE
    (fun _ _ _ ↦ IsLink.left_mem) = G := by
  obtain rfl : E = E(G) := by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
  cases G with | _ _ _ _ _ _ h _ => simp
lemma mk_eq_self' (G : Graph' α β) {E : Set β} (hE : ∀ e, e ∈ E ↔ ∃ x y, G.IsLink e x y) :
    Graph'.mk V(G) G.IsLink E
    (by simpa [show E = E(G) by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]]
      using G.isLink_symm)
    (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq h') hE
    (fun _ _ _ ↦ IsLink.left_mem) = G := by
  smt +mono [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
lemma mk_eq_self'' (G : Graph' α β) {E : Set β} (hE : ∀ e, e ∈ E ↔ ∃ x y, G.IsLink e x y) :
    Graph'.mk V(G) G.IsLink E
    (by simpa [show E = E(G) by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]]
      using G.isLink_symm)
    (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq h') hE
    (fun _ _ _ ↦ IsLink.left_mem) = G := by
  auto [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]-- 超时



protected lemma ext {G₁ G₂ : Graph' α β} (hV : V(G₁) = V(G₂))
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink, ← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
  convert rfl using 2
  · exact hV.symm
  · simp [funext_iff, h]
  simp [edgeSet_eq_setOf_exists_isLink, h]
protected lemma ext' {G₁ G₂ : Graph' α β} (hV : V(G₁) = V(G₂))
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  smt +mono [mk_eq_self, edgeSet_eq_setOf_exists_isLink, funext_iff, h, hV]
protected lemma ext'' {G₁ G₂ : Graph' α β} (hV : V(G₁) = V(G₂))
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  auto [mk_eq_self, edgeSet_eq_setOf_exists_isLink, funext_iff, h, hV]



lemma ext_inc {G₁ G₂ : Graph' α β} (hV : V(G₁) = V(G₂)) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph'.ext hV fun _ _ _ ↦ by simp_rw [isLink_iff_inc, h]
lemma ext_inc' {G₁ G₂ : Graph' α β} (hV : V(G₁) = V(G₂)) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ := by
  smt +mono [ext, isLink_iff_inc, mk_eq_self, h, hV]
lemma ext_inc'' {G₁ G₂ : Graph' α β} (hV : V(G₁) = V(G₂)) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ := by
  auto [ext, isLink_iff_inc, mk_eq_self, h, hV]


def incidenceSet (x : α) : Set β := {e | G.Inc e x}
theorem mem_incidenceSet (x : α) (e : β) : e ∈ G.incidenceSet x ↔ G.Inc e x :=
  Iff.rfl
theorem mem_incidenceSet' (x : α) (e : β) : e ∈ G.incidenceSet x ↔ G.Inc e x := by
  smt +mono [rfl]
theorem mem_incidenceSet'' (x : α) (e : β) : e ∈ G.incidenceSet x ↔ G.Inc e x := by
  auto [rfl]


theorem incidenceSet_subset_edgeSet (x : α) : G.incidenceSet x ⊆ E(G) :=
  fun _ ⟨_, hy⟩ ↦ hy.edge_mem
theorem incidenceSet_subset_edgeSet' (x : α) : G.incidenceSet x ⊆ E(G) := by
  smt +mono [Inc.edge_mem, mem_incidenceSet, Set.subset_def]
theorem incidenceSet_subset_edgeSet'' (x : α) : G.incidenceSet x ⊆ E(G) := by
  auto [Inc.edge_mem, mem_incidenceSet, Set.subset_def]


def loopSet (x : α) : Set β := {e | G.IsLoopAt e x}
theorem mem_loopSet (x : α) (e : β) : e ∈ G.loopSet x ↔ G.IsLoopAt e x :=
  Iff.rfl
theorem mem_loopSet' (x : α) (e : β) : e ∈ G.loopSet x ↔ G.IsLoopAt e x := by
  smt +mono [rfl]
theorem mem_loopSet'' (x : α) (e : β) : e ∈ G.loopSet x ↔ G.IsLoopAt e x := by
  auto [rfl]


theorem loopSet_subset_incidenceSet (x : α) : G.loopSet x ⊆ G.incidenceSet x := fun _ he ↦ ⟨x, he⟩
theorem loopSet_subset_incidenceSet' (x : α) : G.loopSet x ⊆ G.incidenceSet x := by
  smt +mono [mem_loopSet, mem_incidenceSet, Set.subset_def]
theorem loopSet_subset_incidenceSet'' (x : α) : G.loopSet x ⊆ G.incidenceSet x := by
  auto [mem_loopSet, mem_incidenceSet, Set.subset_def]

end Graph'
