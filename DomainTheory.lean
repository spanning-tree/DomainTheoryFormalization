import Mathlib.Order.Basic
import Mathlib.Order.Directed
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Order.ScottTopology

import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.OmegaCompletePartialOrder

namespace DomainTheory


/-
**TODO**: follow Mathlib's style guide
-/

/-
## References

* Abramsky, Samson, and Achim Jung. "Domain theory." (1994).
* Goubault-Larrecq, Jean. Non-Hausdorff topology and domain theory: Selected topics in point-set topology. Vol. 22. Cambridge University Press, 2013.

-/

#check DirectedOn
#check CompletePartialOrder

-- Under the definition of `DirectedOn`, the empty set is directed
lemma empty_set_is_directed {α : Type*} [Preorder α] : DirectedOn (· ≤ ·) (∅ : Set α) := by
  rw [DirectedOn]
  simp

-- In domain theory, we always want the directed set to be nonempty

-- If D is a complete partial order, then D must have a bottom element. Because the empty set is directed and has a least upper bound.
lemma complete_partial_order_has_bottom {α : Type*} [CompletePartialOrder α] : ∃ x : α, IsBot x := by
  have h₁ : DirectedOn (· ≤ ·) (∅ : Set α) := by
    rw [DirectedOn]
    simp
  have h₂: IsLUB ∅ (sSup ∅) := CompletePartialOrder.lubOfDirected ∅ h₁
  use sSup ∅
  rw [IsLUB, IsLeast, upperBounds, lowerBounds] at h₂
  simp at h₂
  exact h₂

/-
We want a more general cases, where the bottom element does not necessarily exist. So we define the class Dcpo (directed complete partial order).
-/

/-- Definition 2.1.13 -/
class Dcpo (α: Type*) extends PartialOrder α, SupSet α where
  lubOfDirected : ∀ d, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d (sSup d)

lemma lub_is_upperbound {α: Type*} [Preorder α] (d : Set α) (sup : α) (hlub : IsLUB d sup) : ∀ x, x ∈ d → x ≤ sup := by
  intro h hd
  rw [IsLUB, upperBounds, IsLeast] at hlub
  simp at hlub
  exact hlub.left hd

/-- Definition 2.2.1 -/
def WayBelow {α : Type*} [Dcpo α] (x y : α) : Prop :=
 ∀ d, d.Nonempty → DirectedOn (· ≤ ·) d → y ≤ sSup d → ∃ x' ∈ d, x ≤ x'

infix:50 " ≪ " => WayBelow

-- the way-below relation implies the less-than relation
/-- Proposition 2.2.2 -/
lemma way_below_implies_less_than {α : Type*} [Dcpo α] (x y: α): x ≪ y → x ≤ y := by
  intro h
  rw [WayBelow] at h
  let d : Set α := {y}
  have hd : d.Nonempty ∧ DirectedOn (· ≤ ·) d := by
    apply And.intro
    exact Set.singleton_nonempty y
    refine directedOn_singleton IsRefl.reflexive y
  have hyX : y ≤ sSup d := by
    have h1 : y ∈ d := by exact Set.mem_singleton y
    have h3 : _ := Dcpo.lubOfDirected d hd.left hd.right
    exact lub_is_upperbound d (sSup d) h3 y h1
  have h : _ := h d hd.left hd.right hyX
  let ⟨d, hd1, hd2⟩ := h
  exact le_of_le_of_eq hd2 hd1

-- x₁ ≤ x₂ ≪ y₂ ≤ y₁ → x₁ ≪ y₁
/-- Proposition 2.2.2 -/
lemma way_below_transitive_strong {α : Type*} [Dcpo α] (x₁ x₂ y₂ y₁: α): x₁ ≤ x₂ → y₂ ≤ y₁ → x₂ ≪ y₂ → x₁ ≪ y₁ := by
  intro h1 h2 h3
  rw [WayBelow] at h3
  intro d hnonempty hd hsup
  have : y₂ ≤ sSup d := Preorder.le_trans y₂ y₁ (sSup d) h2 hsup
  have : _ := h3 d hnonempty hd this
  obtain ⟨d, hd1, hd2⟩ := this
  use d
  apply And.intro hd1
  exact Preorder.le_trans x₁ x₂ d h1 hd2

-- the way-below relation is transitive
lemma way_below_transitive {α : Type*} [Dcpo α] (x y z: α): x ≪ y → y ≪ z → x ≪ z := by
  intro h1 h2
  have h3 : x ≤ y := by exact way_below_implies_less_than x y h1
  have h4 : z ≤ z := by exact Preorder.le_refl z
  exact way_below_transitive_strong x y z z h3 h4 h2

-- I dont know the exact English name of ↡ x, as in the literature, it is usually written in the form of ↡ x
-- **TODO**: check the exact name of ↡ x
/-- Definition 2.2.1 -/
def approximant {α : Type*} [Dcpo α] (x: α) : Set α := { a: α | a ≪ x }

prefix:80 " ↡ " => approximant

-- x is an upper bound of ↡x
lemma approximant_upper_bound {α : Type*} [Dcpo α] (x: α): x ∈ upperBounds (↡ x) := by
  intro y hy
  exact way_below_implies_less_than y x hy

/-- Definition 2.2.6 -/
class ContinuousDcpo (α : Type*) extends Dcpo α where
  basis: Set α
  nonempty_intersection: ∀ x, (↡ x ∩ basis).Nonempty
  directed_intersection: ∀ x, DirectedOn (· ≤ ·) (↡ x ∩ basis)
  sup_intersection: ∀ x, IsLUB (↡ x ∩ basis) x

/-- Proposition 2.2.7.1 -/
theorem ContinuousDcpo.directed_approximant {α: Type*} [ContinuousDcpo α] (x : α): DirectedOn (· ≤ ·) (↡ x) := by
  rw [DirectedOn]
  intro x₁ hx₁ x₂ hx₂
  have : x = sSup (↡ x ∩ ContinuousDcpo.basis) := by
    apply IsLUB.unique (ContinuousDcpo.sup_intersection x)
    apply Dcpo.lubOfDirected
    exact ContinuousDcpo.nonempty_intersection x
    exact ContinuousDcpo.directed_intersection x
  have : x ≤ sSup (↡ x ∩ ContinuousDcpo.basis) := le_of_eq this

  have hx₁ : x₁ ≪ x := hx₁
  have hx₂ : x₂ ≪ x := hx₂
  rw [WayBelow] at hx₁ hx₂
  have h1 : ∃ x' ∈ ↡ x ∩ ContinuousDcpo.basis, x₁ ≤ x' := hx₁ (↡ x ∩ ContinuousDcpo.basis) (ContinuousDcpo.nonempty_intersection x) (ContinuousDcpo.directed_intersection x) this
  have h2 : ∃ x' ∈ ↡ x ∩ ContinuousDcpo.basis, x₂ ≤ x' := hx₂ (↡ x ∩ ContinuousDcpo.basis) (ContinuousDcpo.nonempty_intersection x) (ContinuousDcpo.directed_intersection x) this
  obtain ⟨y₁, hy₁1, hy₁2⟩ := h1
  obtain ⟨y₂, hy₂1, hy₂2⟩ := h2
  have h3 : ∃ z ∈ (↡ x ∩ ContinuousDcpo.basis), y₁ ≤ z ∧ y₂ ≤ z := by
    exact (ContinuousDcpo.directed_intersection x) y₁ hy₁1 y₂ hy₂1
  obtain ⟨z, hz1, hz2, hz3⟩ := h3
  use z
  constructor
  · exact Set.mem_of_mem_inter_left hz1
  constructor
  · exact Preorder.le_trans x₁ y₁ z hy₁2 hz2
  · exact Preorder.le_trans x₂ y₂ z hy₂2 hz3


/-- Proposition 2.2.7.1 -/
theorem ContinuousDcpo.nonempty_approximant {α: Type*} [ContinuousDcpo α] (x : α): (↡ x).Nonempty := by
  obtain ⟨y, hy⟩ := ContinuousDcpo.nonempty_intersection x
  use y
  exact Set.mem_of_mem_inter_left hy

/-- Proposition 2.2.7.1 -/
theorem ContinuousDcpo.lub_approximate{α: Type*} [ContinuousDcpo α] (x: α) : IsLUB (↡ x) x := by
  let x' := sSup (↡ x)
  have : IsLUB (↡ x) x' := by
    exact Dcpo.lubOfDirected (↡ x) (ContinuousDcpo.nonempty_approximant x) (ContinuousDcpo.directed_approximant x)
  have h1 : x' ≤ x := by
    rw [IsLUB, IsLeast] at this
    obtain ⟨_, this⟩ := this
    exact this (approximant_upper_bound x)
  have h2 : x ≤ x' := by
    apply IsLUB.mono (ContinuousDcpo.sup_intersection x) this Set.inter_subset_left
  have h3 : x = x' := by
    apply PartialOrder.le_antisymm
    exact h2
    exact h1
  rw [← h3] at this
  exact this

lemma nonempty_interpolation_set {α : Type*} [ContinuousDcpo α] (y : α): {w: α | ∃ z: α, w ≪ z ∧ z ≪ y}.Nonempty := by
  have : (↡ y).Nonempty := ContinuousDcpo.nonempty_approximant y
  obtain ⟨z, hz⟩ := this
  have : (↡ z).Nonempty := ContinuousDcpo.nonempty_approximant z
  obtain ⟨w, hw⟩ := this
  use w
  refine Set.mem_setOf.mpr ?h.a
  exact Filter.frequently_principal.mp fun a => a hw hz

lemma directed_interpolation_set {α : Type*} [ContinuousDcpo α] (y: α) : DirectedOn (· ≤ ·) {w: α | ∃ z: α, w ≪ z ∧ z ≪ y} := by
  intro w₁ hw₁ w₂ hw₂
  simp
  obtain ⟨z₁, hz₁⟩ := hw₁
  obtain ⟨z₂, hz₂⟩ := hw₂
  have h1: z₁ ≪ y := by
    apply hz₁.elim
    simp
  have h1: z₁ ∈ ↡ y := h1
  have h2: z₂ ≪ y := by
    apply hz₂.elim
    simp
  have h2: z₂ ∈ ↡ y := h2
  have h3: ∃ u ∈ ↡ y, z₁ ≤ u ∧ z₂ ≤ u := by
    obtain ⟨u, hu⟩ := (ContinuousDcpo.directed_approximant y) z₁ h1 z₂ h2
    use u
  obtain ⟨u, hu⟩ := h3
  have h4: w₁ ∈ ↡ u ∧ w₂ ∈ ↡ u := by
    have h5: w₁ ≪ u := way_below_transitive_strong w₁ w₁ z₁ u (Preorder.le_refl w₁) hu.right.left hz₁.left
    have h6: w₂ ≪ u := way_below_transitive_strong w₂ w₂ z₂ u (Preorder.le_refl w₂) hu.right.right hz₂.left
    exact And.intro h5 h6
  have h5: ∃ z ∈ ↡ u, w₁ ≤ z ∧ w₂ ≤ z := by
    apply (ContinuousDcpo.directed_approximant u)
    exact h4.left
    exact h4.right
  obtain ⟨z, hz⟩ := h5
  use z
  constructor
  · use u
    exact And.intro hz.left hu.left
  · exact hz.right

lemma sup_interpolation_set {α : Type*} [ContinuousDcpo α] (y y': α): IsLUB {w: α | ∃ z: α, w ≪ z ∧ z ≪ y} y' → y ≤ y' := by
  have : ∀ z ∈ ↡y, ∀ x ∈ ↡z, x ∈ {w: α | ∃ z: α, w ≪ z ∧ z ≪ y} := by
    intro z hz x hx
    use z
    apply And.intro hx hz
  have : ∀ y' ∈ upperBounds {w: α | ∃ z: α, w ≪ z ∧ z ≪ y}, ∀ z ∈ ↡y, z ≤ y' := by
    intro y' hy' z hz
    have h : y' ∈ upperBounds (↡ z) := by
      intro x hx
      apply hy'
      exact this z hz x hx
    exact(isLUB_le_iff (ContinuousDcpo.lub_approximate z)).mpr h
  have h: IsLUB (↡y) y := ContinuousDcpo.lub_approximate y
  intro h1
  have h1: y' ∈ upperBounds {w: α | ∃ z: α, w ≪ z ∧ z ≪ y} := by
    exact Set.mem_of_mem_inter_left h1
  have : _ := this y' h1
  have : y' ∈ upperBounds (↡ y) := by
    intro x hx
    apply this x
    exact hx
  apply (isLUB_le_iff h).mpr
  exact this

-- In a continuous Dcpo, we can interpolate between two elements with the way-below relation
theorem exists_way_below_interpolation {α : Type*} [ContinuousDcpo α] (x y: α): x ≪ y → ∃ z: α, x ≪ z ∧ z ≪ y := by
  let D := {w: α | ∃ z: α, w ≪ z ∧ z ≪ y}
  have hsupD: ∀ y', IsLUB D y' → y ≤ y' := by
    intro y' hy'
    exact DomainTheory.sup_interpolation_set y y' hy'
  have hsupD: y ≤ sSup D := by
    apply hsupD
    exact Dcpo.lubOfDirected D (nonempty_interpolation_set y) (directed_interpolation_set y)
  intro hxy
  rw [WayBelow] at hxy
  have : _ := hxy D (nonempty_interpolation_set y) (directed_interpolation_set y) hsupD
  obtain ⟨z, hz1, hz2⟩ := this
  obtain ⟨w, hw⟩ := hz1
  use w
  apply And.intro (way_below_transitive_strong x z w w hz2 (Preorder.le_refl w) hw.left) hw.right

-- I dont know the exact English name of ↟ x, as in the literature, it is usually written in the form of ↟ x
-- **TODO**: check the exact name of ↟ x
/-- Definition 2.2.1 -/
def upward {α : Type*} [Dcpo α] (x: α) : Set α := { a: α | x ≪ a }

prefix:80 " ↟ " => upward

lemma upward_dir_sup_in_acc {α : Type*} [ContinuousDcpo α] (x: α): DirSupInacc (↟x) := by
  rw [DirSupInacc]
  intro Z hZ1 hZ2 z hz hxz
  have hxz : x ≪ z := hxz
  have hy : _ := exists_way_below_interpolation x z hxz
  obtain ⟨y, hy1, hy2⟩ := hy
  rw [WayBelow] at hy1
  have : IsLUB Z (sSup Z) := Dcpo.lubOfDirected Z hZ1 hZ2
  have : z ≤ sSup Z := by
    exact IsLUB.mono hz this fun ⦃a⦄ a => a
  have : ∃ y' ∈ Z, y ≤ y' := by
    exact hy2 Z hZ1 hZ2 this
  obtain ⟨y', hy'1, hy'2⟩ := this
  use y'
  apply And.intro hy'1
  apply way_below_transitive_strong x x y y' (Preorder.le_refl x) hy'2 hy1

lemma upward_is_upper_set {α : Type*} [ContinuousDcpo α] (x: α): IsUpperSet (↟ x) := by
  rw [IsUpperSet]
  intro y z hyz hy
  apply way_below_transitive_strong x x y z (Preorder.le_refl x) hyz hy

#check Topology.scott

#check Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInacc

#check Topology.IsScott

-- In a continuous Dcpo, ↟ x is an open set in the Scott topology
theorem upward_is_open_set {α : Type*} [ContinuousDcpo α] [TopologicalSpace α] [Topology.IsScott α] (x: α) : IsOpen (↟ x) := by
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInacc]
  exact And.intro (upward_is_upper_set x) (upward_dir_sup_in_acc x)

lemma upper_dirSupInacc_set_is_union_upward {α : Type*} [ContinuousDcpo α] (X: Set α) (hX: IsUpperSet X ∧ DirSupInacc X): X = ⋃₀ {↟ x | x ∈ X} := by
  obtain ⟨hupper, hdirsup⟩ := hX
  apply Set.eq_of_subset_of_subset
  · rw [Set.subset_def]
    intro x hx
    let X' := ↡ x
    have hsupX' : IsLUB X' x := ContinuousDcpo.lub_approximate x
    rw [DirSupInacc] at hdirsup
    have h1 : _ := hdirsup (ContinuousDcpo.nonempty_approximant x) (ContinuousDcpo.directed_approximant x) hsupX' hx
    obtain ⟨y, hy1, hy2⟩ := h1
    refine Set.mem_sUnion.mpr ?_
    use ↟y
    apply And.intro
    {use y}
    · have : y ≪ x := hy1
      exact this
  · rw [Set.subset_def]
    intro x hx
    rw [@Set.mem_sUnion] at hx
    obtain ⟨X', hX'1, hX'2⟩ := hx
    obtain ⟨y, hy1, hy2⟩ := hX'1
    have : y ≪ x := by
      rw [← hy2] at hX'2
      exact hX'2
    have : y ≤ x := by
      exact way_below_implies_less_than y x this
    exact hupper this hy1

-- In a continuous Dcpo, every open set is a union of upward sets
/-- Proposition 2.3.6.1 -/
theorem open_set_iff_union_upward {α : Type*} [ContinuousDcpo α] [TopologicalSpace α] [Topology.IsScott α] (X: Set α): IsOpen X ↔ X = ⋃₀ {↟ x | x ∈ X} := by
  constructor
  · intro hopen
    rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInacc] at hopen
    exact upper_dirSupInacc_set_is_union_upward X hopen
  · have : ∀ Y ∈ {x | ∃ x_1 ∈ X, ↟ x_1 = x}, IsOpen Y := by
      intro Y hY
      obtain ⟨x, _, hx2⟩ := hY
      rw [← hx2]
      exact upward_is_open_set x
    intro h
    rw [h]
    exact isOpen_sUnion this

-- **TODO**: should we define the topological space explicitly?

class ωContinuousDcpo (α : Type) extends ContinuousDcpo α where
  countable_basis: Set.Countable basis

/-- A pointed Dcpo is a Dcpo with a bottom element. -/
class PointedDcpo (α : Type*) extends Dcpo α, OrderBot α

-- Actually Pointed Dcpo is equivalent to the definition of `CompletePartialOrder`

noncomputable def PointedDcpo_to_CompletePartialOrder {α: Type*} [PointedDcpo α] : CompletePartialOrder α :=
  {
    sSup := by
      intro d
      by_cases d.Nonempty
      exact PointedDcpo.toDcpo.sSup d
      exact ⊥
    lubOfDirected := by
      intro d
      by_cases hd: d.Nonempty
      · intro h
        rw [sSup]
        simp [hd]
        exact PointedDcpo.toDcpo.lubOfDirected d hd h
      · have hd: d = ∅ := Set.not_nonempty_iff_eq_empty.mp hd
        intro _
        rw [sSup]
        simp [hd]
  }

def CompletePartialOrder_to_PointedDcpo {α: Type*} [CompletePartialOrder α] : PointedDcpo α :=
  {
    lubOfDirected := by
      intro d _ hd2
      exact CompletePartialOrder.lubOfDirected d hd2
    bot := sSup ∅
    bot_le := by
      have h1: DirectedOn (· ≤ ·) (∅: Set α) := by
        rw [DirectedOn]
        simp
      have h2: IsLUB ∅ (sSup ∅) := CompletePartialOrder.lubOfDirected ∅ h1
      rw [IsLUB, IsLeast, upperBounds, lowerBounds] at h2
      simp at h2
      exact h2
  }

#check OmegaCompletePartialOrder.Chain
#check ScottContinuous

-- f^[n] ⊥ ≤ f^[n + 1] ⊥
lemma continuous_function_iteration_monotone {α: Type*} [PointedDcpo α] (f: α → α) (hf: ScottContinuous f): ∀ n : ℕ, f^[n] ⊥  ≤ f^[n + 1] ⊥ := by
  have hmonotone : Monotone f := hf.monotone
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp
    have : f^[n] (f ⊥) = f (f^[n] ⊥) := by
      apply Function.iterate_succ_apply' f n
    rw [this]
    have : f^[n] (f (f ⊥)) = f (f^[n + 1] ⊥) := by
      apply Function.iterate_succ_apply' f n (f ⊥)
    rw [this]
    apply hmonotone
    exact ih

-- f^[n] ⊥ ≤ f^[m] ⊥ for n ≤ m
lemma continuous_function_iteration_monotone_strong {α: Type*} [PointedDcpo α] (f: α → α) (hf: ScottContinuous f): ∀ n m : ℕ, n ≤ m → f^[n] ⊥ ≤ f^[m] ⊥ := by
  intro n m hnm
  induction hnm with
      | refl => exact Preorder.le_refl (f^[n] ⊥)
      | step hnm ih =>
        rename_i M
        simp at hnm
        have : f^[M] ⊥ ≤ f^[M + 1] ⊥ := by
          exact continuous_function_iteration_monotone f hf M
        exact Preorder.le_trans (f^[n] ⊥) (f^[M] ⊥) (f^[M.succ] ⊥) ih this


-- The iteration of a continuous function with the bottom element is a chain
def continuous_function_iteration_is_chain {α: Type*} [PointedDcpo α] (f: α → α) (hf: ScottContinuous f): OmegaCompletePartialOrder.Chain α := by
  exact
  {
    toFun := fun n => (f^[n] ⊥)
    monotone' := by
      rw [Monotone]
      exact fun ⦃a b⦄ a_1 => continuous_function_iteration_monotone_strong f hf a b a_1
  }

lemma chain_is_directed {α: Type*} [Preorder α] (c: OmegaCompletePartialOrder.Chain α): (Set.range c).Nonempty ∧ DirectedOn (· ≤ ·) (Set.range c) := by
  rw [Set.range]
  constructor
  · use c 0
    simp
  · rw [DirectedOn]
    simp
    intro i j
    let k := max i j
    use k
    constructor
    · apply c.monotone
      exact le_max_left i j
    · apply c.monotone
      exact le_max_right i j

lemma continuous_function_iteration_is_nonempty {α: Type*} [PointedDcpo α] (f: α → α) (hf: ScottContinuous f): (Set.range (continuous_function_iteration_is_chain f hf)).Nonempty := by
  exact (chain_is_directed (continuous_function_iteration_is_chain f hf)).left

lemma continuous_function_iteration_is_directed {α: Type*} [PointedDcpo α] (f: α → α) (hf: ScottContinuous f): DirectedOn (· ≤ ·) (Set.range (continuous_function_iteration_is_chain f hf)) := by
  exact (chain_is_directed (continuous_function_iteration_is_chain f hf)).right

def least_fixpoint {α: Type*} [PointedDcpo α] (f: α → α) (hf: ScottContinuous f): α := by
  let c : OmegaCompletePartialOrder.Chain α := continuous_function_iteration_is_chain f hf
  exact sSup (Set.range c)

-- **TODO**: Generalize this to OmegaCompletePartialOrder
/-- Theorem 2.1.19.1 -/
theorem least_fixpoint_is_fixpoint {α: Type*} [PointedDcpo α] (f: α → α) (hf: ScottContinuous f): f (least_fixpoint f hf) = (least_fixpoint f hf) := by
  rw [least_fixpoint]
  let s := Set.range (continuous_function_iteration_is_chain f hf)
  simp
  show f (sSup s) = sSup s
  have hlubs : IsLUB s (sSup s) := Dcpo.lubOfDirected s (continuous_function_iteration_is_nonempty f hf) (continuous_function_iteration_is_directed f hf)
  rw [ScottContinuous] at hf
  have hlubfs : _ := hf (continuous_function_iteration_is_nonempty f hf) (continuous_function_iteration_is_directed f hf) hlubs
  have hfs: ∀ x ∈ s, ∃ n : ℕ, x = f^[n] ⊥ := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    use n
    exact (Eq.symm hn)

  have h1: f '' s ⊆ s := by
    rw [Set.image]
    refine Set.setOf_subset.mpr ?_
    intro x hx
    obtain ⟨a, ha⟩ := hx
    have : _ := hfs a ha.left
    obtain ⟨n, hn⟩ := this
    have : f (f^[n] ⊥) = x := by
      rw [hn] at ha
      exact ha.right
    have : f^[n + 1] ⊥ = x := by
      rw [Function.iterate_succ_apply' f n ⊥]
      exact this
    rw [← this]
    use n + 1
    exact rfl

  have h1 : f (sSup s) ≤ sSup s := by
    exact IsLUB.mono hlubfs hlubs h1

  have h2: ∀ x ∈ s, x ≤ f x := by
      intro x hx
      obtain ⟨n, hn⟩ := hfs x hx
      have : f (f^[n] ⊥) = f x := by
        rw [hn] at hx
        exact congrArg f (id (Eq.symm hn))
      have : f^[n + 1] ⊥ = f x := by
        rw [Function.iterate_succ_apply' f n ⊥]
        exact this
      rw [← this]
      rw [hn]
      exact continuous_function_iteration_monotone f hf n

  have h2: ∀ x ∈ s, ∃ x' ∈ f '' s, x ≤ x' := by
    intro x hx
    use f x
    apply And.intro
    exact Set.mem_image_of_mem f hx
    exact h2 x hx

  have h2 : ∀ x ∈ s, x ≤ f (sSup s) := by
    intro x hx
    obtain ⟨x', hx'1, hx'2⟩ := h2 x hx
    have : x' ≤ f (sSup s) := by
      exact lub_is_upperbound (f '' s) (f (sSup s)) hlubfs x' hx'1
    exact Preorder.le_trans x x' (f (sSup s)) hx'2 this

  have h2 : sSup s ≤ f (sSup s) := by
    exact (isLUB_le_iff hlubs).mpr h2

  apply PartialOrder.le_antisymm
  · exact h1
  · exact h2

/-- Theorem 2.1.19.1 -/
theorem least_fixpoint_is_least {α: Type*} [PointedDcpo α] (f: α → α) (hf: ScottContinuous f) (x: α): f x = x → least_fixpoint f hf ≤ x := by
  intro hfix
  have hmonotone : Monotone f := hf.monotone

  have h: ∀ n, f^[n] ⊥ ≤ x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        f^[n + 1] ⊥ = f (f^[n] ⊥) := by
          apply Function.iterate_succ_apply' f n ⊥
        _ ≤ f x := by
          apply hmonotone
          exact ih
        _ = x := by
          exact hfix

  have h: ∀ x' ∈ Set.range (continuous_function_iteration_is_chain f hf), x' ≤ x := by
    intro x' hx'
    obtain ⟨n, hn⟩ := hx'
    rw [← hn]
    exact h n

  exact (isLUB_le_iff (Dcpo.lubOfDirected (Set.range (continuous_function_iteration_is_chain f hf)) (continuous_function_iteration_is_nonempty f hf) (continuous_function_iteration_is_directed f hf))).mpr h


/-- **TODO**: Proposition 2.1.16 -/
theorem monotone_function_has_fixpoint {α: Type} [PointedDcpo α] (f: α → α) (hf: Monotone f): ∃ x: α, f x = x := sorry










end DomainTheory
