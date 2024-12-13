import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
-- import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Group.Bounds

namespace Example3

class CompletePartialOrder (α: Type*) extends PartialOrder α, SupSet α where
  lubOfDirected : ∀ d, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d (sSup d)

@[ext]
structure ClosedInterval where
  left : ℝ
  right : ℝ
  ordered : left ≤ right

instance : PartialOrder ClosedInterval where
  -- i₂ ⊆ i₁ ↔ i₁ ≤ i₂ (reverse inclusion)
  le := fun i₁ i₂ => i₁.left ≤ i₂.left ∧ i₂.right ≤ i₁.right
  le_refl := fun _ => ⟨le_refl _, le_refl _⟩
  le_trans := fun _ _ _ i₁ i₂ => ⟨le_trans i₁.left i₂.left, le_trans i₂.right i₁.right⟩
  le_antisymm := fun _ _ i₁ i₂ => by
    ext
    · exact le_antisymm i₁.left i₂.left
    · exact le_antisymm i₂.right i₁.right

lemma lub_ClosedInterval (s : Set ClosedInterval) (lub: ClosedInterval) : IsLUB (ClosedInterval.left '' s) lub.left → IsGLB (ClosedInterval.right '' s) lub.right → IsLUB s lub := by
  intro hleft hright
  simp [IsLUB, upperBounds, IsLeast, lowerBounds, IsGLB, IsGreatest] at hleft hright ⊢
  obtain ⟨hleft₁, hleft₂⟩ := hleft
  obtain ⟨hright₁, hright₂⟩ := hright
  constructor
  · intro i hi
    constructor
    · exact hleft₁ i hi
    · exact hright₁ i hi
  · intro ub hub
    constructor
    · apply hleft₂
      intro i hi
      exact (hub hi).left
    · apply hright₂
      intro i hi
      exact (hub hi).right

noncomputable instance : CompletePartialOrder ClosedInterval where
  sSup := by
    intro s
    by_cases hbounded : BddAbove (ClosedInterval.left '' s) ∧ BddBelow (ClosedInterval.right '' s) ∧ s.Nonempty
    · have hlub := Real.exists_isLUB (Set.Nonempty.image ClosedInterval.left hbounded.right.right) hbounded.left
      have hglb := Real.exists_isGLB (Set.Nonempty.image ClosedInterval.right hbounded.right.right) hbounded.right.left
      let x := hlub.choose
      let x' := hglb.choose
      exact {
      left := by
        exact hlub.choose
      right := by
        by_cases x ≤ x'
        · exact x'
        · exact x
      ordered := by
        by_cases h' : x ≤ x' <;>
          simp [h']
    }
    · exact ⟨0, 0, (by linarith)⟩

  lubOfDirected := by
    intro s hs hdir
    by_cases hbounded : BddAbove (ClosedInterval.left '' s) ∧ BddBelow (ClosedInterval.right '' s) ∧ s.Nonempty
    · have hlub := Real.exists_isLUB (Set.Nonempty.image ClosedInterval.left hbounded.right.right) hbounded.left
      have hglb := Real.exists_isGLB (Set.Nonempty.image ClosedInterval.right hbounded.right.right) hbounded.right.left
      let x := hlub.choose
      let x' := hglb.choose
      let hx := hlub.choose_spec
      let hx' := hglb.choose_spec
      by_cases h : x ≤ x'
      · simp [sSup, h, hs]
        apply lub_ClosedInterval
        all_goals simp [hbounded]
        exact hx
        exact hx'
      · simp [DirectedOn] at h hdir
        let ε := (x - x') / 3
        have hε₁ : 0 < ε := by
          simp [ε]
          exact h
        have hε₂ : x' + ε < x - ε := by
          simp [ε]
          linarith

        have h₁ : ∃ l ∈ ClosedInterval.left '' s, x - ε < l ∧ l ≤ x := IsLUB.exists_between_sub_self hx hε₁
        have h₂ : ∃ r ∈ ClosedInterval.right '' s, x' ≤ r ∧ r < x' + ε := IsGLB.exists_between_self_add hx' hε₁

        obtain ⟨l, hl, _, _⟩ := h₁
        obtain ⟨r, hr, _, _⟩ := h₂
        obtain ⟨i₁, hi₁₁, hi₁₂⟩ := hl
        obtain ⟨i₂, hi₂₁, hi₂₂⟩ := hr

        obtain ⟨i, _, h₅, h₆⟩ := hdir i₁ hi₁₁ i₂ hi₂₁
        obtain ⟨h₇, _⟩ := h₅
        obtain ⟨_, h₁₀⟩ := h₆
        linarith [i.ordered]

    · simp at hbounded
      by_cases h : ¬s.Nonempty
      · contradiction
      · simp [h] at hbounded
        simp [DirectedOn] at h hdir
        obtain ⟨i₁, hi₁⟩ := h
        by_cases h : ¬BddBelow (ClosedInterval.right '' s)
        · simp [BddBelow, lowerBounds] at h
          have h : ∀ x, ∃ y ∈ s, y.right < x := by
            by_contra h'
            simp at h'
            contradiction
          obtain ⟨i₂, hi₂, hi₁₂⟩ := h i₁.left
          obtain ⟨i, _, h₅, h₆⟩ := hdir i₁ hi₁ i₂ hi₂
          obtain ⟨h₇, _⟩ := h₅
          obtain ⟨_, h₁₀⟩ := h₆
          linarith [i.ordered]
        · simp [h, BddAbove, upperBounds] at hbounded
          have h : ∀ x, ∃ y ∈ s, x < y.left := by
            by_contra h'
            simp at h'
            contradiction
          obtain ⟨i₂, hi₂, hi₁₂⟩ := h i₁.right
          obtain ⟨i, _, h₅, h₆⟩ := hdir i₁ hi₁ i₂ hi₂
          obtain ⟨_, h₈⟩ := h₅
          obtain ⟨h₉, _⟩ := h₆
          linarith [i.ordered]








end Example3
