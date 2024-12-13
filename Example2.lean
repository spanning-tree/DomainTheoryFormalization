import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Group.Bounds

namespace Example2

class CompletePartialOrder (α: Type*) extends PartialOrder α, SupSet α, OrderBot α where
  lubOfDirected : ∀ d, DirectedOn (· ≤ ·) d → IsLUB d (sSup d)

@[ext]
structure ClosedInterval where
  left : ℝ
  right : ℝ
  left_bound : 0 ≤ left
  right_bound : right ≤ 1
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

lemma exists_left_sup (s : Set ClosedInterval) (hs : s.Nonempty) : ∃ x : ℝ, IsLUB (ClosedInterval.left '' s) x ∧ 0 ≤ x ∧ x ≤ 1 := by

  have h₁ :  1 ∈ upperBounds (ClosedInterval.left '' s) := by
    simp [upperBounds]
    intro i _
    trans i.right
    exact i.ordered
    exact i.right_bound

  have h₂ : BddAbove (ClosedInterval.left '' s) := by
    simp [BddAbove]
    use 1

  have h₃ : ∃ x : ℝ, IsLUB (ClosedInterval.left '' s) x := Real.exists_isLUB (Set.Nonempty.image ClosedInterval.left hs) h₂

  obtain ⟨x, hx⟩ := h₃
  use x
  constructor
  · exact hx
  · by_contra h
    simp at h
    by_cases h' : x < 0
    · obtain ⟨i, hi⟩ := hs
      have h₃ : i.left ≤ x := by
        simp [IsLUB, IsLeast, upperBounds] at hx
        obtain ⟨hx, _⟩ := hx
        exact hx i hi
      linarith [i.left_bound]
    · simp at h'
      simp [IsLUB, IsLeast, lowerBounds] at hx
      obtain ⟨_, hx⟩ := hx
      linarith [hx h₁, h h']

lemma exists_right_inf (s : Set ClosedInterval) (hs : s.Nonempty) : ∃ x : ℝ, IsGLB (ClosedInterval.right '' s) x ∧ 0 ≤ x ∧ x ≤ 1 := by

  have h₁ : 0 ∈ lowerBounds (ClosedInterval.right '' s) := by
    simp [lowerBounds]
    intro i _
    trans i.left
    exact i.left_bound
    exact i.ordered

  have h₂ : BddBelow (ClosedInterval.right '' s) := by
    simp [BddBelow]
    use 0

  have h₃ : ∃ x : ℝ, IsGLB (ClosedInterval.right '' s) x := Real.exists_isGLB (Set.Nonempty.image ClosedInterval.right hs) h₂

  obtain ⟨x, hx⟩ := h₃
  use x
  constructor
  · exact hx
  · by_contra h
    simp at h
    by_cases h' : x < 0
    · simp [IsGLB, IsGreatest, upperBounds] at hx
      obtain ⟨_, hx⟩ := hx
      linarith [hx h₁]
    · simp at h'
      obtain ⟨i, hi⟩ := hs
      have h₃ : x ≤ i.right := by
        simp [IsGLB, IsGreatest, lowerBounds] at hx
        obtain ⟨hx, _⟩ := hx
        exact hx i hi
      linarith [i.right_bound, h h']

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
  bot := ⟨0, 1, (by linarith), (by linarith), (by linarith)⟩
  bot_le := by
    intro i
    constructor
    · exact i.left_bound
    · exact i.right_bound
  sSup := by
    intro s
    by_cases h : s.Nonempty
    · exact {
      left := by
        exact (exists_left_sup s h).choose
      right := by
        let x := (exists_left_sup s h).choose
        let x' := (exists_right_inf s h).choose
        by_cases x ≤ x'
        · exact x'
        · exact 1
      left_bound := (exists_left_sup s h).choose_spec.right.left
      right_bound := by
        let x := (exists_left_sup s h).choose
        let x' := (exists_right_inf s h).choose
        by_cases h' : x ≤ x' <;>
          simp [h']
        exact (exists_right_inf s h).choose_spec.right.right
      ordered := by
        let x := (exists_left_sup s h).choose
        let x' := (exists_right_inf s h).choose
        by_cases h' : x ≤ x' <;>
          simp [h']
        exact (exists_left_sup s h).choose_spec.right.right
    }
    · exact ⟨0, 1, (by linarith), (by linarith), (by linarith)⟩

  lubOfDirected := by
    intro s hdir
    by_cases hs : s.Nonempty
    · let x := (exists_left_sup s hs).choose
      let x' := (exists_right_inf s hs).choose
      let hx := (exists_left_sup s hs).choose_spec.left
      let hx' := (exists_right_inf s hs).choose_spec.left
      by_cases h : x ≤ x'
      · simp [sSup, h, hs]
        apply lub_ClosedInterval
        all_goals simp
        exact (exists_left_sup s hs).choose_spec.left
        exact (exists_right_inf s hs).choose_spec.left
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

        have h₃ : i₂.right < i₁.left := by
          linarith

        obtain ⟨i, _, h₅, h₆⟩ := hdir i₁ hi₁₁ i₂ hi₂₁
        obtain ⟨h₇, h₈⟩ := h₅
        obtain ⟨h₉, h₁₀⟩ := h₆
        linarith [i.ordered, h₃, h₇, h₈, h₉, h₁₀]
    · have hs' : s = ∅ := by
        exact Set.not_nonempty_iff_eq_empty.mp hs
      simp [hs, IsLUB, IsLeast, upperBounds, lowerBounds, hs']
      intro i
      constructor
      · exact i.left_bound
      · exact i.right_bound

end Example2
