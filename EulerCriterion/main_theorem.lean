import Mathlib

theorem euler_criterion
    (K : Type*) [Field K] [Fintype K]
    (a : K) (ha : a ≠ 0) (hchar : ringChar K ≠ 2) :
    IsSquare a ↔ a ^ ((Fintype.card K - 1) / 2) = 1 := by
  constructor
  · intro h
    rcases h with ⟨b, hb⟩
    simp? at hb

  ·
  -- proof here
  sorry
