import Mathlib

theorem good_enough (f : ℝ → ℝ) (c : Continuous f) 
  (onRats : (y : ℚ) → f y ≥ 0) : (x : ℝ) → f x ≥ 0 :=
   by 
    by_contra px; push_neg at px; 
    let ⟨x, hx⟩ := px 
    let openset := {y : ℝ | y < 0}
    have hin : f x ∈ openset := hx
    have hio : IsOpen (f ⁻¹' openset) := c.isOpen_preimage openset (isOpen_gt' 0)
    have qq : ∃ t ∈ ⋃ (a : ℚ), ⋃ b, ⋃ (_ : a < b), {Set.Ioo ↑a ↑b},
                  x ∈ t ∧ t ⊆ f ⁻¹' openset := by
         apply  (TopologicalSpace.IsTopologicalBasis.isOpen_iff Real.isTopologicalBasis_Ioo_rat).mp hio x hx
    simp at qq
    let ⟨U , ⟨⟨a, b, lt, eq⟩ , ⟨xinu, usubinv⟩⟩⟩ := qq
    rw [eq] at xinu  usubinv
    let midpoint := (a + b) / 2
    have midab : midpoint ∈ Set.Ioo a b := {
      left := left_lt_add_div_two.mpr lt
      right := add_div_two_lt_right.mpr lt
    }
    have fmab : (m : ℚ) → m ∈ Set.Ioo a b → f m ∈ openset := by 
        intros m hm
        apply usubinv
        simp
        exact hm
    have fmidlt : f midpoint < 0 := fmab midpoint midab
    have fmidge : ¬ f midpoint < 0 := not_lt_of_ge (onRats midpoint)
    tauto

