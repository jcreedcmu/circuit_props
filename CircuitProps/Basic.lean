import Mathlib
open NNReal

inductive Signal where
 | high
 | low
open Signal

def neg : Signal → Signal
| high => low
| low => high

-- A Tprop is a proposition indexed by time
def Tprop := (t : ℝ) → Prop

-- A location is a thing that may have a high signal and may have a
-- low signal at various times.
def Location := Signal → Tprop

def Univ (A : Tprop) : Prop :=
  ∀ t, A t
prefix:30 "⊧" => Univ

def Prev (p : ℝ) (A : Tprop) : Tprop :=
  fun t => ∀ u ∈ Set.Icc 0 p, A (t - u)
notation "□[" p "]" q:60 => Prev p q

def Delay (p : ℝ) (A : Tprop) : Tprop :=
  fun t => A (t - p)
notation "○[" p "]" q:60 => Delay p q

def Andt (A B : Tprop) : Tprop := fun t => A t ∧ B t
def Impt (A B : Tprop) : Tprop := fun t => A t → B t

infixr:35 " ∧t " => Andt
infixr:30 " →t " => Impt

structure Nand (p q : ℝ) (in0 in1 out : Location) where
  low0 : ⊧ (□[p] ○[q] (in0 low) →t out high)
  low1 : ⊧ (□[p] ○[q] (in1 low) →t out high)
  high01 : ⊧ (□[p] ○[q] (in0 high ∧t in1 high) →t out low)

example (p q : ℝ) (in0 in1 out : Location) :
    (□[p] ○[q] (in0 high ∧t in1 high) →t out low) =
   ((□[p] (○[q] (in0 high ∧t in1 high))) →t out low) := by
   rfl

structure Latch (p q : ℝ) (s r qpos qbar : Location) : Prop where
 nand_qpos : Nand p q s qbar qpos
 nand_qbar : Nand p q r qpos qbar

@[simp]
theorem prev_zero {A : Tprop} : (□[0] A) = A := by
  funext t
  apply propext
  constructor
  · intro h
    specialize h 0 (by simp only [Set.Icc_self, Set.mem_singleton_iff])
    simp only [sub_zero] at h
    exact h
  · intro h u hu
    simp_all only [Set.Icc_self, Set.mem_singleton_iff, sub_zero]

@[simp]
theorem delay_zero {A : Tprop} : (○[0] A) = A := by
  funext t
  apply propext
  constructor
  all_goals simp only [Delay, sub_zero, imp_self]

theorem prev_func (p : ℝ) {A B : Tprop} : (⊧ (A →t B)) → (⊧ (□[p] A →t □[p]B)) :=
  fun h t a u hu => h (t - u) (a u hu)

theorem delay_func (p : ℝ) {A B : Tprop} : ⊧ (A →t B) → ⊧ (○[p] A →t ○[p]B) :=
  fun h t a => h (t - p) a

theorem prev_concat (p q : ℝ≥0) (A : Tprop) : (□[p + q] A) = (□[p] □[q] A) := by
  funext t
  apply propext
  constructor
  · intro h u hu v hv
    specialize h (u + v) (by grind)
    ring_nf at h ⊢
    exact h
  · intro h u hu
    cases lt_or_ge u q with
    | inl h' =>
      specialize h 0 (by simp only [Set.mem_Icc, le_refl, zero_le_coe, and_self]) u (by grind)
      ring_nf at h
      exact h
    | inr h' =>
      specialize h (u - q) (by grind) q (by simp only [Set.mem_Icc, zero_le_coe, le_refl, and_self])
      ring_nf at h
      exact h

theorem delay_concat (p q : ℝ≥0) (A : Tprop) : (○[p + q] A) = (○[p] ○[q] A) := by
  funext t
  apply propext
  constructor
  all_goals
  · intro h
    simp_all only [Delay]
    ring_nf at h ⊢
    exact h

theorem prev_and_dist (p : ℝ) (A B : Tprop) : (□[p] (A ∧t B)) = ((□[p] A) ∧t (□[p] B)) := by
  funext t
  apply propext
  constructor
  · intro h
    constructor
    · intro u hu
      specialize h u hu
      exact h.1
    · intro u hu
      specialize h u hu
      exact h.2
  · intro h u hu
    constructor
    · exact h.1 u hu
    · exact h.2 u hu

theorem delay_and_dist (p : ℝ) (A B : Tprop) : (○[p] (A ∧t B)) = ((○[p] A) ∧t (○[p] B)) := by
  funext t
  apply propext
  exact ⟨id, id⟩

lemma and4_assoc (A B C D : Tprop) : ((A ∧t B) ∧t C ∧t D) = (A ∧t B ∧t C ∧t D) := by
  funext t
  apply propext
  constructor
  · intro ⟨⟨a, b⟩, c, d⟩
    exact ⟨a, b, c, d⟩
  · intro ⟨a, b, c, d⟩
    exact ⟨⟨a, b⟩, c, d⟩

lemma delay_prev_comm (p q : ℝ) (A : Tprop) : (○[p] □[q] A) = (□[q] ○[p] A) := by
  funext t
  apply propext
  constructor; all_goals
    intro h u hu
    specialize h u hu
    simp_all only [Delay]
    ring_nf at h ⊢
    exact h

lemma shrink_interval_right (p : ℝ) (q : ℝ≥0) (r : ℝ) (A : Tprop) :
    ⊧ (□[p + q] ○[r] A) →t (□[p] ○[q + r] A) := by
  intro t h u hu
  specialize h (u + q) (by grind [zero_le_coe])
  simp_all only [Delay]
  ring_nf at h ⊢
  exact h

lemma shrink_interval_right' (p : ℝ) (q : ℝ≥0) (A : Tprop) :
    ⊧ (□[p + q] A) →t (□[p] ○[q] A) := by
  intro t h u hu
  specialize h (u + q) (by grind [zero_le_coe])
  simp_all only [Delay]
  ring_nf at h ⊢
  exact h

lemma shrink_interval_left (p : ℝ) (q : ℝ≥0) (A : Tprop) :
    ⊧ (□[p + q] A →t (□[p] A)) := by
  intro t h u hu
  specialize h u (by grind [zero_le_coe])
  exact h

/--
Knowing that `A` was true for the past `p+q` time
is the same thing as knowing that `A` was true
for a segment of time of length `q`, and also
for a segment of length `p` shifted `q` into the past.
-/
theorem peel (p q : ℝ≥0) (A : Tprop) :
   □[p+q] A = (□[p] ○[q] A ∧t □[q] A) := by
  funext t
  apply propext
  constructor
  · intro h
    constructor
    · intro u hu
      simp only [Delay]
      specialize h (u + q) (by grind [zero_le_coe])
      ring_nf at h ⊢
      exact h
    · intro u hu
      simp only [Prev] at h
      exact h u (by grind [zero_le_coe])
  · intro ⟨h1, h2⟩ u hu
    cases lt_or_ge u q with
    | inl h => exact h2 u (by grind)
    | inr h =>
      specialize h1 (u - q) (by grind)
      simp only [Delay] at h1
      ring_nf at h1
      exact h1

theorem latch_stable1a (p q : ℝ) (s r qpos qbar : Location)
    (ℓ : Latch p q s r qpos qbar) :
    ⊧ (□[p]○[q] (qpos high ∧t qbar low ∧t s high ∧t r high) →t (qpos high ∧t qbar low)) := by
  intro t h
  constructor
  · apply ℓ.nand_qpos.low1
    refine prev_func (↑p) (delay_func (↑q) ?_) t h
    intro t ⟨_, qbl, _, _⟩
    exact qbl
  · apply ℓ.nand_qbar.high01
    refine prev_func (↑p) (delay_func (↑q) ?_) t h
    intro t ⟨qph,_,_,rh⟩
    exact ⟨rh, qph⟩

theorem latch_stable1b (p q : ℝ) (s r qpos qbar : Location)
    (ℓ : Latch p q s r qpos qbar) :
    ⊧ (□[p]○[q] (qpos low ∧t qbar high ∧t s high ∧t r high) →t (qpos low ∧t qbar high)) := by
  intro t h
  constructor
  · apply ℓ.nand_qpos.high01
    refine prev_func (↑p) (delay_func (↑q) ?_) t h
    intro t ⟨_, qbh, sht, _⟩
    exact ⟨sht, qbh⟩
  · apply ℓ.nand_qbar.low1
    refine prev_func (↑p) (delay_func (↑q) ?_) t h
    intro t ⟨qpl, _, _, _⟩
    exact qpl

theorem latch_stable1 (p q : ℝ≥0) (s r qpos qbar : Location)
    (ℓ : Latch p q s r qpos qbar) (sig : Signal) :
    ⊧ (□[p + q]○[q] (qpos sig ∧t qbar (neg sig))) ∧t (□[p + q]○[q] (s high ∧t r high))
        →t □[q] (qpos sig ∧t qbar (neg sig)) := by
  rw [← prev_and_dist, ← delay_and_dist, add_comm, prev_concat, and4_assoc]
  refine prev_func q ?_
  exact match sig with
  | high => latch_stable1a p q s r qpos qbar ℓ
  | low  => latch_stable1b p q s r qpos qbar ℓ

theorem latch_stable2 (p q : ℝ≥0) (n : ℕ) (s r qpos qbar : Location)
    (ℓ : Latch p q s r qpos qbar) (sig : Signal) :
    ⊧ (□[p + q]○[n * q] (qpos sig ∧t qbar (neg sig))) ∧t
      (□[p + n * q]○[q] (s high ∧t r high)) →t
       □[n * q] (qpos sig ∧t qbar (neg sig)) := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul, delay_zero, add_zero, prev_zero]
    intro t h
    obtain h1 := h.1 0 (by simp only [Set.mem_Icc, le_refl, true_and]; positivity)
    simp only [sub_zero] at h1
    exact h1
  | succ n hn =>
    have nqq_pos : (n : ℝ) * (q : ℝ) = (n * q  : ℝ≥0) := rfl
    have hh : (((n + 1) : ℕ) * (q : ℝ) ) = ((n * q) + q) := by
      push_cast
      ring_nf
    rw [hh]
    conv => arg 1; rhs; rw[nqq_pos, peel]
    let premise :=
      □[p + q]○[n * q + q](qpos sig ∧t qbar (neg sig)) ∧t
      □[p + (n * q + q)]○[q](s high ∧t r high)

    -- Dead code?
    have subgC : ⊧ (premise →t □[p + q + q] ○[n * q] (qpos sig ∧t qbar (neg sig))) := by
      rw [← delay_prev_comm, show (p : ℝ) + q = (p + q : ℝ≥0) from rfl, peel,
          delay_and_dist, delay_prev_comm, nqq_pos, ← delay_concat]
      intro t ⟨p1, p2⟩
      refine ⟨p1, ?_⟩
      have lem := delay_func (n * q) (latch_stable1 p q s r qpos qbar ℓ sig)
      rw [ delay_and_dist, delay_prev_comm,
          nqq_pos, ← delay_concat,
          delay_prev_comm, ← delay_concat,
          ] at lem
      refine lem t ⟨p1, ?_⟩
      have p2' : (□[(↑p + ↑q) + (↑n * ↑q)]○[↑q](s high ∧t r high)) t := by
        ring_nf at p2 ⊢
        exact p2
      exact shrink_interval_right (↑p + ↑q) (n * q) q (s high ∧t r high) t p2'

    have hn1 : ⊧ (premise →t □[p + q] ○[q] ○[n * q] (qpos sig ∧t qbar (neg sig))) := by
      rw [nqq_pos, ← delay_concat, add_comm (q : ℝ)]
      intro t ⟨pr1, _⟩
      exact pr1

    have hn2 : ⊧ (premise →t □[↑p + ↑n * ↑q]○[↑q]○[↑q](s high ∧t r high)) := by
      intro t ⟨_, pr2⟩
      ring_nf at pr2
      exact shrink_interval_right' _ q _ _ pr2

    have subg1 : ⊧ (premise →t □[n * q]○[q](qpos sig ∧t qbar (neg sig))) := by
      intro t pr
      obtain hn' := delay_func q hn
      rw [delay_and_dist] at hn'
      repeat rw [delay_prev_comm] at hn'
      exact hn' t ⟨hn1 t pr, hn2 t pr⟩

    have combine : ⊧ (premise →t □[p + q + n * q]○[q](qpos sig ∧t qbar (neg sig))) := by
      sorry

    have subg2 : ⊧ (premise →t □[q] (qpos sig ∧t qbar (neg sig))) := by
      intro t ⟨pr1, pr2⟩
      refine latch_stable1 p q s r qpos qbar ℓ sig t ⟨?_, ?_⟩
      · apply shrink_interval_left (q := n * q)
        push_cast at combine ⊢
        ring_nf at combine ⊢
        exact combine t ⟨pr1, pr2⟩
      · apply shrink_interval_left (q := n * q)
        push_cast at pr2 ⊢
        ring_nf at pr2 ⊢
        exact pr2

    intro t h
    exact ⟨subg1 t h, subg2 t h⟩
