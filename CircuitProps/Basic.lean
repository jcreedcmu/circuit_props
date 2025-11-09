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

theorem prev_func (p : ℝ) {A B : Tprop} : ⊧ (A →t B) → ⊧ (□[p] A →t □[p]B) :=
  fun h t a u hu => h (t - u) (a u hu)

theorem delay_func (p : ℝ) {A B : Tprop} : ⊧ (A →t B) → ⊧ (○[p] A →t ○[p]B) :=
  fun h t a => h (t - p) a

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

theorem latch_stable1 (p q : ℝ) (s r qpos qbar : Location)
    (ℓ : Latch p q s r qpos qbar) (sig : Signal) :
    ⊧ (□[p]○[q] (qpos sig ∧t qbar (neg sig) ∧t s high ∧t r high)
        →t (qpos sig ∧t qbar (neg sig))) :=
  match sig with
  | high => latch_stable1a p q s r qpos qbar ℓ
  | low  => latch_stable1b p q s r qpos qbar ℓ
