import Mathlib
open NNReal

inductive Signal where
 | high
 | low
open Signal

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

theorem latch_stable1 (p q : ℝ≥0) (s r qpos qbar : Location)
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

theorem nand_reset (p q : ℝ) (s r qpos qbar : Location)
    (ℓ : Latch p q s r qpos qbar) :
    ⊧ (□[2 * p + q] ○[q] (r low ∧t s high) →t (qpos low ∧t qbar high)) := by
  intro t h
  have hh : qbar high t := by
    apply ℓ.nand_qbar.low0
    sorry
  constructor
  · apply ℓ.nand_qpos.high01
    sorry
  · exact hh

#exit
section use_indexed

-- This notation doesn't have much to do with linear logic,
-- I just wanted something to not conflict with ∧, →
infixr:35 " ⊗ " => And
infixr:30 " ⊸ " => Impl

notation "○" => Delay
notation "□" => Prev
notation "∀" u "," body => Forall (fun u => body)

instance : Coe Tprop Xprop where
  coe x := fun _ _ => x

def interval (a b : ℝ) (X : Tprop) : Tprop :=
   fun t => ∀ u, ((a + t ≤ u ∧ u ≤ b + t) → X u)

notation "□" => interval

instance : Indexed Xprop where
  And := fun A B => fun s g => A s g ⊗ B s g
  Impl := fun A B => fun s g => (□ (-s) (-g) (A s g)) ⊸ (B s g)
  Delay := fun u A => fun s g => ○ u (A s g)
  Const x := fun _ _ => Const x
  Forall k := fun s g => Forall (fun u => k u s g)

def for_some_timing (A : Xprop) : Prop :=
   ∃ sg : ℝ × ℝ, ∀ t, A sg.1 sg.2 t

notation "◇" => for_some_timing

theorem dia_distrib {A B C D : Tprop} : ◇ (A ⊸ B) ∧ ◇ (C ⊸ D) ↔ ◇ ((A ⊸ B) ⊗ (C ⊸ D)) :=
  have undistribute_dia  : ◇ (A ⊸ B) ∧ ◇ (C ⊸ D) → ◇ ((A ⊸ B) ⊗ (C ⊸ D)) := by
    intro h1
    let ⟨⟨⟨s, g⟩, w⟩ , ⟨⟨s', g'⟩, w'⟩⟩ := h1
    use ⟨max s s', min g g'⟩
    intro t
    constructor
    · intro get_a; apply w;  intro u' ⟨h1, h2⟩;
      apply get_a; constructor;
      · linarith [le_max_left s s']
      · linarith [min_le_left g g']
    · intro get_c; apply w'; intro u' ⟨h1, h2⟩;
      apply get_c; constructor;
      · linarith [le_max_right s s']
      · linarith [min_le_right g g']

  have distribute_dia : ◇ ((A ⊸ B) ⊗ (C ⊸ D)) → ◇ (A ⊸ B) ∧ ◇ (C ⊸ D) :=  by
    intro h1
    let ⟨sg , w⟩ := h1
    constructor
    · use sg; intro t; exact (w t).1
    · use sg; intro t; exact (w t).2

  Iff.intro undistribute_dia distribute_dia

def implies_at_spec (sg : ℝ × ℝ) (A B : Tprop) : Tprop :=
  (□ (-sg.1) (-sg.2) (A)) ⊸ B

notation A " ⊸[" sg "] " B => implies_at_spec sg A B
def U (A : Tprop) : Prop :=
 ∀ t, A t

structure Nand : Prop where
   nand1low : ∃ sg, U (x low ⊸[sg] z high)
   nand2low : ∃ sg, U (y low ⊸[sg] z high)
   nandBothHigh : ∃ sg, U ((x high ⊗ y high) ⊸[sg] z low)

theorem lol_curry (A B C : Tprop) (sg : ℝ × ℝ) : ((A ⊗ B) ⊸[sg] C) t → (A ⊸[sg] B ⊸[sg] C) t := by
    intros h ha hb
    apply h
    intros u hle
    constructor
    · exact ha u hle
    · exact hb u hle

structure Latch (s r q qbar : Location) : Prop where
 qside : Nand s qbar q
 qbarside : Nand r q qbar


def dia_functor {A B : Xprop} (f : (sg : ℝ × ℝ) → (t : ℝ)
    → A sg.1 sg.2 t → B sg.1 sg.2 t) (arg : ◇ A) : ◇ B :=
   let ⟨sg', w⟩ := arg
   ⟨sg', fun t => f sg' t (w t)⟩

def latch_set_q {s r q qbar : Location} (L : Latch s r q qbar) : ◇ (s low ⊸ q high) :=
 L.qside.nand1low

def latch_set_qbar {s r q qbar : Location} (L : Latch s r q qbar) :
    ◇ (r high ⊗ s low ⊸ qbar low) := by
 have y : ◇ ((s low ⊸ q high) ⊗ (r high ⊗ q high ⊸ qbar low)) := by
  apply dia_distrib.mp
  constructor
  · exact latch_set_q L
  · exact L.qbarside.nandBothHigh
 apply dia_functor (arg := y)
 intros h h1 h2 h3
 sorry

def latch_reset_qbar {s r q qbar : Location} (L : Latch s r q qbar) : ◇ (r low ⊸ qbar high) :=
 L.qbarside.nand1low

def latch_remain_q {s r q qbar : Location} (L : Latch s r q qbar) :
    ◇ (q high ⊗ s high ⊗ r high ⊸ q high) := by
 have y : ◇ ((s low ⊸ q high) ⊗ (r high ⊗ q high ⊸ qbar low)) := by
  apply dia_distrib.mp
  constructor
  · exact latch_set_q L
  · exact L.qbarside.nandBothHigh
 sorry

end use_indexed
