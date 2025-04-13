import Mathlib 

inductive Signal where
 | high
 | low
open Signal

-- A Tprop is a proposition indexed by time
def Tprop := (t : ℝ) → Prop

-- An Xprop is a proposition indexed by time,
-- and also gate timing characteristics:
-- s is "setup time"
-- g is "gap"
-- <-         s        ->
--             <-  g   ->
-- |----------|         |
-- -s         -g         0
-- If a gate's inputs are stable during [-s,-g],
-- then it promises to have an output value
-- at time 0.
def Xprop := (s : ℝ) → (g: ℝ) → Tprop

def Sgprop := (s : ℝ) → (g: ℝ) → Prop

def Location := Signal → Tprop

variable (x y z : Location) (t t1 t2 : ℝ)

class PreIndexed (X : Type) where
  And : X → X → X
  Impl : X → X → X
  Const : Prop → X
  Forall : (ℝ → X) → X

class Indexed (X : Type) extends PreIndexed X where
  Delay : ℝ → X → X

instance : Indexed Tprop where
  And := λ A B => λ t => A t ∧ B t
  Impl := λ A B => λ t => A t → B t
  Delay := λ u A => λ t => A (t + u)
  Const x := λ _ => x
  Forall k := λ t => ∀ u, k u t

instance : PreIndexed Sgprop where
  And := λ A B => λ s g => A s g ∧ B s g
  Impl := λ A B => λ s g => A s g → B s g
  Const x := λ _ _ => x
  Forall k := λ s g => ∀ u, k u s g

section use_indexed
open Indexed PreIndexed

-- This notation doesn't have much to do with linear logic,
-- I just wanted something to not conflict with ∧, →  
infixr:35 " ⊗ " => And
infixr:30 " ⊸ " => Impl

notation "○" => Delay
notation "∀" u "," body => Forall (λ u => body)

instance : Coe Tprop Xprop where
  coe x := λ _ _ => x

def interval (a b : ℝ) (X : Tprop): Tprop := 
   λ t => ∀ u, ((a + t ≤ u ∧ u ≤ b + t) → X u)

notation "□" => interval

instance : Indexed Xprop where
  And := λ A B => λ s g => A s g ⊗ B s g
  Impl := λ A B => λ s g => (□ (-s) (-g) (A s g)) ⊸ (B s g)
  Delay := λ u A => λ s g => ○ u (A s g)
  Const x := λ _ _ => Const x
  Forall k := λ s g => Forall (λ u => k u s g)

def for_some_timing (A : Xprop) : Prop := 
   ∃ s g, ∀ t, A s g t

notation "◇" => for_some_timing

theorem dia_distrib {A B C D : Tprop} : ◇ (A ⊸ B) ∧ ◇ (C ⊸ D) ↔ ◇ ((A ⊸ B) ⊗ (C ⊸ D)) := 
  have undistribute_dia  : ◇ (A ⊸ B) ∧ ◇ (C ⊸ D) → ◇ ((A ⊸ B) ⊗ (C ⊸ D)) := by
    intro h1 
    let ⟨⟨s, g, w⟩ , ⟨s', g', w'⟩⟩ := h1
    use (max s s')
    use (min g g')
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
    let ⟨ s , g , w ⟩ := h1
    constructor
    · use s; use g; intro t; exact (w t).1
    · use s; use g; intro t; exact (w t).2

  Iff.intro undistribute_dia distribute_dia 

structure Nand : Prop where
   nand1low : ◇ (x low ⊸ z high) 
   nand2low : ◇ (y low ⊸ z high) 
   nandBothHigh : ◇ ((x high ⊗ y high) ⊸ z low)

structure Latch (s r q qbar : Location) : Prop where
 qside : Nand s qbar q 
 qbarside : Nand r q qbar


def latch_set_q {s r q qbar : Location} (L : Latch s r q qbar) : ◇ (s low ⊸ q high) :=
 L.qside.nand1low

def latch_set_qbar {s r q qbar : Location} (L : Latch s r q qbar) : ◇ (r high ⊗ s low ⊸ qbar low) := by
 have y : ◇ ((s low ⊸ q high) ⊗ (r high ⊗ q high ⊸ qbar low)) := by 
  apply dia_distrib.mp
  constructor
  · exact latch_set_q L
  · exact L.qbarside.nandBothHigh
 sorry

def latch_reset_qbar {s r q qbar : Location} (L : Latch s r q qbar) : ◇ (r low ⊸ qbar high) :=
 L.qbarside.nand1low
 
def latch_remain_q {s r q qbar : Location} (L : Latch s r q qbar) : ◇ (q high ⊗ s high ⊗ r high ⊸ q high) := by
 have y : ◇ ((s low ⊸ q high) ⊗ (r high ⊗ q high ⊸ qbar low)) := by 
  apply dia_distrib.mp
  constructor
  · exact latch_set_q L
  · exact L.qbarside.nandBothHigh
 sorry

end use_indexed
