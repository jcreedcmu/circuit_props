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
infixr:35 " ⊸ " => Impl

notation "○" => Delay
notation "∀" u "," body => Forall (λ u => body)

instance : Coe Tprop Xprop where
  coe x := λ _ _ => x

def interval (a b : ℝ) (X : Tprop): Tprop := 
   λ t => ∀ u, (a ≤ u ∧ u ≤ b) → X t

notation "□" => interval

instance : Indexed Xprop where
  And := λ A B => λ s g => A s g ⊗ B s g
  Impl := λ A B => λ s g => □ (-s) (-g) (A s g) ⊸ (B s g)
  Delay := λ u A => λ s g => ○ u (A s g)
  Const x := λ _ _ => Const x
  Forall k := λ s g => Forall (λ u => k u s g)

def for_some_timing (A : Xprop) : Prop := 
   ∃ s g, ∀ t, A s g t

notation "◇" => for_some_timing

def nand_ts : Prop := 
   ◇ (x low ⊸ z high) ∧ 
   ◇ (y low ⊸ z high) ∧ 
   ◇ ((x high ⊗ y high) ⊸ z low)

theorem foo (A B C D : Tprop) : ◇ (A ⊸ B) ∧ ◇ (C ⊸ D) → ◇ ((A ⊸ B) ⊗ (C ⊸ D)) :=  by
  intro h1 
  delta for_some_timing
  obtain ⟨⟨ s , g, w⟩ , ⟨s', g', w'⟩⟩ := h1
  
  sorry

end use_indexed
