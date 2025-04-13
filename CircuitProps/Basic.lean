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
-- <-   s    -><-  g   ->
-- |----------|         |
-- 0          s         s+g
-- If a gate's inputs are stable during [0,s],
-- then it promises to have an output value
-- at time s+g
def Xprop := (s : ℝ) → (g: ℝ) → Tprop

def Location := Signal → Tprop

variable (x y z : Location) (t t1 t2 : ℝ)

class Indexed (X : Type) where
  And : X → X → X
  Impl : X → X → X
  Delay : ℝ → X → X
  Const : Prop → X
  Forall : (ℝ → X) → X

instance : Indexed Tprop where
  And := λ A B => λ t => A t ∧ B t
  Impl := λ A B => λ t => A t → B t
  Delay := λ u A => λ t => A (t + u)
  Const x := λ _ => x
  Forall k := λ t => ∀ u, k u t

section use_indexed
open Indexed

-- This notation doesn't have much to do with linear logic,
-- I just wanted something to not conflict with ∧, →  
infixr:35 " ⊗ " => And
infixr:35 " ⊸ " => Impl

notation "○" => Delay
notation "∀" u "," body => Forall (λ u => body)

instance : Coe Tprop Xprop where
  coe x := λ _ _ => x

def interval (lim: ℝ) {A : Type} [Indexed A] (X : A): A := 
   ∀ u, (Const (u ≤ lim ∧ u ≥ 0)) ⊸ ○ u X 

notation "□" => interval

instance : Indexed Xprop where
  And := λ A B => λ s g => A s g ⊗ B s g
  Impl := λ A B => λ s g => □ s (A s g) ⊸ ○ (s + g) (B s g)
  Delay := λ u A => λ s g => ○ u (A s g)
  Const x := λ _ _ => Const x
  Forall k := λ s g => Forall (λ u => k u s g)


def nand_ts : Xprop := 
   (x low ⊸ z high) ⊗
   (y low ⊸ z high) ⊗ 
   ((x high ⊗ y high) ⊸ z low)

end use_indexed
