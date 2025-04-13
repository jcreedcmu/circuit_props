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
def Xprop := (t : ℝ) → (s : ℝ) → (g: ℝ) → Prop

def Location := Signal → Tprop

class Andable (X : Type) where
  And : X → X → X

instance : Andable Tprop where
  And := λ A B => λ t => A t ∧ B t

instance : Andable Xprop where
  And := λ A B => λ t s g => A t s g ∧ B t s g

-- This notation doesn't have much to do with linear logic,
-- I just wanted something to not conflict with ∧ 
infixr:35 " ⊗ " => Andable.And


class Implable (X : Type) where
  Impl : X → X → X

instance : Implable Tprop where
  Impl := λ A B => λ t => A t → B t

instance : Implable Xprop where
  Impl := λ A B => λ t s g => A t s g → B t s g

-- This notation doesn't have much to do with linear logic,
-- I just wanted something to not conflict with →  
infixr:35 " ⊸ " => Implable.Impl

class Delayable (X : Type) where
  Delay : ℝ → X → X

instance : Delayable Tprop where
  Delay := λ u A => λ t => A (t + u)

instance : Delayable Xprop where
  Delay := λ u A => λ t s g => A (t + u) s g

notation "○" => Delayable.Delay

variable (x y z : Location) (t t1 t2 : ℝ)


class Constable (X : Type) where
  Const : Prop → X

instance : Constable Tprop where
  Const x := λ _ => x

class Forallable (X : Type) where
  Forall : (ℝ → X) → X

instance : Forallable Tprop where
  Forall k := λ t => ∀ u, k u t


def interval (lim: ℝ) {A : Type} [Delayable A] [Constable A] [Implable A] [Forallable A] (X : A): A := 
   Forallable.Forall (X := A) (λ u => (Constable.Const (u ≤ lim ∧ u ≥ 0)) ⊸  Delayable.Delay (X := A) u X )

notation "□" => interval


def lifted_imp (A B : Tprop): Tprop := λ t => A t → B t


infixr:30 " ⊸ "  => lifted_imp

def with_delay (d1 d2 : ℝ) (A B : Tprop) : Tprop := 
    □ d1 A ⊸ ○ (d1 + d2) B 

notation A " ⇒ " "[" d1 "," d2 "]" B =>  with_delay d1 d2 A B

def nand_ts (d1 d2 : ℝ) : Tprop := 
   (x low ⇒ [d1, d2] z high) ⊗
   (y low ⇒ [d1, d2] z high) ⊗ 
   ((x high ⊗ y high) ⇒ [d1, d2] z low)

