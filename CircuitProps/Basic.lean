import Mathlib

inductive Signal where
 | high
 | low
open Signal

def Tprop := ℝ → Prop

def Location := Signal → Tprop

variable (x y z : Location) (t t1 t2 : ℝ)

def delay (off: ℝ) (A : Tprop) : Tprop := λ t =>
   A (t + off)

notation "○" => delay

def interval (lim: ℝ) (A : Tprop) : Tprop := λ t =>
   ∀ u, (u ≤ lim ∧ u ≥ 0) → ○ u A t

notation "□" => interval


def lifted_imp (A B : Tprop): Tprop := λ t => A t → B t
def lifted_and (A B : Tprop): Tprop := λ t => A t ∧ B t

infixr:35 " ∧' "   => lifted_and
infixr:30 " →'  "  => lifted_imp

def with_delay (d1 d2 : ℝ) (A B : Tprop) : Tprop := 
    □ d1 A →' ○ (d1 + d2) B 

def nand_ts (d1 d2 : ℝ) : Tprop := 
   with_delay d1 d2 (x low) (z high) ∧'
   with_delay d1 d2 (y low) (z high) ∧' 
   with_delay d1 d2 (x high ∧' y high) (z low) 


