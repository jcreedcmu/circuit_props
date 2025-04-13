import Mathlib

inductive Signal where
 | high
 | low
open Signal

def Tprop := ℝ → Prop

variable (Place : Type) (x y z : Place) (t t1 t2 : ℝ) (has : Place → Signal → Tprop)

def delay (off: ℝ) (A : Tprop) : Tprop := λ t =>
   A (t + off)

notation "○" => delay

def interval (lim: ℝ) (A : Tprop) : Tprop := λ t =>
   ∀ u, (u ≤ lim ∧ u ≥ 0) → ○ u A t

notation "□" => interval

def with_delay (d1 d2 : ℝ) (A B : Tprop) : Tprop := 
   λ t => □ d1 A t → ○ (d1 + d2) B t

def nand_ts (d1 d2 : ℝ)  := λ t => 
   with_delay d1 d2 (has x low) (has z high) t ∧ 
   with_delay d1 d2 (has y low) (has z high) t ∧ 
   with_delay d1 d2 (λ u => has x high u ∧ has y high u) (has z low) t 


