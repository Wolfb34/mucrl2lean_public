import tactic
import tactic.induction
import data.option.basic


-- Allow diamond inheritance
set_option old_structure_cmd true

/-- A type `S₀` is a "commutative semigroup with zero” if it is a commutative semigroup, has a zero
element, and `0` is left and right absorbing. -/
@[protect_proj, ancestor semigroup_with_zero comm_semigroup]
class comm_semigroup_with_zero_and_tau (S₀ : Type*) extends semigroup_with_zero S₀, comm_semigroup S₀ :=
(tau : S₀)
(tau_ne_zero : tau ≠ 0)
(tau_mul : ∀a : S₀, tau * a = 0)
(mul_tau : ∀a : S₀, a * tau = 0)
(tau_act : ∀a b: S₀, a * b ≠ tau)


/- The inductive type mcrl2 and all its constructors. Needs to be of Type 1 because of the sum operator. -/
inductive mcrl2  (α : Type) [comm_semigroup_with_zero_and_tau α] : Type 1
| atom : α → mcrl2
| tau : mcrl2
| seq : mcrl2 → mcrl2 → mcrl2
| alt : mcrl2 → mcrl2 → mcrl2
| par : mcrl2 → mcrl2 → mcrl2
| parl : mcrl2 → mcrl2 → mcrl2
| comm : mcrl2 → mcrl2 → mcrl2
| encap : set α → mcrl2 → mcrl2
| sum {β : Type} : set β → (β → mcrl2) → mcrl2
| abstract : set α → mcrl2 → mcrl2
| deadlock : mcrl2

attribute [protected] mcrl2.tau


infix (name:=alt) ` + `:70 := mcrl2.alt
infix (name:=seq) ` ⬝ `:100 := mcrl2.seq
infix (name:=par)` || `:90 := mcrl2.par
infix (name:=parl)` |_ `:90 := mcrl2.parl
infix (name:=comm)` ∣ `:90 := mcrl2.comm

notation `δ` := mcrl2.deadlock

export comm_semigroup_with_zero_and_tau (tau)
