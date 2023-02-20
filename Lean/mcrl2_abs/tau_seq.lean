import ..transition.transition

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]

inductive has_tau_sequence : 
option (mcrl2 α) → option (mcrl2 α) → Prop 
| refl {x} : has_tau_sequence x x
| trans {x y z} (h : transition y tau z) (h' : has_tau_sequence x (some y)) : 
  has_tau_sequence x z


lemma tau_left {x : mcrl2 α} {y z} (h : transition x tau y) (h' : has_tau_sequence y z) : has_tau_sequence (some x) z :=
begin
  induction' h',
  case refl : y { apply has_tau_sequence.trans h,
    exact has_tau_sequence.refl},
  case trans : y w z hw { apply has_tau_sequence.trans hw,
    apply ih,
    assumption}
end

lemma doub_tau {x y z : option (mcrl2 α)} (h₁: has_tau_sequence x y) 
(h₂: has_tau_sequence y z) : has_tau_sequence x z :=
begin
  induction' h₂,
  { assumption},
  { apply has_tau_sequence.trans h,
    exact ih h₁},
end