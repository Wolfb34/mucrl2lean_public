import ..transition.transition

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]

inductive has_tau_sequence : option (mcrl2 α) → option (mcrl2 α) → Prop 
| refl {x} : has_tau_sequence x x
| trans {x y z} (h : transition x tau y) (h' : has_tau_sequence y z) : has_tau_sequence x z

lemma left_tau (x) (y : mcrl2 α) (z) (h : has_tau_sequence x (some y)) (h' : transition y tau z) : has_tau_sequence x z :=
begin
  induction' h,
  { apply has_tau_sequence.trans h',
    exact has_tau_sequence.refl},
  { apply has_tau_sequence.trans h,
    exact ih z h'}
end

lemma doub_tau {x y z : option (mcrl2 α)} (h₁: has_tau_sequence x y) 
(h₂: has_tau_sequence y z) : has_tau_sequence x z :=
begin
  induction' h₁,
  { assumption},
  { apply has_tau_sequence.trans h,
    exact ih h₂}
end