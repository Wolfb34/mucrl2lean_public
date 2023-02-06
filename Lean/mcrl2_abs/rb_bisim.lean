import .b_bisim

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]


def is_rb_bisimulation (R : (mcrl2 α) →  (mcrl2 α) → Prop) : Prop := 
(∀x y : mcrl2 α, R x y → ∀x' a, transition x a x' → ∃y', transition y a y' ∧ b_bisim α x' y') ∧ symmetric R

def rb_bisim (α : Type) [comm_semigroup_with_zero_and_tau α] : (mcrl2 α) → (mcrl2 α) → Prop
| x y := ∃R : (mcrl2 α → mcrl2 α → Prop), R x y ∧ is_rb_bisimulation R

#check eq
lemma rb_bisim_reflexive : reflexive (rb_bisim α) :=
begin
  intro x,
  apply exists.intro (λa b, a = b),
  apply and.intro,
  { simp},
  { apply and.intro,
    intros v w hR v' a hv,
    apply exists.intro v',
    apply and.intro,
    { rw ←hR, assumption},
    { exact (b_bisim_reflexive _)},
    { intros u w h; rw h; refl}}
end

lemma rb_bisim_symmetric : symmetric (rb_bisim α) :=
begin
  intros x y h,
  rcases h with ⟨R, hRx, R_bisim, R_symm⟩,
  use R,
  apply and.intro,
  { exact (R_symm hRx)},
  { exact ⟨R_bisim, R_symm⟩}
end

lemma comp_rb_bisim {R R' : mcrl2 α → mcrl2 α → Prop}
(hr : is_rb_bisimulation R) (hr' : is_rb_bisimulation R') :
is_rb_bisimulation (R_comp R R') :=
begin
  apply and.intro,
  { rintros x y hR x' a hx,
    cases hr with R_bisim R_symm,
    cases hr' with R'_bisim R'_symm,
    cases hR,
    { rcases hR_h with ⟨w, hw, hw'⟩,
      specialize R_bisim x w hw x' a hx,
      rcases R_bisim with ⟨w', hw'a, hx'w'⟩,
      }
    },
  { exact comp_rb_symmetric hr hr'}
end

lemma rb_bisim_transitive : transitive (rb_bisim α) :=
sorry