import .encap
import .encap_axioms

variables {α : Type}
variables [comm_semigroup_with_zero_and_tau α]

namespace mcrl2

/- Defining the class of mcrl2 with encapsulation.-/
class mcrl2_encap (α : Type) (M : Type 1) [comm_semigroup_with_zero_and_tau α] extends mcrl2_mrg α M :=
  (encap : set α → M → M)
  (dead_encap : ∀A, encap A deadlock = deadlock)
  (encap_pass : ∀a A, a ∉ A → encap A (atom a) = atom a)
  (encap_fail : ∀a A, a ∈ A → encap A (atom a) = deadlock)
  (encap_alt : ∀x y A, encap A (alt x y) = alt (encap A x) (encap A y))
  (encap_seq : ∀x y A, encap A (seq x y) = seq (encap A x) (encap A y))

/- The instance of mcrl2' with encapsulation. -/
instance mcrl2'.encap : mcrl2_encap α (mcrl2' α) := {
  encap := (λa, quotient.lift (λx, ⟦encap a x⟧) 
        begin
          intros x y h,
          simp,
          exact bisim.encap h
        end),
  dead_encap := begin
    intros A,
    apply quot.sound,
    exact mcrl2.dead_encap
  end,
  encap_pass := begin
    intros a A h,
    apply quot.sound,
    exact mcrl2.encap_pass h
  end,
  encap_fail := begin
    intros a A h,
    apply quot.sound,
    exact mcrl2.encap_fail h
  end,
  encap_alt := begin
    intros x y A,
    apply quotient.induction_on₂ x y ,
    intros x' y',
    apply quot.sound,
    exact mcrl2.encap_alt
  end,
  encap_seq := begin
    intros x y A,
    apply quotient.induction_on₂ x y,
    intros x' y',
    apply quot.sound,
    exact mcrl2.encap_seq
  end,
  ..mcrl2'.mrg
}

end mcrl2