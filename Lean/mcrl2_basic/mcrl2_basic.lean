import .basic_axioms
import .congruence


variables {α : Type}
variables [comm_semigroup_with_zero_and_tau α]

namespace mcrl2


/- This is the base class of mrl2, with atoms, alternative and sequential composition and their axioms.-/
class mcrl2_base (α : Type) (M : Type 1) [comm_semigroup_with_zero_and_tau α] :=
  (atom : α → M)
  (alt : M → M → M)
  (seq : M → M → M)
  (alt_comm : ∀x y, alt x y = alt y x)
  (alt_assoc : ∀x y z, alt x (alt y z) = alt (alt x y) z)
  (alt_idem : ∀x, alt x x = x)
  (alt_dist : ∀x y z, seq (alt x y) z = alt (seq x z) (seq y z))
  (seq_assoc : ∀x y z, seq (seq x y) z = seq x (seq y z))



/- This is the instance of mcrl2_base for mcrl2'. Quotient lifting and quotient induction make most of the proofs straightforward with the lemmas we have.-/
instance mcrl2'.base : mcrl2_base α (mcrl2' α) := {
  atom := λa, ⟦mcrl2.atom a⟧,
  alt := quotient.lift₂ (λa b : mcrl2 α, ⟦a + b⟧)
         begin
          intros a₁ a₂ b₁ b₂ h₁ h₂,
          simp,
          exact bisim.alt _ _ _ _ h₁ h₂
         end,
  seq := quotient.lift₂ (λa b, ⟦a ⬝ b⟧)
         begin
          intros a b a' b' ha hb,
          simp,
          exact bisim.seq ha hb
         end,
  alt_assoc := begin
    intros x y z,
    apply quot.induction_on₃ x y z,
    intros a b c,
    apply quotient.sound,
    exact mcrl2.alt_assoc
  end,
  alt_idem := begin
    intro x,
    apply quot.induction_on x,
    intro a,
    apply quotient.sound,
    exact mcrl2.alt_idem
  end,
  alt_dist := begin
    intros x y z,
    apply quot.induction_on₃ x y z,
    intros a b c,
    apply quotient.sound,
    exact mcrl2.alt_dist
  end,
  seq_assoc := begin
    intros x y z,
    apply quot.induction_on₃ x y z,
    intros a b c,
    apply quotient.sound,
    exact mcrl2.seq_assoc
  end,
    alt_comm := begin
    intros x y,
    apply quot.induction_on₂ x y,
    intros a b,
    apply quotient.sound,
    exact mcrl2.alt_comm
  end
}

end mcrl2
