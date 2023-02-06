import tactic
import data.option.basic
import .comm
import .par
import .parl
import .par_axioms

variables {α : Type}
variables [comm_semigroup_with_zero α]

namespace mcrl2

/- Defining the class of mcrl2 with parallelism.-/
class mcrl2_mrg (α : Type) (M : Type 1) [comm_semigroup_with_zero α] extends mcrl2_base α M :=
  (parl : M → M → M)
  (par : M → M → M)
  (comm : M → M → M)
  (deadlock : M)
  (dead_alt : ∀x, alt x deadlock = x)
  (dead_seq : ∀x, seq deadlock x = deadlock)
  (par_def : ∀x y, par x y = alt (alt (parl x y) (parl y x)) (comm x y) )
  (parl_seq_atom : ∀x a, parl (atom a) x = seq (atom a) x)
  (parl_seq : ∀x y a, parl (seq (atom a) x) y = seq (atom a) (par x y))
  (parl_alt : ∀x y z, parl (alt x y) z = alt (parl x z) (parl y z))
  (comm_success : ∀a b c, a * b = c → comm (atom a) (atom b) = (atom c))
  (comm_fail : ∀a b , a * b = 0 → comm (atom a) (atom b) = deadlock)
  (comm_seq_distl : ∀x a b, 
   comm (seq (atom a) x) (atom b) = seq (comm (atom a) (atom b)) x)
  (comm_seq_distr : ∀x a b,
   comm (atom a) (seq (atom b) x) = seq (comm (atom a) (atom b)) x)
  (comm_seq_dist : ∀x y a b,
   comm (seq (atom a) x) (seq (atom b) y) = seq (comm (atom a) (atom b))
  (par x y))
  (comm_alt_distl : ∀x y z, comm (alt x y) z = alt (comm x z) (comm y z))
  (comm_alt_distr : ∀x y z, comm x (alt y z) = alt (comm x y) (comm x z))
  (dead_parl : ∀x, parl deadlock x = deadlock)
  (dead_comml : ∀x, comm deadlock x = deadlock)
  (dead_commr : ∀x, comm x deadlock = deadlock)

/- The instance of mcrl2' with parallelism. Similarly to mcrl2_base, quotient lifting and induction make the proofs simple with the klemmas we already have. -/
instance mcrl2'.mrg : mcrl2_mrg α (mcrl2' α) := {
  deadlock := ⟦mcrl2.deadlock⟧,
  comm := quotient.lift₂ (λa b : mcrl2 α, ⟦a ∣ b⟧) 
         begin
          intros a₁ a₂ b₁ b₂ h₁ h₂,
          simp,
          exact bisim.comm h₁ h₂
         end,
  parl := quotient.lift₂ (λa b : mcrl2 α, ⟦a |_ b⟧) 
         begin
          intros a₁ a₂ b₁ b₂ h₁ h₂,
          simp,
          exact bisim.parl h₁ h₂
         end,
  par := quotient.lift₂ (λa b : mcrl2 α, ⟦a || b⟧) 
         begin
          intros a₁ a₂ b₁ b₂ h₁ h₂,
          simp,
          exact bisim.par h₁ h₂
         end,
  dead_alt := begin
    intros x,
    apply quotient.induction_on x ,
    intros x,
    apply quot.sound,
    exact mcrl2.dead_alt
  end,
  dead_seq := begin
    intros x,
    apply quotient.induction_on x ,
    intros x,
    apply quot.sound,
    exact mcrl2.dead_seq
  end,
  par_def := begin
    intros x y,
    apply quot.induction_on₂ x y,
    intros a b,
    apply quotient.sound,
    exact mcrl2.par_def
  end,
  parl_seq_atom := begin
    intros x a,
    apply quot.induction_on x,
    intros y,
    apply quotient.sound,
    exact mcrl2.parl_seq_atom
  end,
  parl_seq := begin
    intros x y a,
    apply quot.induction_on₂ x y,
    intros v w,
    apply quotient.sound,
    exact mcrl2.parl_seq
  end,
  parl_alt := begin
    intros x y z,
    apply quot.induction_on₃ x y z,
    intros u v w,
    apply quotient.sound,
    exact mcrl2.parl_alt
  end,
  comm_success := begin
    intros a b c h, 
    apply quotient.sound,
    exact mcrl2.comm_success h
  end,
  comm_fail := begin
    intros a b h, 
    apply quotient.sound,
    exact mcrl2.comm_fail h
  end,
  comm_seq_distl := begin
    intros x a b,
    apply quot.induction_on x,
    intro x',
    apply quotient.sound,
    exact mcrl2.comm_seq_distl
  end,
  comm_seq_distr := begin
    intros x a b,
    apply quot.induction_on x,
    intro x',
    apply quotient.sound,
    exact mcrl2.comm_seq_distr
  end,
  comm_seq_dist := begin
    intros x y a b,
    apply quot.induction_on₂ x y,
    intros x' y',
    apply quotient.sound,
    exact mcrl2.comm_seq_dist
  end,
  comm_alt_distl := begin
    intros x y z,
    apply quotient.induction_on₃ x y z,
    intros x' y' z',
    apply quot.sound,
    exact mcrl2.comm_alt_distl
  end,
  comm_alt_distr := begin
    intros x y z,
    apply quotient.induction_on₃ x y z,
    intros x' y' z',
    apply quot.sound,
    exact mcrl2.comm_alt_distr
  end,
  dead_parl := begin
    intros x,
    apply quotient.induction_on x,
    intros x,
    apply quot.sound,
    exact mcrl2.dead_parl
  end,
  dead_comml := begin
    intros x,
    apply quotient.induction_on x,
    intros x,
    apply quot.sound,
    exact mcrl2.dead_comml
  end,
  dead_commr := begin
    intros x,
    apply quotient.induction_on x,
    intros x,
    apply quot.sound,
    exact mcrl2.dead_commr
  end,
  ..mcrl2'.base}


end mcrl2

