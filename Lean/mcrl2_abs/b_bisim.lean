import .semi_b_bisim
import ..quotient


variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]


def some_branch_b (R : option (mcrl2 α) → option (mcrl2 α) → Prop) : Prop :=
∀x : mcrl2 α, ∀ y x' a, R x y → transition x a x'  → 
((a = tau ∧ R x' y) ∨
 (∃y' : mcrl2 α, ∃z, has_tau_sequence y y' ∧ transition y' a z ∧ R x y' ∧ R x' z))

def is_branching_bisimulation (R : option (mcrl2 α) → option (mcrl2 α) → Prop) : Prop := 
none_branch R ∧ some_branch_b R ∧ symmetric R

def b_bisim (α : Type) [comm_semigroup_with_zero_and_tau α] : option (mcrl2 α) → option (mcrl2 α) → Prop
| x y := ∃R : option (mcrl2 α) → option (mcrl2 α) → Prop, (R x y) ∧ is_branching_bisimulation R

lemma stutt_bb (R : option (mcrl2 α) → option (mcrl2 α) → Prop) (h : is_semi_branching R)
(h' : stuttering R) : is_branching_bisimulation R :=
begin
  rcases h with ⟨R_none, R_some, R_symm⟩,
  apply and.intro R_none,
  apply and.intro,
  { intros x y x' a hR ha,
    have h, by exact R_some x y x' a hR ha,
    rcases h with ⟨y', z, hy₁, hy₂, hR₁, hR₂⟩,
    rcases hy₂ with ⟨y', rfl, h⟩ | ⟨rfl, rfl⟩,
    { apply or.inr,
      use y',
      use z,
      apply and.intro hy₁,
      apply and.intro h,
      apply and.intro hR₁,
      exact hR₂},
    { induction' hy₁,
      { apply or.inl,
        apply and.intro rfl,
        exact hR₂},
      { apply or.inr,
        use y_1,
        use z,
        apply and.intro hy₁,
        apply and.intro h,
        apply and.intro,
        { specialize h' y x z (R_symm hR) (R_symm hR₁),
          apply R_symm,
          apply h',
          exact hy₁,
          exact h},
        exact hR₂}}},
  exact R_symm  
end

lemma branch_is_semib (R : option (mcrl2 α) → option (mcrl2 α) → Prop) (h : is_branching_bisimulation R) : is_semi_branching R :=
begin
  rcases h with ⟨R_none, R_some, R_symm⟩,
  apply and.intro R_none,
  apply and.intro,
  { intros x y x' a hR ha,
    specialize R_some x y x' a hR ha,
    rcases R_some with ⟨rfl, h⟩ | ⟨y', z, hy₁, hy₂, hR₁, hR₂⟩,
    { use y,
      use y,
      apply and.intro has_tau_sequence.refl,
      apply and.intro,
      { apply or.inr,
        apply and.intro,
        repeat {refl}},
      apply and.intro,
      assumption,
      assumption},
    { use y',
      use z,
      exact ⟨hy₁, by exact or.inl ⟨y', rfl, hy₂⟩, hR₁, hR₂⟩}},
  exact R_symm
end

lemma sb_iff_b {x y} : sb_bisim α x y ↔ b_bisim α x y := 
begin
  split,
  { intro h,
    use (largest_sb x y h),
    apply and.intro sorry,
    apply stutt_bb,
    sorry,
    exact largest_is_stuttering h},
  { intro h,
    rcases h with ⟨R, hR, R_bisim⟩,
    use R,
    apply and.intro hR,
    apply branch_is_semib R R_bisim}
end

lemma b_reflexive : reflexive (b_bisim α) :=
begin
  intro x,
  apply iff.elim_left sb_iff_b,
  exact sb_reflexive x
end

lemma b_symmetric : symmetric (b_bisim α) :=
begin
  intros x y h,
  simp [←sb_iff_b] at *,
  exact sb_symmetric h
end

lemma b_transitive : transitive (b_bisim α) :=
begin
  intros x y z h₁ h₂,
  simp [←sb_iff_b] at *,
  exact sb_transitive h₁ h₂
end