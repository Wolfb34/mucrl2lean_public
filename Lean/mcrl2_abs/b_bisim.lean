import .tau_seq

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]

def none_branch (R : option (mcrl2 α) → option (mcrl2 α) → Prop) : Prop :=
∀y : option (mcrl2 α), R none y → (has_tau_sequence y none ∧ R none none)

def some_branch (R : option (mcrl2 α) → option (mcrl2 α) → Prop) : Prop :=
∀x : mcrl2 α, ∀ y x' a, R x y → transition x a x'  → 
((a = tau ∧ R x' y) ∨
 (∃z : mcrl2 α, ∃y', has_tau_sequence y z ∧ R x z ∧ transition z a y' ∧ R x' y'))

def is_branching_bisimulation (R : option (mcrl2 α) → option (mcrl2 α) → Prop) : Prop := 
none_branch R ∧ some_branch R ∧ symmetric R

def b_bisim (α : Type) [comm_semigroup_with_zero_and_tau α] : option (mcrl2 α) → option (mcrl2 α) → Prop
| x y := ∃R : option (mcrl2 α) → option (mcrl2 α) → Prop, (R x y) ∧ is_branching_bisimulation R

lemma bisim_tau_none (R : option (mcrl2 α) → option (mcrl2 α) → Prop)  (x y) 
(R_bisim : is_branching_bisimulation R) (h : R x y) (h' : has_tau_sequence x none) : has_tau_sequence y none ∧ R none none :=
begin
  rcases R_bisim with ⟨R_none, R_some, R_symm⟩,
  apply and.intro,
  { induction' h',
    { specialize R_none y h,
      exact R_none.left},
    { have h : _, by exact R_some x y y_1 tau h h_1,
      cases h,
      { cases h_2 with _ Ryy,
        exact ih R y R_none R_some R_symm Ryy},
      { rcases h_2 with ⟨w, w', hyw, hRxw, hww', hy1w⟩,
        apply doub_tau hyw,
        apply has_tau_sequence.trans hww',
        apply ih R w' R_none R_some R_symm,
        exact hy1w}}},
  { induction' h',
    { have h', by exact R_none y h,
      exact h'.right},
    { have h_x, by exact R_some x y y_1 tau h h_1,
      cases h_x,
      { specialize ih R y R_none R_some R_symm,
        apply ih,
        exact h_x.right},
      { rcases h_x with ⟨_, _, _, _, _, hRy_1⟩,
        specialize ih R h_x_h_w R_none R_some R_symm hRy_1,
        assumption}}}
end

lemma bisim_tau_some {R : option (mcrl2 α) → option (mcrl2 α) → Prop}  (x y x')
(R_bisim : is_branching_bisimulation R) (h : R x y) (h' : has_tau_sequence x x') : ∃y', has_tau_sequence y y' ∧ R x'  y' :=
begin
  rcases R_bisim with ⟨R_none, R_some, R_symm⟩,
  induction' h',
  { exact ⟨y, has_tau_sequence.refl, h⟩},
  { have R_pass, by exact R_some x y y_1 tau h h_1,
    rcases R_pass with ⟨_, _⟩ | ⟨y', w, hty, hRx, hty', hRy_1⟩,
    { apply ih,
      repeat {assumption},},
    { specialize ih w R_none R_some R_symm hRy_1,
      rcases ih with ⟨w', htw, hRw⟩,
      use w',
      apply and.intro,
      { apply doub_tau hty,
        apply has_tau_sequence.trans hty',
        assumption},
      { assumption}}}
end

lemma b_bisim_reflexive : reflexive (b_bisim α) :=
begin
  intro x,
  use (λa b, a = b),
  repeat {apply and.intro},
  refl,
  { intros y h,
    rw ←h,
    exact ⟨has_tau_sequence.refl, by simp⟩},
  { intros x y x' a hRx hx,
    apply or.inr,
    use x,
    use x',
    rw hRx,
    exact ⟨has_tau_sequence.refl, by simp, hx, by simp⟩},
  { intros u w h; rw h; refl}
end

lemma b_bisim_symmetric : symmetric (b_bisim α) :=
begin
  intros x y h,
  rcases h with ⟨R, hRx, R_none, R_some, R_symm⟩,
  use R,
  apply and.intro,
  { exact (R_symm hRx)},
  { exact ⟨R_none, R_some, R_symm⟩}
end

lemma R_comp_none (R R' : option (mcrl2 α) → option (mcrl2 α) → Prop) 
(h : is_branching_bisimulation R) (h' : is_branching_bisimulation R') : 
none_branch (R_comp R R') :=
begin
  rcases h with  ⟨R_none, R_some, R_symm⟩,
  rcases h' with ⟨R'_none, R'_some, R'_symm⟩,
  intros y h,
  cases h,
  { rcases h_h with ⟨w, hRw, hR'w⟩,
    have h, by exact bisim_tau_none R none w ⟨R_none, R_some, R_symm⟩ hRw has_tau_sequence.refl,
    cases h with htw hRn,
    have h', by exact bisim_tau_none R' w y ⟨R'_none, R'_some, R'_symm⟩ hR'w htw,
    apply and.intro h'.left,
    apply R_comp.stepl,
    exact ⟨none, hRn, h'.right⟩},
  { rcases h_h with ⟨w, hRw, hR'w⟩,
    have hR'w', by exact R'_symm hR'w,
    have hRw', by exact R_symm hRw,
    have h, by exact bisim_tau_none R' none w ⟨R'_none, R'_some, R'_symm⟩ hR'w' has_tau_sequence.refl,
    cases h with htw hRn,
    have h', by exact bisim_tau_none R w y ⟨R_none, R_some, R_symm⟩ hRw' htw,
    apply and.intro h'.left,
    apply R_comp.stepl,
    exact ⟨none, h'.right, hRn⟩}
end

lemma R_comp_some (R R' : option (mcrl2 α) → option (mcrl2 α) → Prop) 
(h : is_branching_bisimulation R) (h' : is_branching_bisimulation R') : 
some_branch (R_comp R R') :=
begin
  rcases h with  ⟨R_none, R_some, R_symm⟩,
  rcases h' with ⟨R'_none, R'_some, R'_symm⟩,
  intros x y x' a h hax,
  cases h,
  { rcases h_h with ⟨w, hRw, hR'w⟩,
    have h, by exact R_some x w x' a hRw hax,
    cases h,
    { apply or.inl,
      apply and.intro h.left,
      apply R_comp.stepl,
      exact ⟨w, h.right, hR'w⟩},
    { rcases h with ⟨w', z, hw, hRw', hw'a, hRx'⟩,
      induction' hw,
      { have h, by exact R'_some w' y z a hR'w hw'a,
        cases h,
        { apply or.inl,
          apply and.intro h.left,
          apply R_comp.stepl,
          exact ⟨z, hRx', h.right⟩},
        { apply or.inr,
          rcases h with ⟨_, _, _, _, _, _⟩,
          use h_w,
          use h_h_w,
          apply and.intro h_h_h_left,
          apply and.intro,
          { apply R_comp.stepl,
            use w',
            apply and.intro,
            repeat {assumption}},
          apply and.intro h_h_h_right_right_left,
          apply R_comp.stepl,
          exact ⟨z, hRx', h_h_h_right_right_right⟩}},
      { specialize ih R R' R_none R_some R_symm R'_none R'_some R'_symm,
        have h', by exact R'_some x_1 y y_1 tau hR'w h,
        rcases h' with ⟨_, hR'⟩ | h',
        { }}}}
end

lemma b_bisim_transitive : transitive (b_bisim α) :=
begin
  rintros x y z ⟨R, Rxy, R_none, R_some, R_symm⟩ ⟨R', R'yz, R'_none, R'_some, R'_symm⟩,
  use R_comp R R',
  repeat {apply and.intro},
  { apply R_comp.stepl,
    use y, exact ⟨Rxy, R'yz⟩},
  { exact R_comp_none R R' ⟨R_none, R_some, R_symm⟩ ⟨R'_none, R'_some, R'_symm⟩},
  { exact R_comp_some R R' ⟨R_none, R_some, R_symm⟩ ⟨R'_none, R'_some, R'_symm⟩},
  { exact comp_symmetric}
end
