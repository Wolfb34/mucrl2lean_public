import .tau_seq
import ..quotient
import data.rel
variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]

def semi_transition : option (mcrl2 α) → α → option (mcrl2 α) → Prop 
| x a y := (∃x', x = some x' ∧ transition x' a y) ∨ (a = tau ∧ y = (x))

def none_branch (R : option (mcrl2 α) → option (mcrl2 α) → Prop) : Prop :=
∀y : option (mcrl2 α), R none y → (has_tau_sequence y none ∧ R none none)

def some_branch_sb (R : option (mcrl2 α) → option (mcrl2 α) → Prop) : Prop :=
∀x : mcrl2 α, ∀ y x' a, R x y → transition x a x'  → 
 ∃y' z, has_tau_sequence y y' ∧ semi_transition y' a z ∧ R x y' ∧ R x' z

def is_semi_branching (R : option (mcrl2 α) → option (mcrl2 α) → Prop) : Prop :=
none_branch R ∧ some_branch_sb R ∧ symmetric R

def sb_bisim (α : Type) [comm_semigroup_with_zero_and_tau α] : 
option (mcrl2 α) → option (mcrl2 α) → Prop
| x y := ∃R : option (mcrl2 α) → option (mcrl2 α) → Prop, (R x y) ∧ is_semi_branching R

lemma semi_tau_sequencer {x : option (mcrl2 α)} {y z} (h' : semi_transition y tau z) 
(h : has_tau_sequence x y) : 
has_tau_sequence x z :=
begin
  rcases h' with ⟨y', rfl, h'⟩ | h',
  { exact has_tau_sequence.trans h' h},
  { rw h'.right,
    assumption}
end

lemma semi_tau_sequencel {x : option (mcrl2 α)} {y} {z} (h' : semi_transition x tau y) 
(h : has_tau_sequence y z) : 
has_tau_sequence x z :=
begin
  rcases h' with ⟨x', rfl, h'⟩ | h',
  { exact tau_left h' h},
  { rw ←h'.right,
    assumption}
end

lemma seq_lift {R : option (mcrl2 α) → option (mcrl2 α) → Prop} {x y x'} 
(R_bisim : is_semi_branching R) (h : R x y) (h' : has_tau_sequence x x'):
∃y', has_tau_sequence y y' ∧ R x' y' :=
begin
  induction' h',
  { exact ⟨y, has_tau_sequence.refl, h⟩},
  case trans : x w x' hw { 
    specialize ih R_bisim h,
    rcases ih with ⟨w', hyw, hww⟩,
    have hw, by exact R_bisim.right.left w w' x' tau hww hw,
    rcases hw with ⟨v, u, hv₁, hv₂, hR₁, hR₂⟩,
    use u,
    apply and.intro,
    { apply doub_tau hyw,
      exact semi_tau_sequencer hv₂ hv₁},
    assumption}
end

lemma bisim_tau_none (R : option (mcrl2 α) → option (mcrl2 α) → Prop)  (x y) 
(R_bisim : is_semi_branching R) (h : R x y) (h' : has_tau_sequence x none) : has_tau_sequence y none ∧ R none none :=
begin
  rcases R_bisim with ⟨R_none, R_some, R_symm⟩,
  induction' h',
  { have h', by exact R_none y h,
    exact h'},
  { have hy, by exact seq_lift ⟨R_none, R_some, R_symm⟩ h h',
    rcases hy with ⟨w, hw, hw'⟩,
    specialize R_some y_1 w none tau hw' h_1,
    rcases R_some with ⟨v', w', hv₁, hv₂, hR₁, hR₂⟩,
    specialize R_none w' hR₂,
    apply and.intro,
    { apply doub_tau hw,
      apply doub_tau hv₁,
      apply semi_tau_sequencel hv₂,
      exact R_none.left},
    { exact R_none.right}}
end

lemma R_comp_none {R R' : option (mcrl2 α) → option (mcrl2 α) → Prop} 
(h : is_semi_branching R) (h' : is_semi_branching R') : 
none_branch (R_comp R R') :=
begin
  intros y h,
  cases h,
  { rcases h_h with ⟨w, hw, hw'⟩,
    have h₁, by exact h.left w hw,
    cases h₁,
    have hwy, by exact bisim_tau_none R' w y h' hw' h₁_left,
    cases hwy,
    apply and.intro hwy_left,
    apply R_comp.stepl ⟨none, h₁_right, hwy_right⟩},
  { rcases h_h with ⟨w, hw, hw'⟩,
    have h₁, by exact h'.left w (h'.right.right hw'),
    cases h₁,
    have hwy, by exact bisim_tau_none R w y h (h.right.right hw) h₁_left,
    cases hwy,
    apply and.intro hwy_left,
    apply R_comp.stepl ⟨none, hwy_right, h₁_right⟩}
end

lemma R_comp_some {R R' : option (mcrl2 α) → option (mcrl2 α) → Prop}
(h : is_semi_branching R) (h' : is_semi_branching R') : 
some_branch_sb (R_comp R R') :=
begin
  intros x y x' a hR hxax,
  have R_symm, by exact h.right.right,
  have R'_symm, by exact h'.right.right,
  have R_some, by exact h.right.left,
  have R'_some, by exact h'.right.left,
  cases hR,
  { rcases hR_h with ⟨w, hw₁, hw₂⟩,
    have hR, by exact R_some x w x' a hw₁ hxax,
    rcases hR with ⟨w', z, hw'₁, hw'₂, hR₁, hR₂⟩,
    have part1, by exact seq_lift h' hw₂ hw'₁,
    rcases part1 with ⟨y', hyy, hw'y⟩,
    rcases hw'₂ with ⟨w'', hw, hw₂⟩ | ⟨rfl, rfl⟩,
    { rw hw at *,
      have part2, by exact R'_some w'' y' z a hw'y hw₂,
      rcases part2 with ⟨v, z', hv₁, hv₂, hR'₁, hR'₂⟩,
      use v,
      use z',
      apply and.intro (doub_tau hyy hv₁),
      apply and.intro hv₂,
      apply and.intro,
      { apply R_comp.stepl,
        exact ⟨w'', hR₁, hR'₁⟩},
      { apply R_comp.stepl,
        exact ⟨z, hR₂, hR'₂⟩}},
    { use y',
      use y',
      apply and.intro hyy,
      apply and.intro,
      { apply or.inr,
        apply and.intro,
        repeat {refl}},
      apply and.intro,
      { exact R_comp.stepl ⟨z, hR₁, hw'y⟩},
      { exact R_comp.stepl ⟨z, hR₂, hw'y⟩}}},
  { rcases hR_h with ⟨w, hw₁, hw₂⟩,
    have hR', by exact R'_some x w x' a (R'_symm hw₂) hxax,
    rcases hR' with ⟨w', z, hw'₁, hw'₂, hR'₁, hR'₂⟩,
    have part1, by exact seq_lift h (R_symm hw₁) hw'₁,
    rcases part1 with ⟨y', hyy, hw'y⟩,
    rcases hw'₂ with ⟨w'', hw, hw₂⟩ | ⟨rfl, rfl⟩,
    { rw hw at *,
      have part2, by exact R_some w'' y' z a hw'y hw₂,
      rcases part2 with ⟨v, z', hv₁, hv₂, hR₁, hR₂⟩,
      use v,
      use z',
      apply and.intro (doub_tau hyy hv₁),
      apply and.intro hv₂,
      apply and.intro,
      { apply R_comp.stepr,
        exact ⟨w'', R_symm hR₁, R'_symm hR'₁⟩},
      { apply R_comp.stepr,
        exact ⟨z, R_symm hR₂, R'_symm hR'₂⟩}},
    { use y',
      use y',
      apply and.intro hyy,
      apply and.intro,
      { apply or.inr,
        apply and.intro,
        repeat {refl}},
      apply and.intro,
      { exact R_comp.stepr ⟨z, R_symm hw'y, R'_symm hR'₁⟩},
      { exact R_comp.stepr ⟨z, R_symm hw'y, R'_symm hR'₂⟩}}}
end

def stuttering (R : option (mcrl2 α) → option (mcrl2 α) → Prop) : Prop :=
∀x y x', R x y → R x' y → 
∀w : mcrl2 α, has_tau_sequence x w → transition w tau x' → R (some w) y 

lemma stuttering_inv {R : option (mcrl2 α) → option (mcrl2 α) → Prop} (h : stuttering R) 
: ∀x : mcrl2 α, ∀y x', R x y → R x' y → 
∀w , transition x tau w → has_tau_sequence w x' →  R w y :=
begin
  intros x y x' hR₁ hR₂ w hw₁ hw₂,
  induction hw₂,
  assumption,
  { specialize h x y hw₂_z hR₁ hR₂ hw₂_y,
    apply hw₂_ih,
    { apply h,
      { apply tau_left hw₁,
        exact hw₂_h'},
      { exact hw₂_h}},
    exact hw₁}
end

def largest_sb (x y) (h : sb_bisim α x y) : option (mcrl2 α) → option (mcrl2 α) → Prop :=
sorry

lemma largest_is_stuttering {x y} (h : sb_bisim α x y) : stuttering (largest_sb x y h) :=
sorry

lemma sb_reflexive : reflexive (sb_bisim α) :=
begin
  intro x,
  use (λx y, x = y),
  repeat {apply and.intro},
  refl,
  { intros y h,
    rw h,
    apply and.intro has_tau_sequence.refl,
    simp},
  { intros v w v' a hR ha,
    rw ←hR,
    use v,
    use v',
    apply and.intro has_tau_sequence.refl,
    apply and.intro,
    { exact or.inl ⟨v, rfl, ha⟩},
    simp},
  { intros x y h,
    exact eq.symm h}
end

lemma sb_symmetric : symmetric (sb_bisim α) :=
begin
  intros x y h,
  rcases h with ⟨R, hR, R_bisim⟩,
  use R,
  apply and.intro,
  { apply R_bisim.right.right hR},
  assumption
end

lemma sb_transitive : transitive (sb_bisim α) :=
begin
  intros x y z hxy hyz,
  rcases hxy with ⟨R, hR, R_bisim⟩,
  rcases hyz with ⟨R', hR', R'_bisim⟩,
  use R_comp R R',
  apply and.intro,
  { apply R_comp.stepl,
    exact ⟨y, hR, hR'⟩},
  { repeat {apply and.intro},
    exact R_comp_none R_bisim R'_bisim,
    exact R_comp_some R_bisim R'_bisim,
    exact comp_symmetric}
end
