import .transition.transition

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]


/- Defining the notion of bisimulation for mcrl2 processes. -/
def is_bisimulation (R : mcrl2 α → mcrl2 α → Prop) : Prop :=
(∀x y : mcrl2 α, (∀x' a, R x y → transition x a x' → ∃y', transition y a y' ∧ option.rel R x' y')) ∧ symmetric R

#print is_bisimulation
def bisim (α : Type) [comm_semigroup_with_zero α] : mcrl2 α → mcrl2 α → Prop
| x y := ∃R : mcrl2 α → mcrl2 α → Prop, (R x y) ∧ is_bisimulation R

/- Helper lemmas for proofs. -/
lemma option.rel.mono {R₁ R₂ : mcrl2 α → mcrl2 α → Prop}
(h : ∀{x y}, R₁ x y → R₂ x y) :
∀{x y}, option.rel R₁ x y → option.rel R₂ x y
| none none (option.rel.none) := by exact option.rel.none
| (some x) (some y) (option.rel.some R₁) :=
begin
  apply option.rel.some,
  apply h,
  assumption
end

lemma option.rel.refl {x₁ : option (mcrl2 α)} {R : mcrl2 α → mcrl2 α → Prop}
(h: ∀x, R x x) :
option.rel R x₁ x₁ :=
begin
  cases x₁,
  { exact option.rel.none},
  { apply option.rel.some,
    exact h x₁}
end

lemma bisim_lift_none {x y : mcrl2 α} {a : α} {R : mcrl2 α → mcrl2 α → Prop}
: is_bisimulation R → R x y → transition x a none -> transition y a none :=
begin
  intros h₁ h₂ h₃,
  cases h₁,
  specialize h₁_left x y none a h₂ h₃,
  cases h₁_left with w w_h,
  cases w_h with l r,
  cases w,
  { assumption},
  { cases r}
end

lemma bisim_lift {x y : mcrl2 α} {a : α} {x' : option (mcrl2 α)} {R : mcrl2 α → mcrl2 α → Prop}
: is_bisimulation R → R x y → transition x a x' -> ∃ y', transition y a y' ∧ option.rel R x' y' :=
begin
  intros h₁ h₂ h₃,
  cases h₁,
  specialize h₁_left x y x' a h₂ h₃,
  cases h₁_left with w h_w,
  apply exists.intro w,
  exact h_w
end

lemma bisim_symm_lift {x y a y'} {R : mcrl2 α → mcrl2 α → Prop} :
is_bisimulation R → R x y → transition y a y' → ∃ x', transition x a x' ∧ option.rel R y' x':=
begin
  intros R_bisim hRxy h,
  cases R_bisim with R_bisim R_symm,
  have hRyx: R y x, by apply R_symm; assumption,
  exact bisim_lift (and.intro R_bisim R_symm) hRyx h
end

lemma bisim_exists_lift {y a x'} {R R' : mcrl2 α → mcrl2 α → Prop}
(hR : ∀{x y}, R x y → R' x y) :
(∃y', transition y a y' ∧ option.rel R x' y') → (∃y', transition y a y' ∧ option.rel R' x' y') :=
begin
  intro h,
  apply Exists.imp _ h,
  intro y',
  rintro ⟨yay', Rx'y'⟩,
  apply and.intro,
  assumption,
  apply option.rel.mono @hR,
  assumption
end

/- Proving that bisimilarity is an equivalence relation. -/
theorem bisim_reflexive : reflexive (bisim α) :=
begin
  intro x,
  apply exists.intro (λa b, a = b),
  apply and.intro,
  { simp},
  { apply and.intro,
    { intros x' y,
      intros y' a h₁ h₂,
      apply exists.intro y',
      apply and.intro,
      { rw ←h₁,
        assumption},
      { simp,
        cases y',
        { exact option.rel.none},
        { apply option.rel.some,
          refl}}},
    { intros x' y' h,
      apply eq.symm,
      assumption}}
end

theorem bisim_symmetric : symmetric (bisim α) :=
begin
  intros x y h,
  cases h with R h,
  cases h with rxy r_bisim,
  cases r_bisim with r_bisim r_symm,
  apply exists.intro R,
  apply and.intro,
  { exact r_symm rxy},
  { exact and.intro r_bisim r_symm}
end

/- Proving transitivity via the symmetric composition of relations-/
inductive R_comp {α : Type 1} (R₁ R₂ : α → α → Prop) :
α → α → Prop
| stepl {a b} (h : ∃c, R₁ a c ∧ R₂ c b) : R_comp a b
| stepr {a b} (h : ∃c, R₁ a c ∧ R₂ c b) : R_comp b a

lemma comp_symmetric {R R' : mcrl2 α → mcrl2 α → Prop} :
symmetric (R_comp R R') :=
begin
  intros x y h,
  cases h,
  { exact R_comp.stepr h_h},
  { exact R_comp.stepl h_h}
end

lemma comp_bisim {R R' : mcrl2 α → mcrl2 α → Prop}
(hr : is_bisimulation R) (hr' : is_bisimulation R') :
is_bisimulation (R_comp R R') :=
begin
  apply and.intro,
  { intros x y x' a l r,
    cases l,
    { cases l_h with w h,
      cases h with Rx R'y,
      have h₁: ∃y', transition w a y' ∧ option.rel R x' y',
      by exact bisim_lift hr Rx r,
      cases h₁ with w' w'_h,
      cases w'_h with wa Rw',
      have h₁: ∃y', transition y a y' ∧ option.rel R' w' y',
      by exact bisim_lift hr' R'y wa,
      cases h₁ with y' h_y',
      cases h_y' with ya R'w',
      apply exists.intro y',
      apply and.intro,
      { assumption},
      { cases Rw',
        { cases R'w',
          apply option.rel.some,
          cases Rw',
          cases R'w',
          apply R_comp.stepl,
          apply exists.intro Rw'_b,
          apply and.intro,
          repeat {assumption}},
        { cases R'w',
          exact option.rel.none}}},
    { cases l_h with w h,
      cases h with Ry R'x,
      have Ry' : R w y, by exact hr.right Ry,
      have R'x' : R' x w, by exact hr'.right R'x,
      have h₁: ∃y', transition w a y' ∧ option.rel R' x' y',
      by exact bisim_lift hr' R'x' r,
      cases h₁ with w' w'_h,
      cases w'_h with wa Rw',
      have h₁: ∃y', transition y a y' ∧ option.rel R w' y',
      by exact bisim_lift hr Ry' wa,
      cases h₁ with y' h_y',
      cases h_y' with ya R'w',
      apply exists.intro y',
      apply and.intro,
      { assumption},
      { cases Rw',
          { cases R'w',
            apply option.rel.some,
            apply R_comp.stepr,
            cases Rw',
            cases R'w',
            apply exists.intro Rw'_b,
            apply and.intro,
            { apply hr.right, assumption},
            { apply hr'.right, assumption}
            },
          { cases R'w',
            exact option.rel.none}}}},
  { exact comp_symmetric}
end

theorem bisim_transitive : transitive (bisim α) :=
begin
  intros x y z h₁ h₂,
  cases h₁ with R,
  cases h₁_h with Rxy R_bisim,
  cases h₂ with R',
  cases h₂_h with R'yz R'_bisim,
  apply exists.intro (R_comp R R'),
  apply and.intro,
  { apply R_comp.stepl,
    apply exists.intro y,
    apply and.intro,
    repeat {assumption}},
  { apply comp_bisim R_bisim R'_bisim}
end

/- Defining the quotient of mcrl2'-/
@[instance] def setoid_mcrl2 : setoid (mcrl2 α) :=
{r     := bisim α,
 iseqv :=
  begin
    repeat {apply and.intro},
    { apply bisim_reflexive},
    { apply bisim_symmetric},
    { apply bisim_transitive}
  end
}

lemma setoid_iff (a b : mcrl2 α) :
a ≈ b ↔ bisim α a b :=
by refl

def mcrl2' (α : Type) [comm_semigroup_with_zero α] := quotient (@setoid_mcrl2 α _)