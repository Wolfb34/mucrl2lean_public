import ..quotient
import ..transition.iff_lemmas

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]

/- Here we prove the congruence rules for the operators. -/
inductive R_alt {x₁ x₂ y₁ y₂ : mcrl2 α} (R₁ R₂ : mcrl2 α → mcrl2 α → Prop) :
mcrl2 α → mcrl2 α → Prop
| R₁ (x y) (h : R₁ x y) : R_alt x y
| R₂ (x y) (h : R₂ x y) : R_alt x y
| basel : R_alt (x₁ + y₁) (x₂ + y₂)
| baser : R_alt (x₂ + y₂) (x₁ + y₁)

theorem bisim.alt (x₁ x₂ y₁ y₂: mcrl2 α) (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂):
 x₁ + y₁ ≈ x₂ + y₂ :=
begin
  rcases h₁ with ⟨R₁, R₁x, R₁_bisim, R₁_symm⟩,
  rcases h₂ with ⟨R₂, R₂y, R₂_bisim, R₂_symm⟩,
  apply exists.intro (R_alt R₁ R₂),
  apply and.intro,
  { apply R_alt.basel},
  { apply and.intro,
    { intros x y x' a Rxy hxax',
      cases Rxy,
      { have h : ∃ y', transition y a y' ∧ option.rel R₁ x' y',
        by exact bisim_lift (and.intro R₁_bisim R₁_symm) Rxy_h hxax',
        exact bisim_exists_lift R_alt.R₁ h},
      { have h : ∃ y', transition y a y' ∧ option.rel R₂ x' y',
        by exact bisim_lift (and.intro R₂_bisim R₂_symm) Rxy_h hxax',
        exact bisim_exists_lift R_alt.R₂ h},
      { simp only [transition.alt_iff, or_and_distrib_right, exists_or_distrib],
        cases hxax',
        { have h : ∃y', transition x₂ a y' ∧ option.rel R₁ x' y',
          by exact bisim_lift (and.intro R₁_bisim R₁_symm) R₁x hxax'_h,
          left,
          apply bisim_exists_lift R_alt.R₁ h},
        { have h : ∃y', transition y₂ a y' ∧ option.rel R₂ x' y',
          by exact bisim_lift (and.intro R₂_bisim R₂_symm) R₂y hxax'_h,
          right,
          apply bisim_exists_lift R_alt.R₂ h}},
      { simp only [transition.alt_iff, or_and_distrib_right, exists_or_distrib],
        cases hxax',
        { have R₁x' : R₁ x₂ x₁, by apply R₁_symm R₁x,
          have h : ∃y', transition x₁ a y' ∧ option.rel R₁ x' y',
          by exact bisim_lift (and.intro R₁_bisim R₁_symm) R₁x' hxax'_h,
          left,
          apply bisim_exists_lift R_alt.R₁ h},
        { have R₂y' : R₂ y₂ y₁, by apply R₂_symm R₂y,
          have h : ∃y', transition y₁ a y' ∧ option.rel R₂ x' y',
          by exact bisim_lift (and.intro R₂_bisim R₂_symm) R₂y' hxax'_h,
          right,
          apply bisim_exists_lift R_alt.R₂ h}}},
    { intros x y h,
      cases h,
      { apply R_alt.R₁,
        exact R₁_symm h_h},
      { apply R_alt.R₂,
        exact R₂_symm h_h},
      { exact R_alt.baser},
      { exact R_alt.basel}}}
end

inductive R_seq {x₁ x₂ y₁ y₂ : mcrl2 α} (R₁ R₂ : mcrl2 α → mcrl2 α → Prop) :
mcrl2 α → mcrl2 α → Prop
| R₁ (x y) (h : R₁ x y) : R_seq x y
| R₂ (x y) (h : R₂ x y) : R_seq x y
| basel : R_seq (x₁ ⬝ y₁) (x₂ ⬝ y₂)
| baser : R_seq (x₂ ⬝ y₂) (x₁ ⬝ y₁)
| stepl {x y} (h : R₁ x y) : R_seq (x ⬝ y₁) (y ⬝ y₂)
| stepr {x y} (h : R₁ x y) : R_seq (y ⬝ y₂) (x ⬝ y₁)

lemma bisim_exists_lift_seq {x₁ x₂ y₁ y₂ y a x'} {R₁ R₂  : mcrl2 α → mcrl2 α → Prop}
 (hR₂ : R₂ y₁ y₂):
(∃y', transition y a y' ∧ option.rel R₁ x' y') → (∃y', transition y a y' ∧ option.rel (@R_seq _ _ x₁ x₂ y₁ y₂ R₁ R₂) (seq' x' y₁) (seq' y' y₂)) :=
begin
  intro h,
  cases h with w h_w,
  cases h_w with l r,
  apply exists.intro w,
  apply and.intro,
  assumption,
  cases r,
  { cases r,
    apply option.rel.some,
    apply R_seq.stepl,
    assumption},
  { apply option.rel.some,
    apply R_seq.R₂,
    assumption}
end

lemma bisim_exists_lift_seq_symm {x₁ x₂ y₁ y₂ y a x'} {R₁ R₂  : mcrl2 α → mcrl2 α → Prop}
 (hR₂ : R₂ y₂ y₁) (R₁_symm : symmetric R₁):
(∃y', transition y a y' ∧ option.rel R₁ x' y') → (∃y', transition y a y' ∧ option.rel (@R_seq _ _ x₁ x₂ y₁ y₂ R₁ R₂) (seq' x' y₂) (seq' y' y₁)) :=
begin
  intro h,
  cases h with w h_w,
  cases h_w with l r,
  apply exists.intro w,
  apply and.intro,
  assumption,
  cases r,
  { cases r,
    apply option.rel.some,
    apply R_seq.stepr,
    apply R₁_symm,
    assumption},
  { apply option.rel.some,
    apply R_seq.R₂,
    assumption}
end

theorem bisim.seq {x₁ x₂ y₁ y₂: mcrl2 α} (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂) :
 x₁ ⬝ y₁ ≈ x₂ ⬝ y₂ :=
begin
  rcases h₁ with ⟨R₁, R₁x, R₁_bisim, R₁_symm⟩,
  rcases h₂ with ⟨R₂, R₂y, R₂_bisim, R₂_symm⟩,
  apply exists.intro (R_seq R₁ R₂),
  apply and.intro,
  { apply R_seq.basel},
  { apply and.intro,
    { intros x y x' a Rxy xax',
      cases Rxy,
      { have h: ∃y', transition y a y' ∧ option.rel R₁ x' y',
        by exact bisim_lift (and.intro R₁_bisim R₁_symm) Rxy_h xax',
        exact bisim_exists_lift R_seq.R₁ h},
      { have h: ∃y', transition y a y' ∧ option.rel R₂ x' y',
        by exact bisim_lift (and.intro R₂_bisim R₂_symm) Rxy_h xax',
        exact bisim_exists_lift R_seq.R₂ h},
      { cases xax',
        simp only [transition.seq_iff, ←exists_and_distrib_right, and_assoc, exists_comm, exists_eq_left],
        specialize R₁_bisim x₁ x₂ xax'_z a R₁x xax'_h,
        apply bisim_exists_lift_seq,
        repeat {assumption}},
      { cases xax',
        simp only [transition.seq_iff, ←exists_and_distrib_right, and_assoc, exists_comm, exists_eq_left],
        specialize R₁_bisim x₂ x₁ xax'_z a (R₁_symm R₁x) xax'_h,
        apply bisim_exists_lift_seq_symm,
        exact (R₂_symm R₂y),
        repeat {assumption}},
      { cases xax',
        simp only [transition.seq_iff, ←exists_and_distrib_right, and_assoc, exists_comm, exists_eq_left],
        specialize R₁_bisim Rxy_x Rxy_y xax'_z a Rxy_h xax'_h,
        apply bisim_exists_lift_seq,
        repeat {assumption}},
      { cases xax',
        simp only [transition.seq_iff, ←exists_and_distrib_right, and_assoc, exists_comm, exists_eq_left],
        specialize R₁_bisim Rxy_y Rxy_x xax'_z a (R₁_symm Rxy_h) xax'_h,
        apply bisim_exists_lift_seq_symm,
        exact (R₂_symm R₂y),
        repeat {assumption}}},
    { intros x y h,
      cases h,
      { apply R_seq.R₁,
        apply R₁_symm,
        assumption},
      { apply R_seq.R₂,
        apply R₂_symm,
        assumption},
      { exact R_seq.baser},
      { exact R_seq.basel},
      { exact R_seq.stepr h_h},
      { exact R_seq.stepl h_h}}}
end