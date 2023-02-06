import ..mcrl2_mrg.mcrl2_mrg

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]

/- The relation used to prove congruence of encapsulation-/
inductive R_encap {x₁ y₁ : mcrl2 α} {A : set α} (R : mcrl2 α → mcrl2 α → Prop) :
mcrl2 α → mcrl2 α → Prop
| R {x y} (h : R x y) : R_encap x y
| basel : R_encap (encap A x₁) (encap A y₁)
| baser : R_encap (encap A y₁) (encap A x₁)
| step {x y} (h : R x y) : R_encap (encap A x) (encap A y)

theorem R_encap.symm {x₁ y₁ A R} (R_symm : symmetric R) :
symmetric (@R_encap α _ x₁ y₁ A R) :=
begin
  intros x y h,
  cases h,
  { apply R_encap.R,
    exact R_symm h_h},
  { exact R_encap.baser},
  { exact R_encap.basel},
  { exact R_encap.step (R_symm h_h)}
end

theorem bisim.encap {x₁ x₂ : mcrl2 α} {A} (h : x₁ ≈ x₂) : 
(encap A x₁) ≈ (encap A x₂) :=
begin
  rcases h with ⟨R, Rx, R_bisim⟩,
  apply exists.intro (R_encap R),
  apply and.intro R_encap.basel,
  apply and.intro,
  { intros x y x' a h₁ h₂, 
    cases h₁,
    { have h : ∃y', transition y a y' ∧ option.rel R x' y',
      by exact bisim_lift R_bisim h₁_h h₂,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro w,
      apply and.intro haw,
      apply option.rel.mono,
      { intros a b, exact R_encap.R},
      { assumption}},
    { cases h₂,
      have h : ∃y', transition x₂ a y' ∧ option.rel R h₂_y y',
      by exact bisim_lift R_bisim Rx h₂_h₂,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro (encap A <$> w), 
      apply and.intro,
      { apply transition.encap_pass; assumption},
      { cases hRw,
        { apply option.rel.some,
          apply R_encap.step,
          assumption},
        { exact option.rel.none}}},
    { cases h₂,
      have h : ∃y', transition x₁ a y' ∧ option.rel R h₂_y y',
      by exact bisim_lift R_bisim (R_bisim.right Rx) h₂_h₂,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro (encap A <$> w), 
      apply and.intro,
      { apply transition.encap_pass; assumption},
      { cases hRw,
        { apply option.rel.some,
          apply R_encap.step,
          assumption},
        { exact option.rel.none}}},
    { cases h₂,
      have h : ∃y', transition h₁_y a y' ∧ option.rel R h₂_y y',
      by exact bisim_lift R_bisim h₁_h h₂_h₂,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro (encap A <$> w), 
      apply and.intro,
      { apply transition.encap_pass; assumption},
      { cases hRw,
        { apply option.rel.some,
          apply R_encap.step,
          assumption},
        { exact option.rel.none}}}},
  { exact R_encap.symm R_bisim.right} 
end