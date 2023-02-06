import ..mcrl2_basic.mcrl2_basic

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]

/- Finally, the || operator.-/
inductive R_par {x₁ x₂ y₁ y₂ : mcrl2 α} (R₁ R₂ : mcrl2 α → mcrl2 α → Prop) :
mcrl2 α → mcrl2 α → Prop
| R₁ {x y} (h : R₁ x y) : R_par x y
| R₂ {x y} (h : R₂ x y) : R_par x y
| basel : R_par (x₁ || y₁) (x₂ || y₂)
| baser : R_par (x₂ || y₂) (x₁ || y₁)
| stepl {x x' y y' a z z'} (hR₁x : R₁ x x') (hR₂ : R₂ y y') (hR₁z : R₁ z z') 
  (ht  : transition x  a z)
  (ht' : transition x' a z') :
  R_par (z || y) (z' || y')
| stepr {x x' y y' a z z'} (hR₁x : R₁ x x') (hR₂ : R₂ y y') (hR₁z : R₂ z z') 
  (ht  : transition y  a z)
  (ht' : transition y' a z') :
  R_par (x || z) (x' || z')
| stepcomm {x x' y y' a b z₁ z₂ z₁' z₂'} (hR₁x : R₁ x x') (hR₂y : R₂ y y') 
  (hR₁z : R₁ z₁ z₁' ) (hR₂z : R₂ z₂ z₂' )
  (hx  : transition x  a z₁)  (hy  : transition y  b z₂)
  (hx' : transition x' a z₁') (hy' : transition y' b z₂') :
  R_par (z₁ || z₂) (z₁' || z₂')

lemma bisim_exists_lift_par_l {x₁ x₂ y₁ y₂ x x' y y' a z} {R₁ R₂  : mcrl2 α → mcrl2 α → Prop} 
 (hxz : transition x a z) (hR₁ : R₁ x x') (hR₂ : R₂ y y') :
(∃z', transition x' a z' ∧ option.rel R₁ z z') → (∃z', transition x' a z' ∧ option.rel (@R_par _ _ x₁ x₂ y₁ y₂ R₁ R₂) (par' z y) (par' z' y')) :=
begin 
  intro h,
  rcases h with ⟨w, hwa, hRw⟩,
  apply exists.intro w,
  apply and.intro,
  assumption,
  cases hRw,
  { apply option.rel.some,
    apply R_par.stepl,
    exact hR₁,
    repeat {assumption}},
  { apply option.rel.some,
    apply R_par.R₂,
    assumption}
end

lemma bisim_exists_lift_par_r {x₁ x₂ y₁ y₂ x x' y y' a z} {R₁ R₂  : mcrl2 α → mcrl2 α → Prop} 
 (hxz : transition y a z) (hR₁ : R₁ x x') (hR₂ : R₂ y y') :
(∃z', transition y' a z' ∧ option.rel R₂ z z') → (∃z', transition  y' a z' ∧ option.rel (@R_par _ _ x₁ x₂ y₁ y₂ R₁ R₂) (par' x z) (par' x' z')) :=
begin 
  intro h,
  rcases h with ⟨w, hwa, hRw⟩,
  apply exists.intro w,
  apply and.intro,
  assumption,
  cases hRw,
  { apply option.rel.some,
    apply R_par.stepr,
    repeat {assumption}},
  { apply option.rel.some,
    apply R_par.R₁,
    assumption}
end

lemma bisim_exists_lift_par_comm {x₁ x₂ y₁ y₂ x x' y y' a b z₁ z₂} {R₁ R₂  : mcrl2 α → mcrl2 α → Prop} 
 (hxz : transition x a z₁) (hyz' : transition y b z₂) (hR₁ : R₁ x x') (hR₂ : R₂ y y') (hab : a * b ≠ 0):
(∃z' , transition x' a z' ∧ option.rel R₁ z₁ z') → (∃z' , transition y' b z' ∧ option.rel R₂ z₂ z') → 
(∃z', transition (x' || y') (a * b) z' ∧ option.rel (@R_par _ _ x₁ x₂ y₁ y₂ R₁ R₂) (par' z₁ z₂) z') :=
begin 
  intros h₁ h₂,
  rcases h₁ with ⟨w₁, hw₁a, hRw₁⟩,
  rcases h₂ with ⟨w₂, hw₂b, hRw₂⟩,
  simp only [transition.par_iff, exists_or_distrib, or_and_distrib_right, ←exists_and_distrib_right, and_assoc, exists_eq_left],
  apply or.inr,
  apply or.inr,
  apply exists.intro (par' w₁ w₂),
  apply exists.intro w₁,
  apply exists.intro w₂,
  apply and.intro,
  refl,
  apply exists.intro a,
  apply exists.intro b,
  apply and.intro,
  assumption,
  apply and.intro,
  refl,
  apply and.intro,
  assumption,
  apply and.intro,
  assumption,
  cases hRw₂,
  { cases hRw₁,
    { apply option.rel.some,
      apply R_par.stepcomm,
      exact hR₁,
      exact hR₂,
      assumption,
      assumption,
      repeat {assumption}},
    { apply option.rel.some,
      cases hRw₂,
      apply R_par.R₂,
      assumption}},
  { cases hRw₁,
    { apply option.rel.some,
      apply R_par.R₁,
      assumption},
    { apply option.rel.none}}
end

lemma bisim_exists_lift_par {x₁ x₂ y₁ y₂ x x' y y' a z} {R₁ R₂ : mcrl2 α → mcrl2 α → Prop} 
 (R₁_bisim : is_bisimulation R₁) (R₂_bisim : is_bisimulation R₂) (hR₁ : R₁ x x') (hR₂ : R₂ y y') (haz : transition (x || y) a z):
 (∃z', transition (x' || y') a z' ∧ option.rel (@R_par _ _ x₁ x₂ y₁ y₂ R₁ R₂) z z') :=
begin 
  cases R₁_bisim with R₁_bisim R₁_symm,
  cases R₂_bisim with R₂_bisim R₂_symm,
  cases haz,
  { specialize R₁_bisim x x' haz_x' a hR₁ haz_h,
    simp only [transition.par_iff, exists_or_distrib, or_and_distrib_right, ←exists_and_distrib_right, and_assoc, exists_eq_left],
    apply or.inl,
    simp only [exists_comm, exists_eq_left],
    exact bisim_exists_lift_par_l haz_h hR₁ hR₂ R₁_bisim},
  { specialize R₂_bisim y y' haz_y' a hR₂ haz_h, 
    simp only [transition.par_iff, exists_or_distrib, or_and_distrib_right, ←exists_and_distrib_right, and_assoc, exists_eq_left],
    apply or.inr,
    apply or.inl,
    simp only [exists_comm, exists_eq_left],
    exact bisim_exists_lift_par_r haz_h hR₁ hR₂ R₂_bisim},
  { specialize R₁_bisim x x' haz_x' haz_a hR₁ haz_h₁, 
    specialize R₂_bisim y y' haz_y' haz_b hR₂ haz_h₂,
    exact bisim_exists_lift_par_comm haz_h₁ haz_h₂ hR₁ hR₂ haz_h₃ R₁_bisim R₂_bisim}

end

lemma R_par.symm {x₁ x₂ y₁ y₂ : mcrl2 α} {R₁ R₂ : mcrl2 α → mcrl2 α → Prop} 
 (h₁ : symmetric R₁) (h₂ : symmetric R₂) :
symmetric (@R_par α _ x₁ x₂ y₁ y₂ R₁ R₂) :=
begin
  intros x y h,
  cases h,
  { apply R_par.R₁,
    apply h₁,
    assumption},
  { apply R_par.R₂,
    apply h₂,
    assumption},
  { exact R_par.baser},
  { exact R_par.basel},
  { apply R_par.stepl,
    exact h₁ h_hR₁x,
    apply h₂,
    assumption,
    apply h₁,
    assumption,
    repeat {assumption}},
  { apply R_par.stepr,
    apply h₁,
    exact h_hR₁x,
    exact h₂ h_hR₂,
    apply h₂,
    repeat {assumption}},
  { apply R_par.stepcomm,
    exact h₁ h_hR₁x,
    exact h₂ h_hR₂y,
    exact h₁ h_hR₁z,
    exact h₂ h_hR₂z,
    repeat {assumption}}
end

theorem bisim.par {x₁ x₂ y₁ y₂: mcrl2 α} (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂) : 
x₁ || y₁ ≈ x₂ || y₂ :=
begin
  rcases h₁ with ⟨R₁, R₁x, R₁_bisim⟩,
  rcases h₂ with ⟨R₂, R₂y, R₂_bisim⟩,
  apply exists.intro (R_par R₁ R₂),
  apply and.intro,
  apply R_par.basel,
  apply and.intro,
  { intros x y x' a Rxy xax',
    cases Rxy,
    { have h: ∃y', transition y a y' ∧ option.rel R₁ x' y',
      by exact bisim_lift R₁_bisim Rxy_h xax',
      cases h with w h_w,
      cases h_w with l r,
      apply exists.intro w,
      apply and.intro,
      assumption,
      apply option.rel.mono,
      { intros x y, exact R_par.R₁},
      { assumption}},
    { have h: ∃y', transition y a y' ∧ option.rel R₂ x' y',
      by exact bisim_lift R₂_bisim Rxy_h xax',
      cases h with w h_w,
      cases h_w with l r,
      apply exists.intro w,
      apply and.intro,
      assumption,
      apply option.rel.mono,
      { intros x y, exact R_par.R₂},
      { assumption}},
    { exact bisim_exists_lift_par R₁_bisim R₂_bisim R₁x R₂y xax' },
    { exact bisim_exists_lift_par R₁_bisim R₂_bisim (R₁_bisim.right R₁x) (R₂_bisim.right R₂y) xax'},
    { apply bisim_exists_lift_par; assumption},
    { apply bisim_exists_lift_par; assumption},
    { apply bisim_exists_lift_par; assumption}},
  { exact R_par.symm R₁_bisim.right R₂_bisim.right}
end