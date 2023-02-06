import ..mcrl2_basic.mcrl2_basic

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]

/- This relation is used to prove congruence of communication. The proof requires helper lemmas that are further on.-/
inductive R_comm {x₁ x₂ y₁ y₂ : mcrl2 α} (R₁ R₂ : mcrl2 α → mcrl2 α → Prop) :
mcrl2 α → mcrl2 α → Prop
| R₁ {x y} (h : R₁ x y) : R_comm x y
| R₂ {x y} (h : R₂ x y) : R_comm x y
| basel : R_comm (x₁ ∣ y₁) (x₂ ∣ y₂)
| baser : R_comm (x₂ ∣ y₂) (x₁ ∣ y₁)
| stepl {a b x₁' x₂' y₁' y₂'} (hR₁ : R₁ x₁' x₂') (hR₂ : R₂ y₁' y₂' )
 (h₁x : transition x₁ a x₁') (h₂x : transition x₂ a x₂') 
 (h₁y : transition y₁ b y₁') (h₂y : transition y₂ b y₂') :
R_comm (x₁' || y₁') (x₂' || y₂') 
| stepr {a b x₁' x₂' y₁' y₂'} (hR₁ : R₁ x₁' x₂') (hR₂ : R₂ y₁' y₂' )
 (h₁x : transition x₁ a x₁') (h₂x : transition x₂ a x₂') 
 (h₁y : transition y₁ b y₁') (h₂y : transition y₂ b y₂') :
R_comm (x₂' || y₂') (x₁' || y₁') 
| par_l {x x' y y' a z z'} (hR : R_comm (x || y) (x' || y')) (hR' : R_comm (x' || y') (x || y))
  (hR₁ : R₁ x x') (hR₂ : R₂ y y')
  (hRz : R₁ z z')
  (ht : transition x a z) (ht' : transition x' a z') :
  R_comm (z || y) (z' || y') 
| par_r {x x' y y' a z z'} (hR : R_comm (x || y) (x' || y')) (hR' : R_comm (x' || y') (x || y))
  (hR₁ : R₁ x x') (hR₂ : R₂ y y')
  (hRz : R₂ z z')
  (ht : transition y a z) (ht' : transition y' a z') :
  R_comm (x || z) (x' || z')
| comm {x x' y y' a b z₁ z₁' z₂ z₂'} (hR : R_comm (x || y) (x' || y')) (hR' : R_comm (x' || y') (x || y))
  (hRz₁ : R₁ z₁ z₁') (hRz₂ : R₂ z₂ z₂')
  (hR₁ : R₁ x x') (hR₂ : R₂ y y')
  (htx : transition x a z₁) (htx' : transition x' a z₁')
  (hty : transition y b z₂) (hty' : transition y' b z₂') :
  R_comm (z₁ || z₂) (z₁' || z₂')

lemma R_comm.symm {x₁ x₂ y₁ y₂ : mcrl2 α} {R₁ R₂ : mcrl2 α → mcrl2 α → Prop}
(h₁ : symmetric R₁) (h₂ : symmetric R₂):
symmetric (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) :=
begin
  intros x y h,
  cases h,
  { apply R_comm.R₁,
    apply h₁,
    assumption},
  { apply R_comm.R₂,
    apply h₂,
    assumption},
  { exact R_comm.baser},
  { exact R_comm.basel},
  { apply R_comm.stepr; assumption},
  { apply R_comm.stepl; assumption},
  { apply R_comm.par_l,
    repeat {assumption},
    exact h₁ h_hR₁,
    exact h₂ h_hR₂,
    exact h₁ h_hRz},
  { apply R_comm.par_r,
    repeat {assumption},
    exact h₁ h_hR₁,
    exact h₂ h_hR₂,
    apply h₂ h_hRz},
  { apply R_comm.comm,
    exact h_hR',
    repeat {assumption},
    exact h₁ h_hRz₁,
    exact h₂ h_hRz₂,
    exact h₁ h_hR₁,
    exact h₂ h_hR₂}
end

lemma bisim_exists_lift_comm_l {x₁ x₂ y₁ y₂ x x' y y' a z} {R₁ R₂  : mcrl2 α → mcrl2 α → Prop} 
 (hxz : transition x a z)
 (hR₁ : R₁ x x') (hR₂ : R₂ y y')
 (hR : (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (x || y) (x' || y' )) 
 (hR' : (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (x' || y' ) (x || y)) :
(∃z', transition x' a z' ∧ option.rel R₁ z z') → (∃z', transition x' a z' ∧ option.rel (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (par' z y) (par' z' y')) :=
begin 
  intro h,
  rcases h with ⟨w, hwa, hRw⟩,
  apply exists.intro w,
  apply and.intro,
  assumption,
  cases hRw,
  { apply option.rel.some,
    apply R_comm.par_l,
    exact hR,
    repeat {assumption}},
  { apply option.rel.some,
    apply R_comm.R₂,
    assumption}
end

lemma bisim_exists_lift_comm_r {x₁ x₂ y₁ y₂ x x' y y' a z} {R₁ R₂  : mcrl2 α → mcrl2 α → Prop} 
 (hxz : transition y a z)
 (hR₁ : R₁ x x') (hR₂ : R₂ y y')
 (hR : (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (x || y) (x' || y' )) 
 (hR' : (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (x' || y' ) (x || y)) :
(∃z', transition y' a z' ∧ option.rel R₂ z z') → (∃z', transition y' a z' ∧ option.rel (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (par' x z) (par' x' z')) :=
begin 
  intro h,
  rcases h with ⟨w, hwa, hRw⟩,
  apply exists.intro w,
  apply and.intro,
  assumption,
  cases hRw,
  { apply option.rel.some,
    apply R_comm.par_r,
    exact hR,
    repeat {assumption}},
  { apply option.rel.some,
    apply R_comm.R₁,
    assumption}
end

lemma bisim_exists_lift_comm_comm {x₁ x₂ y₁ y₂ x x' y y' a b z₁ z₂} {R₁ R₂  : mcrl2 α → mcrl2 α → Prop} 
 (hxz : transition x a z₁) (hyz' : transition y b z₂) (hR₁ : R₁ x x') (hR₂ : R₂ y y') 
 (hab : a * b ≠ 0)
 (hR : (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (x || y) (x' || y' )) 
 (hR' : (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (x' || y' ) (x || y)) :
(∃z' , transition x' a z' ∧ option.rel R₁ z₁ z') → (∃z' , transition y' b z' ∧ option.rel R₂ z₂ z') → 
(∃z', transition (x' || y') (a * b) z' ∧ option.rel (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (par' z₁ z₂) z') :=
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
      apply R_comm.comm,
      repeat {assumption}},
    { apply option.rel.some,
      cases hRw₂,
      apply R_comm.R₂,
      assumption}},
  { cases hRw₁,
    { apply option.rel.some,
      apply R_comm.R₁,
      assumption},
    { apply option.rel.none}}
end

lemma bisim_exists_lift_comm {x₁ x₂ y₁ y₂ x x' y y' a z} {R₁ R₂ : mcrl2 α → mcrl2 α → Prop} 
 (R₁_bisim : is_bisimulation R₁) (R₂_bisim : is_bisimulation R₂) (hR₁ : R₁ x x') (hR₂ : R₂ y y') (haz : transition (x || y) a z)
 (hR : (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (x || y) (x' || y' )) 
 (hR' : (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) (x' || y' ) (x || y)) :
 (∃z', transition (x' || y') a z' ∧ option.rel (@R_comm _ _ x₁ x₂ y₁ y₂ R₁ R₂) z z') :=
begin 
  cases R₁_bisim with R₁_bisim R₁_symm,
  cases R₂_bisim with R₂_bisim R₂_symm,
  cases haz,
  { specialize R₁_bisim x x' haz_x' a hR₁ haz_h,
    simp only [transition.par_iff, exists_or_distrib, or_and_distrib_right, ←exists_and_distrib_right, and_assoc, exists_eq_left],
    apply or.inl,
    simp only [exists_comm, exists_eq_left],
    exact bisim_exists_lift_comm_l haz_h hR₁ hR₂ hR hR' R₁_bisim,},
  { specialize R₂_bisim y y' haz_y' a hR₂ haz_h, 
    simp only [transition.par_iff, exists_or_distrib, or_and_distrib_right, ←exists_and_distrib_right, and_assoc, exists_eq_left],
    apply or.inr,
    apply or.inl,
    simp only [exists_comm, exists_eq_left],
    exact bisim_exists_lift_comm_r haz_h hR₁ hR₂ hR hR' R₂_bisim},
  { specialize R₁_bisim x x' haz_x' haz_a hR₁ haz_h₁, 
    specialize R₂_bisim y y' haz_y' haz_b hR₂ haz_h₂,
    exact bisim_exists_lift_comm_comm haz_h₁ haz_h₂ hR₁ hR₂ haz_h₃ hR hR' R₁_bisim R₂_bisim}
end

/- The main congruence theorem for |.-/
theorem bisim.comm {x₁ x₂ y₁ y₂: mcrl2 α} (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂) : 
x₁ ∣ y₁ ≈ x₂ ∣ y₂ :=
begin 
  rcases h₁ with ⟨R₁, R₁x, R₁_bisim⟩,
  rcases h₂ with ⟨R₂, R₂y, R₂_bisim⟩,
  apply exists.intro (R_comm R₁ R₂),
  apply and.intro,
  apply R_comm.basel,
  apply and.intro,
  { intros x y x' a Rxy xax',
    cases Rxy,
    { apply bisim_exists_lift,
      { intros v w, exact R_comm.R₁},
      { apply bisim_lift; assumption}},
    { apply bisim_exists_lift,
      { intros v w, exact R_comm.R₂},
      { apply bisim_lift; assumption}},
    { simp [transition.comm_iff, ←exists_and_distrib_right, and_assoc],
      cases xax',
      cases R₁_bisim with R₁_bisim R₁_symm,
      specialize R₁_bisim x₁ x₂ xax'_x' xax'_a R₁x xax'_h₁,
      rcases R₁_bisim with ⟨w, haw, Rw⟩,
      cases R₂_bisim with R₂_bisim R₂_symm,
      specialize R₂_bisim y₁ y₂ xax'_y' xax'_b R₂y xax'_h₂,
      rcases R₂_bisim with ⟨w', haw', Rw'⟩,
      apply exists.intro (par' w w'),
      apply exists.intro w,
      apply exists.intro w',
      apply and.intro,
      refl,
      apply exists.intro xax'_a,
      apply exists.intro xax'_b,
      apply and.intro,
      refl,
      apply and.intro,
      assumption,
      apply and.intro,
      assumption,
      apply and.intro,
      assumption,
      cases Rw,
      { cases Rw',
        { apply option.rel.some,
          apply R_comm.stepl; assumption},
        { apply option.rel.some,
          exact R_comm.R₁ Rw_ᾰ}},
      { cases Rw',
        { apply option.rel.some,
          apply R_comm.R₂,
          assumption},
        { exact option.rel.none}}},
    { simp [transition.comm_iff, ←exists_and_distrib_right, and_assoc],
      cases xax',
      cases R₁_bisim with R₁_bisim R₁_symm,
      specialize R₁_bisim x₂ x₁ xax'_x' xax'_a (R₁_symm R₁x) xax'_h₁,
      rcases R₁_bisim with ⟨w, haw, Rw⟩,
      cases R₂_bisim with R₂_bisim R₂_symm,
      specialize R₂_bisim y₂ y₁ xax'_y' xax'_b (R₂_symm R₂y) xax'_h₂,
      rcases R₂_bisim with ⟨w', haw', Rw'⟩,
      apply exists.intro (par' w w'),
      apply exists.intro w,
      apply exists.intro w',
      apply and.intro,
      refl,
      apply exists.intro xax'_a,
      apply exists.intro xax'_b,
      apply and.intro,
      refl,
      apply and.intro,
      assumption,
      apply and.intro,
      assumption,
      apply and.intro, 
      assumption,
      cases Rw,
      { cases Rw',
        { apply option.rel.some,
          apply R_comm.stepr,
          exact R₁_symm Rw_ᾰ,
          exact R₂_symm Rw'_ᾰ,
          repeat {assumption}},
        { apply option.rel.some,
          exact R_comm.R₁ Rw_ᾰ}},
      { cases Rw',
        { apply option.rel.some,
          apply R_comm.R₂,
          assumption},
        { exact option.rel.none}}},
    { apply bisim_exists_lift_comm,
      repeat {assumption},
      exact R_comm.symm R₁_bisim.right R₂_bisim.right Rxy},
    { apply bisim_exists_lift_comm,
      repeat {assumption},
      exact R₁_bisim.right Rxy_hR₁,
      exact R₂_bisim.right Rxy_hR₂,
      exact R_comm.symm R₁_bisim.right R₂_bisim.right Rxy},
    { apply bisim_exists_lift_comm,
      repeat {assumption},
      exact R_comm.symm R₁_bisim.right R₂_bisim.right Rxy},
    { apply bisim_exists_lift_comm,
      repeat {assumption},
      exact R_comm.symm R₁_bisim.right R₂_bisim.right Rxy},
    { apply bisim_exists_lift_comm,
      repeat {assumption},
      exact R_comm.symm R₁_bisim.right R₂_bisim.right Rxy}},
  { exact R_comm.symm R₁_bisim.right R₂_bisim.right}
end