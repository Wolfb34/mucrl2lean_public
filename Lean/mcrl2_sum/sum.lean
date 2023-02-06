import ..mcrl2_encap.mcrl2_encap

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]
variable {β : Type}

/- The relation used to prove congruence of the summation operator.-/
inductive R_sum {f g} {D : set β} (R_α : ∀a, a ∈ D → mcrl2 α → mcrl2 α → Prop) : 
mcrl2 α → mcrl2 α → Prop 
| R {x y a} {ha} (h : R_α a ha x y) : R_sum x y
| basel : R_sum (sum D f) (sum D g)
| baser : R_sum (sum D g) (sum D f)
| stepl {d} 
  (h₁ : R_sum (sum D f) (sum D g)) (h₁ : R_sum (sum D g) (sum D f))
  (h₂: d ∈ D) :
  R_sum (f d) (g d)
| stepr {d} 
  (h₁ : R_sum (sum D f) (sum D g)) (h₁ : R_sum (sum D g) (sum D f)) 
  (h₂: d ∈ D) :
  R_sum (g d) (f d)

lemma R_sum.symm {f g} {D : set β} (R_α : ∀a, a ∈ D → mcrl2 α → mcrl2 α → Prop) 
  (R_α_symm : ∀a ha, symmetric (R_α a ha)) :
symmetric (@R_sum α _ β f g D R_α) :=
begin
  intros x y h,
  cases h,
  { apply R_sum.R,
    apply R_α_symm,
    assumption},
  { apply R_sum.baser},
  { apply R_sum.basel},
  { apply R_sum.stepr; assumption},
  { apply R_sum.stepl; assumption}
end

lemma bisim.sum {f g : β → mcrl2 α} {D} (h : ∀a, a ∈ D → f a ≈ g a) :
sum D f ≈ sum D g :=
begin
  choose R R₁x R_bisim using h,
  apply exists.intro (R_sum R),
  apply and.intro,
  exact R_sum.basel,
  apply and.intro,
  { intros x y x' a h₁ h₂, 
    cases h₁,
    { have h : (∃y', transition y a y' ∧ option.rel (R h₁_a h₁_ha) x' y'),
      by exact bisim_lift (R_bisim h₁_a h₁_ha) h₁_h h₂,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro w,
      apply and.intro haw,
      apply option.rel.mono _ hRw,
      intros x y,
      apply R_sum.R},
    { cases h₂,
      simp [transition.sum_iff, ←exists_and_distrib_right, and_assoc],
      have h : (∃y', transition (g h₂_a') a y' ∧ option.rel (R h₂_a' h₂_ha') x' y'),
      by exact bisim_lift (R_bisim h₂_a' h₂_ha') (R₁x h₂_a' h₂_ha') h₂_h,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro w,
      apply exists.intro h₂_a',
      apply and.intro h₂_ha',
      apply and.intro haw,
      apply option.rel.mono _ hRw,
      intros x y,
      exact R_sum.R},
    { cases h₂,
      simp [transition.sum_iff, ←exists_and_distrib_right, and_assoc],
      have h : (∃y', transition (f h₂_a') a y' ∧ option.rel (R h₂_a' h₂_ha') x' y'),
      by exact bisim_lift (R_bisim h₂_a' h₂_ha') ((R_bisim h₂_a' h₂_ha').right (R₁x h₂_a' h₂_ha')) h₂_h,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro w,
      apply exists.intro h₂_a',
      apply and.intro h₂_ha',
      apply and.intro haw,
      apply option.rel.mono _ hRw,
      intros x y,
      exact R_sum.R},
    { have h : (∃y', transition (g h₁_d) a y' ∧ option.rel (R h₁_d h₁_h₂) x' y'),
      by exact bisim_lift (R_bisim h₁_d h₁_h₂) (R₁x h₁_d h₁_h₂) h₂,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro w,
      apply and.intro haw,
      apply option.rel.mono _ hRw,
      intros x y,
      exact R_sum.R},
    { have h : (∃y', transition (f h₁_d) a y' ∧ option.rel (R h₁_d h₁_h₂) x' y'),
      by exact bisim_lift (R_bisim h₁_d h₁_h₂) ((R_bisim h₁_d h₁_h₂).right (R₁x h₁_d h₁_h₂)) h₂,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro w,
      apply and.intro haw,
      apply option.rel.mono _ hRw,
      intros x y,
      exact R_sum.R}},
    { choose R_bisim R_symm using R_bisim,
      exact R_sum.symm R R_symm}
end