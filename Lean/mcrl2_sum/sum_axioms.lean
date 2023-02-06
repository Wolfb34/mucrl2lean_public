import ..mcrl2_encap.mcrl2_encap
import ..transition.sum

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]
variable {β : Type}

/- The proofs of the mcrl2 axioms for the quotient. -/
lemma mcrl2'.sum_idem {x : mcrl2 α} {D : set β} (h : ∃d, d ∈ D) :
sum D (λa, x) ≈ x := by exact R_add_congr (transition.sum_idem D h x)

lemma mcrl2'.sum_elem {f : β → mcrl2 α} {D : set β} {d} (h : d ∈ D) :
sum D f ≈ sum D f + f d := by exact R_add_congr (transition.sum_elem D f d h)

lemma mcrl2'.sum_alt  {f g : β → mcrl2 α} {D : set β} :
sum D (λa, f a + g a) ≈ sum D f + sum D g := by exact R_add_congr (transition.sum_alt D f g)

lemma mcrl2'.sum_seq {f : β → mcrl2 α} {x D} :
sum D f ⬝ x ≈ sum D (λa, f a ⬝ x) := by exact R_add_congr (transition.sum_seq D f x)

lemma mcrl2'.sum_parl {f : β → mcrl2 α} {x D} :
sum D f |_ x ≈ sum D (λa, f a |_ x) := by exact R_add_congr (transition.sum_parl D f x)

lemma mcrl2'.sum_comm {f : β → mcrl2 α} {x D} :
sum D f ∣ x ≈ sum D (λa, f a ∣ x) := by exact R_add_congr (transition.sum_comm D f x)

lemma mcrl2'.comm_sum {f : β → mcrl2 α} {x D} :
x ∣ sum D f  ≈ sum D (λa, x ∣ f a) := by exact R_add_congr (transition.comm_sum D f x)

lemma mcrl2'.encap_sum {f : β → mcrl2 α} {H D} :
encap H (sum D f) ≈ sum D (λa, encap H (f a)) := by exact R_add_congr (transition.encap_sum H D f)

inductive R_sum_ext {f g : β → mcrl2 α} {D : set β} (R_α : ∀a, a ∈ D → mcrl2 α → mcrl2 α → Prop) :
mcrl2 α → mcrl2 α → Prop
| R {x y a ha} (h : R_α a ha x y) : R_sum_ext x y
| basel : R_sum_ext (sum D f) (sum D g)
| baser : R_sum_ext (sum D g) (sum D f)
| refl {x} : R_sum_ext x x

lemma R_sum_ext_refl  {f g : β → mcrl2 α} {D : set β} (R_α : ∀a, a ∈ D → mcrl2 α → mcrl2 α → Prop) :
reflexive (@R_sum_ext α _ β f g D R_α) :=
begin
  intro x,
  apply R_sum_ext.refl
end

lemma R_sum_ext.symm  {f g : β → mcrl2 α} {D : set β} (R_α : ∀a, a ∈ D → mcrl2 α → mcrl2 α → Prop) 
(R_α_symm : ∀a ha, symmetric (R_α a ha)) :
symmetric (@R_sum_ext α _ β f g D R_α) :=
begin
  intros x y h,
  cases h,
  { apply R_sum_ext.R,
    apply R_α_symm _ _,
    assumption},
  { exact R_sum_ext.baser},
  { exact R_sum_ext.basel},
  { assumption}
end

lemma mcrl2'.sum_ext {f g : β → mcrl2 α} {D : set β} (h : ∀d, d ∈ D → f d ≈ g d) :
sum D f ≈ sum D g :=
begin
  choose R R₁x R_bisim using h,
  apply exists.intro (R_sum_ext R),
  apply and.intro,
  exact R_sum_ext.basel,
  apply and.intro,
  { intros x y x' a h₁ h₂,
    cases h₁,
    { have h : ∃y', transition y a y' ∧ option.rel (R h₁_a h₁_ha) x' y',
      by exact bisim_lift (R_bisim _ _) h₁_h h₂,
      rcases h with ⟨w, haw, hRw⟩,
      apply exists.intro w,
      apply and.intro haw,
      apply option.rel.mono _ hRw,
      intros x y,
      exact R_sum_ext.R},
    { cases h₂,
      simp [transition.sum_iff, ← exists_and_distrib_right, and_assoc],
      have h : ∃y', transition (g h₂_a') a y' ∧ option.rel (R h₂_a' h₂_ha') x' y',
      by exact bisim_lift (R_bisim _ _) (R₁x _ _) h₂_h,
      rcases h with ⟨w, haw, hRw⟩,
      exact ⟨w, h₂_a', h₂_ha', haw, begin
        apply option.rel.mono _ hRw,
        intros x y,
        exact R_sum_ext.R
      end⟩},
    { cases h₂,
      simp [transition.sum_iff, ← exists_and_distrib_right, and_assoc],
      have h : ∃y', transition (f h₂_a') a y' ∧ option.rel (R h₂_a' h₂_ha') x' y',
      by exact bisim_lift (R_bisim _ _) ((R_bisim _ _).right (R₁x _ _)) h₂_h,
      rcases h with ⟨w, haw, hRw⟩,
      exact ⟨w, h₂_a', h₂_ha', haw, begin
        apply option.rel.mono _ hRw,
        intros x y,
        exact R_sum_ext.R
      end⟩},
    { exact ⟨x', h₂, by exact option.rel.refl (R_sum_ext_refl R)⟩}},
  { choose R_bisim R_symm using R_bisim,
    exact R_sum_ext.symm R R_symm}
end