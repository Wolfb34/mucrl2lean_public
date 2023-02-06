import .quotient

open mcrl2
variable {α : Type}
variable [comm_semigroup_with_zero α]

/- This relation is used to prove many of the axioms for the quotient.-/
inductive R_add {x y : mcrl2 α} :
mcrl2 α → mcrl2 α → Prop
| basel : R_add x y
| baser : R_add y x
| refl {a} : R_add a a

lemma R_add.symm {x y : mcrl2 α} :
symmetric (@R_add α _ x y) :=
begin
  intros x₁ y₁ h,
  cases h,
  { exact R_add.baser},
  { exact R_add.basel},
  { assumption}
end

lemma R_add_refl {x y} : ∀x₁, (@R_add α _ x y) x₁ x₁ := by intro x₁; exact R_add.refl

lemma R_add_congr {x y : mcrl2 α} (h : ∀z a, (transition x a z) ↔ (transition y a z)) :
x ≈ y :=
begin
  apply exists.intro R_add,
  apply and.intro R_add.basel,
  apply and.intro,
  { intros x₁ y₁ x₁' a h₁ h₂,
    apply exists.intro x₁',
    cases h₁,
    { rw ←h,
      apply and.intro h₂,
      exact option.rel.refl R_add_refl},
    { rw h,
      apply and.intro h₂,
      exact option.rel.refl R_add_refl},
    { apply and.intro h₂,
      exact option.rel.refl R_add_refl}},
  { exact R_add.symm}
end