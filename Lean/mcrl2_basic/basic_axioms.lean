import ..add
import ..transition.alt_seq

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]


/- This relation is used to prove the seq_assoc rule for the mcrl2' quotient.-/
inductive R_seq_assoc {x y z: mcrl2 α} :
mcrl2 α → mcrl2 α → Prop
| basel : R_seq_assoc (x ⬝ y ⬝ z)   (x ⬝ (y ⬝ z))
| baser : R_seq_assoc (x ⬝ (y ⬝ z)) (x ⬝ y ⬝ z)
| stepl {x a x'} (h_l : R_seq_assoc (x ⬝ y ⬝ z) (x ⬝ (y ⬝ z))) (h_r : R_seq_assoc (x ⬝ (y ⬝ z)) (x ⬝ y ⬝ z))
  (h₂ : transition x a (some x')) :
  R_seq_assoc (x' ⬝ y ⬝ z) (x' ⬝ (y ⬝ z))
| stepr {x a x'} (h_l : R_seq_assoc (x ⬝ y ⬝ z) (x ⬝ (y ⬝ z))) (h_r : R_seq_assoc (x ⬝ (y ⬝ z)) (x ⬝ y ⬝ z) )
  (h₂ : transition x a (some x')) : R_seq_assoc (x' ⬝ (y ⬝ z)) (x' ⬝ y ⬝ z)
| refl {x} : R_seq_assoc x x

lemma R_seq_assoc.symm {x y z : mcrl2 α}:
symmetric (@R_seq_assoc α _ x y z) :=
begin
  intros x₁ y₁ h,
  cases h,
  { exact R_seq_assoc.baser},
  { exact R_seq_assoc.basel},
  { apply R_seq_assoc.stepr, repeat {assumption}},
  { apply R_seq_assoc.stepl, repeat {assumption}},
  { assumption}
end

/- Here we prove the axioms for the mcrl2' quotient.-/
lemma mcrl2.alt_comm {x y : mcrl2 α} : x + y ≈ y + x :=
by exact R_add_congr (transition.alt_comm x y)

lemma mcrl2.alt_assoc {x y z : mcrl2 α} : x + (y + z) ≈ x + y + z :=
by exact R_add_congr (transition.alt_assoc x y z)

lemma mcrl2.alt_idem {x : mcrl2 α} : x + x ≈ x :=
by exact R_add_congr (transition.alt_idem x)

lemma mcrl2.alt_dist {x y z : mcrl2 α} : (x + y) ⬝ z ≈ x ⬝ z + y ⬝ z :=
by exact R_add_congr (transition.alt_dist x y z)

lemma mcrl2.seq_assoc {x y z : mcrl2 α} : (x ⬝ y) ⬝ z ≈ x ⬝ (y ⬝ z) :=
begin
  apply exists.intro R_seq_assoc,
  apply and.intro,
  exact R_seq_assoc.basel,
  apply and.intro,
  { intros x₁ y₁ x₁' a₁ h₁ h₂,
    cases h₁,
    { cases h₂,
      cases h₂_h,
      simp only [transition.seq_iff, ←exists_and_distrib_right, and_assoc, exists_comm, exists_eq_left],
      apply exists.intro h₂_h_z,
      apply and.intro,
      assumption,
      cases h₂_h_z,
      { apply option.rel.some,
        exact R_seq_assoc.refl},
      { apply option.rel.some,
        apply R_seq_assoc.stepl,
        exact h₁,
        exact R_seq_assoc.baser,
        assumption}},
    { cases h₂,
      simp only [transition.seq_iff, ←exists_and_distrib_right, and_assoc, exists_comm, exists_eq_left],
      cases h₂_z,
      { apply exists.intro none,
        apply and.intro,
        assumption,
        apply option.rel.some,
        exact R_seq_assoc.refl},
      { apply exists.intro (some h₂_z),
        apply and.intro,
        assumption,
        apply option.rel.some,
        apply R_seq_assoc.stepr,
        exact R_seq_assoc.basel,
        repeat {assumption}}},
    { cases h₂,
      simp only [transition.seq_iff, ←exists_and_distrib_right, and_assoc, exists_comm, exists_eq_left],
      cases h₂_h,
      apply exists.intro h₂_h_z,
      apply and.intro,
      assumption,
      cases h₂_h_z,
      { apply option.rel.some,
        exact R_seq_assoc.refl},
      { apply option.rel.some,
        apply R_seq_assoc.stepl,
        exact h₁,
        apply R_seq_assoc.stepr,
        exact h₁_h_l,
        repeat {assumption}}},
    { cases h₂,
      simp only [transition.seq_iff, ←exists_and_distrib_right, and_assoc, exists_comm, exists_eq_left],
      apply exists.intro h₂_z,
      apply and.intro,
      assumption,
      cases h₂_z,
      { apply option.rel.some,
        exact R_seq_assoc.refl},
      { apply option.rel.some,
        apply R_seq_assoc.stepr,
        apply R_seq_assoc.stepl,
        exact h₁_h_l,
        repeat {assumption}}},
    { apply exists.intro x₁',
      apply and.intro,
      assumption,
      cases x₁',
      exact option.rel.none,
      apply option.rel.some,
      exact R_seq_assoc.refl}},
  { exact R_seq_assoc.symm}
end