import ..mcrl2_basic.mcrl2_basic
import ..transition.par_comm
import ..add

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]

/- This is where the axioms are proved for the quotient.-/

lemma mcrl2.dead_alt {x : mcrl2 α} : x + δ ≈ x :=
by exact R_add_congr (transition.alt_deadlock x)

lemma mcrl2.dead_seq {x : mcrl2 α} : δ ⬝ x ≈ δ :=
by exact R_add_congr (transition.seq_deadlock x)

lemma mcrl2.dead_parl {x : mcrl2 α} : δ |_ x ≈ δ :=
by exact R_add_congr (transition.parl_deadlock x)

lemma mcrl2.dead_comml {x : mcrl2 α} : δ ∣ x ≈ δ :=
by exact R_add_congr  (transition.comm_deadlockl x) 

lemma mcrl2.dead_commr {x : mcrl2 α} : x ∣ δ ≈ δ :=
by exact R_add_congr (transition.comm_deadlockr x)

inductive R_add_par {x y : mcrl2 α} :
mcrl2 α → mcrl2 α → Prop
| basel : R_add_par x y
| baser : R_add_par y x
| par {a b} : R_add_par (a || b) (b || a) 
| refl {a} : R_add_par a a 

lemma R_add_par.symm {x y : mcrl2 α} : 
symmetric (@R_add_par α _ x y) :=
begin
  intros x₁ y₁ h,
  cases h,
  { exact R_add_par.baser},
  { exact R_add_par.basel},
  { exact R_add_par.par},
  { assumption}
end

lemma R_add_par_refl {x y} : ∀x₁, (@R_add_par α _ x y) x₁ x₁ := by intro x₁; exact R_add_par.refl

lemma R_add_par.lift_rel  {x y} {x₁ y₁ : option (mcrl2 α)} :
option.rel (@R_add_par α _ x y) (par' x₁ y₁) (par'  y₁ x₁) :=
begin
  cases x₁,
  { cases y₁,
    { apply option.rel.none},
    { apply option.rel.some, exact R_add_par.refl}},
  { cases y₁,
    { apply option.rel.some, exact R_add_par.refl},
    { apply option.rel.some, exact R_add_par.par}}
end

lemma mcrl2.par_def {x y : mcrl2 α} : x || y ≈ x |_ y + y |_ x + x ∣ y :=
begin
  apply exists.intro R_add_par,
  apply and.intro,
  exact R_add_par.basel,
  apply and.intro,
  { intros x₁ y₁ x₁' a₁ h₁ h₂,
    cases h₁,
    { cases h₂,
      { apply exists.intro (par' h₂_x' (some y)),
        apply and.intro,
        { apply transition.altl,
          apply transition.altl,
          apply transition.parl,
          assumption},
        { cases h₂_x',
          { apply option.rel.some, exact R_add_par.refl},
          { apply option.rel.some, exact R_add_par.refl}}},
      { apply exists.intro (par' h₂_y' (some x)),
        apply and.intro,
        { apply transition.altl,
          apply transition.altr,
          apply transition.parl,
          assumption},
        { cases h₂_y',
          { apply option.rel.some, exact R_add_par.refl},
          { apply option.rel.some, exact R_add_par.par}}},
      { apply exists.intro (par' h₂_x' h₂_y'),
        apply and.intro,
        { apply transition.altr,
          apply transition.comm; assumption},
        { cases h₂_x',
          { cases h₂_y',
            { apply option.rel.none},
            { apply option.rel.some, exact R_add_par.refl}},
          { cases h₂_y',
            { apply option.rel.some, exact R_add_par.refl},
            { apply option.rel.some, exact R_add_par.refl}}}}},
    { cases h₂,
      { cases h₂_h,
        { cases h₂_h_h,
          apply exists.intro (par' h₂_h_h_x' (some y)),
          apply and.intro,
          { apply transition.par_l; assumption},
          { cases h₂_h_h_x',
            { apply option.rel.some, exact R_add_par.refl},
            { apply option.rel.some, exact R_add_par.refl}}},
        { cases h₂_h_h,
          apply exists.intro (par' (some x) h₂_h_h_x'),
          apply and.intro,
          { apply transition.par_r; assumption},
          { cases h₂_h_h_x',
            { apply option.rel.some, exact R_add_par.refl},
            { apply option.rel.some, exact R_add_par.par}}}},
      { cases h₂_h,
        apply exists.intro (par' h₂_h_x' h₂_h_y'),
        apply and.intro,
        { apply transition.par_comm; assumption},
        { cases h₂_h_x',
          { cases h₂_h_y',
            { apply option.rel.none},
            { apply option.rel.some, exact R_add_par.refl}},
          { cases h₂_h_y',
            { apply option.rel.some, exact R_add_par.refl},
            { apply option.rel.some, exact R_add_par.refl}}}}},
    { cases h₂,
      { apply exists.intro (par' (some h₁_b) h₂_x'),
        apply and.intro,
        { apply transition.par_r; assumption},
        { exact R_add_par.lift_rel}},
      { apply exists.intro (par' h₂_y' (some h₁_a)),
        apply and.intro,
        { apply transition.par_l; assumption},
        { exact R_add_par.lift_rel}},
      { apply exists.intro (par' h₂_y' h₂_x'),
        apply and.intro,
        { change comm_semigroup_with_zero.mul h₂_a h₂_b with h₂_a * h₂_b,
          rw mul_comm at *, apply transition.par_comm; assumption},
        { exact R_add_par.lift_rel}}},
    { apply exists.intro x₁',
      apply and.intro h₂,
      cases x₁',
      exact option.rel.none,
      apply option.rel.some,
      exact R_add_par.refl}},
  { exact R_add_par.symm}
end

lemma mcrl2.parl_seq_atom {a : α} {x : mcrl2 α} : (atom a) |_ x ≈ (atom a) ⬝ x :=
by exact R_add_congr (transition.parl_seq_atom a x)

lemma mcrl2.parl_seq {a : α} {x y} : (atom a) ⬝ x |_ y ≈ (atom a) ⬝ (x || y) :=
begin
  apply exists.intro R_add,
  apply and.intro R_add.basel,
  apply and.intro,
  { intros x₁ y₁ x₁' a₁ h₁ h₂,
    cases h₁,
    { cases h₂,
      cases h₂_h,
      cases h₂_h_h,
      apply exists.intro (par' ↑x ↑y),
      apply and.intro,
      { simp [transition.seq_iff], 
        apply exists.intro none,
        apply and.intro rfl h₂_h_h},
      { apply option.rel.some, exact R_add.refl}},
    { cases h₂,
      cases h₂_h,
      apply exists.intro (some (x || y)),
      apply and.intro,
      { simp [transition.parl_iff],
        apply exists.intro (some x),
        apply and.intro rfl,
        simp [transition.seq_iff],
        apply exists.intro none,
        apply and.intro rfl h₂_h},
      { apply option.rel.some, exact R_add.refl}},
    { apply exists.intro x₁',
      apply and.intro h₂,
      cases x₁',
      exact option.rel.none,
      apply option.rel.some,
      exact R_add.refl}},
  { exact R_add.symm}
end

lemma mcrl2.parl_alt {x y z : mcrl2 α} : (x + y) |_ z ≈ x |_ z + y |_ z :=
by exact R_add_congr (transition.parl_alt x y z)

lemma mcrl2.comm_success {a b c : α} (h : a * b = c) : ((atom a) ∣ (atom b)) ≈ atom c :=
by exact R_add_congr (transition.comm_success a b c h)

lemma mcrl2.comm_fail {a b : α} (h : a * b = 0) : ((atom a) ∣ (atom b)) ≈ δ :=
by exact R_add_congr (transition.comm_fail a b h)

lemma mcrl2.comm_seq_distl {a b : α} {x : mcrl2 α} : (atom a ⬝ x) ∣ (atom b) ≈ ((atom a) ∣ (atom b)) ⬝ x :=
by exact R_add_congr (transition.comm_seq_distl a b x)

lemma mcrl2.comm_seq_distr {a b : α} {x : mcrl2 α} : (atom a) ∣ (atom b ⬝ x) ≈ ((atom a) ∣ (atom b)) ⬝ x :=
by exact R_add_congr (transition.comm_seq_distr a b x)

lemma mcrl2.comm_seq_dist {a b : α} {x y : mcrl2 α} : (atom a ⬝ x) ∣ (atom b ⬝ y) ≈ (atom a ∣ atom b) ⬝ (x || y) := 
by exact R_add_congr (transition.comm_seq_dist a b x y)

lemma mcrl2.comm_alt_distl {x y z : mcrl2 α} : ((x + y) ∣ z) ≈ x ∣ z + y ∣ z :=
by exact R_add_congr (transition.comm_alt_distl x y z)

lemma mcrl2.comm_alt_distr {x y z : mcrl2 α} : (x ∣ (y + z)) ≈ x ∣ y + x ∣ z :=
by exact R_add_congr (transition.comm_alt_distr x y z)