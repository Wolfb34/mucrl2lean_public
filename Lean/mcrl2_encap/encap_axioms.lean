import ..mcrl2_mrg.mcrl2_mrg
import ..transition.encap

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]


/- The quotient axioms-/
lemma mcrl2.dead_encap {A : set α} : encap A δ ≈ δ :=
by exact R_add_congr (transition.encap_deadlock A)

lemma mcrl2.encap_pass {a : α} {A} (h : a ∉ A) : encap A (atom a) ≈ atom a :=
by exact R_add_congr (transition.encap_success a A h)

lemma mcrl2.encap_fail {a : α} {A} (h : a ∈ A) : encap A (atom a) ≈ δ :=
by exact R_add_congr (transition.encap_fail a A h)

lemma mcrl2.encap_alt {x y : mcrl2 α} {A} : encap A (x + y) ≈ encap A x + encap A y :=
by exact R_add_congr (transition.encap_alt x y A) 

/- encap_seq needed bisimulation, and here we show that it does hold. -/
inductive R_encap_seq {x y : mcrl2 α} {A : set α} :
mcrl2 α → mcrl2 α → Prop
| basel : R_encap_seq (encap A (x ⬝ y)) (encap A x ⬝ encap A y) 
| baser : R_encap_seq (encap A x ⬝ encap A y) (encap A (x ⬝ y))
| stepl {x' a} {z : mcrl2 α} 
  (hR₁ : R_encap_seq (encap A (x' ⬝ y))       (encap A x' ⬝ encap A y)) 
  (hR₂ : R_encap_seq (encap A x' ⬝ encap A y) (encap A (x' ⬝ y))) 
  (ht : transition x' a z) :
R_encap_seq (encap A (z ⬝ y)) (encap A z ⬝ encap A y)
| stepr {x' a} {z : mcrl2 α} 
  (hR₁ : R_encap_seq (encap A (x' ⬝ y))       (encap A x' ⬝ encap A y))
  (hR₂ : R_encap_seq (encap A x' ⬝ encap A y) (encap A (x' ⬝ y)))
  (ht : transition x' a z) :
R_encap_seq (encap A z ⬝ encap A y) (encap A (z ⬝ y))
| refl {x} : R_encap_seq x x

lemma R_encap_seq_refl {x y : mcrl2 α} {A}  : ∀z : mcrl2 α, (@R_encap_seq α _ x y A) z z := 
by intro x; exact R_encap_seq.refl

lemma R_encap_seq.symm {x y} {A} :
symmetric (@R_encap_seq α _ x y A) :=
begin
  intros x y h,
  cases h,
  { exact R_encap_seq.baser},
  { exact R_encap_seq.basel},
  { apply R_encap_seq.stepr; assumption},
  { apply R_encap_seq.stepl; assumption},
  { assumption}
end

lemma mcrl2.encap_seq {x y : mcrl2 α} {A} : encap A (x ⬝ y) ≈ encap A x ⬝ encap A y :=
begin
  apply exists.intro R_encap_seq,
  apply and.intro,
  exact R_encap_seq.basel,
  apply and.intro,
  { intros x₁ y₁ x₁' a h₁ h₂,
    cases h₁,
    { simp [transition.seq_iff, transition.encap_iff, ←exists_and_distrib_right, and_assoc, exists_eq_left, ←exists_and_distrib_right, exists_comm],
      simp [transition.seq_iff, transition.encap_iff, ←exists_and_distrib_right, and_assoc, exists_eq_left, ←exists_and_distrib_right, exists_comm] at h₂,
      rcases h₂ with ⟨w, hx₁', v, hw, hav, ha⟩,
      apply exists.intro v,
      apply and.intro hav,
      apply and.intro ha,
      simp [hx₁', hw],
      cases v,
      { simp [seq'],
        apply option.rel.some,
        exact R_encap_seq.refl},
      { apply option.rel.some,
        apply R_encap_seq.stepl,
        exact R_encap_seq.basel,
        exact R_encap_seq.baser,
        assumption}},
    { simp [transition.seq_iff, transition.encap_iff, ←exists_and_distrib_right, and_assoc, exists_eq_left, ←exists_and_distrib_right, exists_comm],
      simp [transition.seq_iff, transition.encap_iff, ←exists_and_distrib_right, and_assoc, exists_eq_left, ←exists_and_distrib_right, exists_comm] at h₂,
      rcases h₂ with ⟨w, hx₁', v, hw, hav, ha⟩,
      apply exists.intro v,
      apply and.intro hav,
      apply and.intro ha,
      simp [hx₁', hw],
      cases v,
      { simp [seq'],
        apply option.rel.some,
        exact R_encap_seq.refl},
      { apply option.rel.some,
        apply R_encap_seq.stepr,
        exact R_encap_seq.basel,
        exact R_encap_seq.baser,
        assumption}},
    { simp [transition.seq_iff, transition.encap_iff, ←exists_and_distrib_right, and_assoc, exists_eq_left, ←exists_and_distrib_right, exists_comm],
      simp [transition.seq_iff, transition.encap_iff, ←exists_and_distrib_right, and_assoc, exists_eq_left, ←exists_and_distrib_right, exists_comm] at h₂,
      rcases h₂ with ⟨w, hx₁', v, hw, hav, ha⟩,
      apply exists.intro v,
      apply and.intro hav,
      apply and.intro ha,
      simp [hx₁', hw],
      cases v,
      { simp [seq'],
        apply option.rel.some,
        exact R_encap_seq.refl},
      { apply option.rel.some,
        apply R_encap_seq.stepl,
        exact h₁,
        apply R_encap_seq.stepr; assumption,
        assumption}},
    { simp [transition.seq_iff, transition.encap_iff, ←exists_and_distrib_right, and_assoc, exists_eq_left, ←exists_and_distrib_right, exists_comm],
      simp [transition.seq_iff, transition.encap_iff, ←exists_and_distrib_right, and_assoc, exists_eq_left, ←exists_and_distrib_right, exists_comm] at h₂,
      rcases h₂ with ⟨w, hx₁', v, hw, hav, ha⟩,
      apply exists.intro v,
      apply and.intro hav,
      apply and.intro ha,
      simp [hx₁', hw],
      cases v,
      { simp [seq'],
        apply option.rel.some,
        exact R_encap_seq.refl},
      { apply option.rel.some,
        apply R_encap_seq.stepr,
        apply R_encap_seq.stepl; assumption,
        exact h₁,
        assumption}},
    { apply exists.intro x₁',
      apply and.intro h₂,
      exact option.rel.refl R_encap_seq_refl}},
  { exact R_encap_seq.symm}
end