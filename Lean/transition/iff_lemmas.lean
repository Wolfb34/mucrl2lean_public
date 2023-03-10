/- This file defines all the iff-lemmas. These are used to lift transitions into Lean's logic.-/
import tactic
import tactic.induction
import data.option.basic
import .transition


open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]


lemma transition.atom_iff (a b : α) (z) : transition (atom a) b z ↔ z = none ∧ (a ≠ 0) ∧ b = a :=
begin
  split,
  { intro h,
    cases h,
    exact ⟨rfl, h_h, rfl⟩ },
  { rintro ⟨rfl, h, rfl⟩,
    exact transition.atom h}
end

lemma transition.alt_iff (x y : mcrl2 α) (a z) : transition (x + y) a z ↔ transition x a z ∨ transition y a z :=
begin
  split,
  { rintro (h | h),
    { left, assumption },
    { right, assumption } },
  { rintro (h | h),
    { exact transition.altl h },
    { exact transition.altr h } }
end

lemma transition.seq_iff (x y : mcrl2 α) (a : α) (z) : transition (x ⬝ y) a z ↔ (∃ x', z = seq' x' y ∧ transition x a x') :=
begin
  split,
  { rintro (h | _),
    exact ⟨_, rfl, by assumption⟩ },
  { rintro ⟨x', rfl, h⟩,
    exact transition.seq h }
end

lemma transition.parl_iff (x y : mcrl2 α) (a z) : transition (x |_ y) a z ↔ (∃ x', z = par' x' y ∧ transition x a x') :=
begin
  split,
  { rintro (h | _),
    exact ⟨_, rfl, by assumption⟩ },
  { rintro (⟨x', rfl, h⟩),
    exact transition.parl h  }
end

/- This states that x || y has a transition if you can execute from x, from y, or a communication between x and y.-/
lemma transition.par_iff (x y : mcrl2 α) (a z) : transition (x || y) a z ↔
  (∃ x', z = par' x' y ∧ transition x a x') ∨
  (∃ y', z = par' x y' ∧ transition y a y') ∨
  (∃ x' y', z = par' x' y' ∧ ∃ a' b', a ≠ 0 ∧ a = a' * b' ∧ transition x a' x' ∧ transition y b' y') :=
begin
  split,
  { intro h, cases h,
    { exact or.inl ⟨h_x', rfl, (by assumption)⟩ },
    { exact or.inr (or.inl ⟨h_y', rfl, (by assumption)⟩) },
    { exact or.inr (or.inr ⟨h_x', h_y', rfl, h_a, h_b, h_h₃, rfl, h_h₁, h_h₂⟩)}},
  { rintro (⟨x', rfl, h⟩ | ⟨y', rfl, h⟩ | ⟨x', y', rfl, a', b', ha, rfl, hx, hy⟩),
    { exact transition.par_l h },
    { exact transition.par_r h },
    { exact transition.par_comm hx hy ha } }
end

lemma transition.comm_iff (x y : mcrl2 α) (a z) : transition (x ∣ y) a z ↔
  (∃ x' y', z = par' x' y' ∧ ∃ a' b', a = a' * b' ∧ a ≠ 0 ∧ transition x a' x' ∧ transition y b' y') :=
begin
  split,
  { intro h,
    cases h,
    exact ⟨h_x', h_y', rfl, h_a, h_b, rfl, (by assumption), (by assumption), (by assumption)⟩ },
  { rintro ⟨x', y', rfl, a', b', rfl, ha, hx, hy⟩,
    { exact transition.comm hx hy ha} }
end

lemma transition.no_zero {x : mcrl2 α} {z: option (mcrl2 α)} : ¬transition x 0 z :=
begin
  intro h,
  induction' h ; try { assumption },
  repeat {contradiction}
end

lemma transition.encap_iff (x : mcrl2 α) (a : α) (y A) : transition (encap A x) a y ↔
(∃ y', y = encap A <$> y' ∧ (transition x a y')) ∧ a ∉ A :=
begin
  apply iff.intro,
  { intro h,
    cases h,
    cases h_y,
    { apply and.intro,
      apply exists.intro none,
      simp,
      repeat {assumption}},
    { apply and.intro,
      apply exists.intro (some h_y),
      simp,
      repeat {assumption}}},
  { intro h,
    cases h with l r,
    rcases l with ⟨w, h_w₁, h_w₂⟩,
    rw h_w₁,
    apply transition.encap_pass; assumption}
end

lemma transition.deadlock_iff (a z) :
transition (δ : mcrl2 α) a z ↔ false :=
begin
  simp,
  intro h,
  cases h
end

lemma transition.sum_iff (β : Type) (A : set β) (f : β → mcrl2 α) ( a z) :
transition (sum A f) a z ↔ (∃a': β, a' ∈ A ∧ transition (f a') a z) :=
begin
  split,
  { intro h,
    cases h,
    exact ⟨h_a', h_ha', h_h⟩},
  { intro h,
    rcases h with ⟨a', ha', h⟩,
    apply transition.sum; assumption}
end