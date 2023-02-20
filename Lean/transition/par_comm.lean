/- This file includes proofs of the axioms for the 3 parallel operators ||, |_ and |. This also includes some axioms for the deadlock operator. -/
import .iff_lemmas

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]


/- parl_def ((x || y) = x |_ y + y |_ x + x | y) needs to be proved via bisimulation-/

lemma transition.parl_seq_atom (a₁) (x : mcrl2 α) (x' : option (mcrl2 α)) (a₂)  :
transition ((atom a₁) |_ x) a₂ x' ↔ transition ((atom a₁) ⬝ x) a₂ x' :=
begin
  simp [transition.parl_iff, transition.atom_iff, transition.seq_iff, and_rotate, exists_eq_left]
end

/- parl_seq  (((atom a ⬝ x) |_ y) = (atom a) ⬝ (x || y)) needs to be proved via bisimulation.-/

lemma transition.parl_alt (x y z : mcrl2 α) (x' : option (mcrl2 α)) (a) :
  transition ((x + y) |_ z) a x' ↔ transition (x |_ z + y |_ z) a x' :=
begin
  simp only [transition.alt_iff, transition.parl_iff, and_or_distrib_left, exists_or_distrib]
end

lemma transition.comm_success (a b c : α) (h₁ : a * b = c)  (x' : option (mcrl2 α)) (d):
transition ((atom a) ∣ (atom b)) d x' ↔ transition (atom c) d x' :=
begin
  simp only [transition.comm_iff, transition.atom_iff, ← h₁, exists_and_distrib_left,
      exists_and_distrib_right, ← and_assoc, @eq_comm _ b, exists_eq_right, par'],
  split,
  { intro h,
    cases h with h hb,
    cases h with h ha,
    cases h with h hd,
    cases h with hx' hdab,
    apply and.intro,
    { apply and.intro hx',
      rw ← hdab,
      assumption},
    {assumption}},
  { intro h,
    cases h with h hdab,
    cases h with hx' hab,
    repeat {apply and.intro},
    assumption,
    assumption,
    { rw hdab,
      assumption},
    { intro h,
      rw h at hab,
      exact hab (zero_mul b)},
    { intro h,
      rw h at hab,
      exact hab (mul_zero a)}}
end

lemma transition.comm_fail (a b : α) (h₁ : a * b = 0)  (x' : option (mcrl2 α)) (d) :
transition ((atom a) ∣ (atom b)) d x' ↔ transition δ d x' :=
begin
  simp [transition.deadlock_iff, transition.comm_iff, transition.atom_iff],
  intros x y hx' a' b' hd hnd hx ha ha' hy hb hb',
  simp [hd, ha', hb'] at hnd,
  exact hnd h₁
end

lemma transition.comm_seq_distl (a b : α) (x : mcrl2 α) (x' : option (mcrl2 α)) (c) :
transition ((atom a) ⬝ x ∣ (atom b)) c x' ↔ transition ((atom a ∣ atom b)⬝ x) c x' :=
begin
  simp [transition.comm_iff, transition.seq_iff, transition.atom_iff, ← and_assoc]
end

lemma transition.comm_seq_distr (a b : α) (x : mcrl2 α) (x' : option (mcrl2 α)) (c) :
transition ((atom a) ∣ (atom b) ⬝ x) c x' ↔ transition ((atom a ∣ atom b)⬝ x) c x' :=
begin
  simp [transition.comm_iff, transition.seq_iff, transition.atom_iff, ← and_assoc]
end

lemma transition.comm_seq_dist (a b : α) (x y : mcrl2 α) (x' : option (mcrl2 α)) (c) :
transition ((atom a) ⬝ x ∣ (atom b) ⬝ y) c x' ↔ transition ((atom a ∣ atom b)⬝ (x || y)) c x' :=
begin
  simp [transition.comm_iff, transition.seq_iff, transition.atom_iff, ← and_assoc]
end

lemma transition.comm_alt_distl  (x y z : mcrl2 α) (x' : option (mcrl2 α)) (a):
transition ((x + y) ∣ z) a x' ↔ transition (x ∣z + y ∣ z) a x' :=
begin
  simp [transition.alt_iff, transition.comm_iff, ← and_assoc, exists_or_distrib, or_and_distrib_right, and_or_distrib_left]
end

lemma transition.comm_alt_distr (x y z : mcrl2 α) (x' : option (mcrl2 α)) (a)  :
transition (x ∣ (y + z)) a x' ↔ transition (x ∣ y + x ∣ z) a x' :=
begin
  simp [transition.alt_iff, transition.comm_iff, ← and_assoc, exists_or_distrib, or_and_distrib_right, and_or_distrib_left]
end

lemma transition.alt_deadlock  (x : mcrl2 α) (z) (a) :
transition (x + δ) a z ↔ transition x a z :=
begin
  simp [transition.alt_iff, transition.deadlock_iff]
end

lemma transition.seq_deadlock (x : mcrl2 α) (z) (a):
transition (δ ⬝ x) a z ↔ transition δ a z :=
begin
  simp [transition.seq_iff, transition.deadlock_iff]
end

lemma transition.parl_deadlock (x: mcrl2 α) (z) (a) :
transition (δ |_ x) a z ↔ transition (δ : mcrl2 α) a z :=
begin
  simp [transition.parl_iff, transition.deadlock_iff]
end

lemma transition.comm_deadlockl (x z) (a) :
transition ((δ : mcrl2 α) ∣ x) a z ↔ transition (δ : mcrl2 α) a z :=
begin
  simp [transition.comm_iff, transition.deadlock_iff]
end

lemma transition.comm_deadlockr (x z) (a) :
transition (x ∣ (δ : mcrl2 α)) a z ↔ transition (δ : mcrl2 α) a z :=
begin
  simp [transition.comm_iff, transition.deadlock_iff]
end