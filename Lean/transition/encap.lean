import .iff_lemmas

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]

/- Next are the equations on the encapsulation operator.-/
lemma transition.encap_deadlock (A z) (a : α):
transition (encap A (δ : mcrl2 α)) a z ↔ transition (δ : mcrl2 α) a z :=
begin
  simp [transition.encap_iff, transition.deadlock_iff],
end

lemma transition.encap_success (a₁ : α) (A) (h : a₁ ∉ A) (z a₂) :
transition (encap A (atom a₁)) a₂ z ↔ transition (atom a₁) a₂ z :=
begin
  simp [transition.encap_iff, transition.atom_iff, h, ←and_assoc, h],
  intros _ _ h,
  rw h,
  assumption
end

lemma transition.encap_fail (a₁ : α) (A) (h : a₁ ∈ A) (z a₂) :
transition (encap A (atom a₁)) a₂ z ↔ transition δ a₂ z :=
begin
  simp [transition.deadlock_iff, transition.encap_iff, transition.atom_iff, h],
  intros _ _ _ _ h,
  rw h,
  assumption
end

lemma transition.encap_alt (x : mcrl2 α) (y A z) (a : α) :
transition (encap A (x + y)) a z ↔ transition ((encap A x) + (encap A y)) a z:=
begin
  simp [transition.encap_iff, transition.alt_iff, ←exists_and_distrib_right, and_or_distrib_left, or_and_distrib_right, exists_or_distrib]
end

/- encap_seq (∂_H(x ⬝ y) = ∂_H(x) ⬝ ∂_H(y)) needs to be proved via bisimulation. -/