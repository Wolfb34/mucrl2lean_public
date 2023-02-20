/- This file includes the proofs of the axioms for the alternative and sequential composition. -/
import .iff_lemmas

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]



lemma transition.alt_comm (x y: mcrl2 α) (x' : option (mcrl2 α)) (a) :
  transition (x + y) a x' ↔ transition (y + x) a x' :=
begin
  simp only [transition.alt_iff, or_comm]
end

lemma transition.alt_idem (x : mcrl2 α) (y : option (mcrl2 α)) (a) :
transition (x + x) a y ↔ transition x a y :=
begin
  simp only [transition.alt_iff, or_self]
end

lemma transition.alt_assoc (x y z: mcrl2 α) (x' : option (mcrl2 α)) (a) :
transition (x + (y + z)) a x' ↔ transition ((x + y) + z) a x' :=
begin
  simp only [transition.alt_iff, or_assoc]
end

lemma transition.alt_dist (x y z : mcrl2 α) (x' : option (mcrl2 α)) (a) :
transition ((x + y) ⬝ z) a x' ↔ transition ((x⬝ z) + (y ⬝ z)) a x' :=
begin
  simp only [transition.alt_iff, transition.seq_iff, and_or_distrib_left, exists_or_distrib]
end

/- No seq_assoc here because we have to prove it via bisimulation. -/
