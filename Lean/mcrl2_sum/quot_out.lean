import ..mcrl2_encap.mcrl2_encap

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]
variable {β : Type}

/- Lemmas used to reason on the quotient. Necessary for the proofs of the axioms. -/

lemma mcrl2'.quot_alt {x y : mcrl2' α} :
quot.out (mcrl2'.base.alt x y) ≈ (quot.out x) + (quot.out y) :=
begin
  apply quot.induction_on₂ x y,
  intros a b,
  simp [mcrl2_base.alt, quotient.lift₂, quotient.lift],
  have h : quot.out ⟦a + b⟧ ≈ a + b := by exact quotient.mk_out (a + b),
  have h' : (quot.mk setoid.r a).out ≈ a := by exact quotient.mk_out _,
  have h'' : (quot.mk setoid.r b).out ≈ b := by exact quotient.mk_out _,
  apply setoid.trans,
  exact h,
  apply bisim.alt,
  repeat {apply setoid.symm; assumption}
end

lemma mcrl2'.quot_seq {x y : mcrl2' α} :
quot.out (mcrl2'.base.seq x y) ≈ (quot.out x) ⬝ (quot.out y) :=
begin
  apply quot.induction_on₂ x y,
  intros a b,
  simp [mcrl2_base.seq, quotient.lift₂, quotient.lift],
  apply setoid.trans,
  exact quotient.mk_out _,
  apply bisim.seq,
  repeat {apply setoid.symm; exact quotient.mk_out _}
end

lemma mcrl2'.quot_parl {x y : mcrl2' α} :
quot.out (mcrl2'.mrg.parl x y) ≈ (quot.out x) |_ (quot.out y) :=
begin
  apply quot.induction_on₂ x y,
  intros a b,
  simp [mcrl2_mrg.parl, quotient.lift₂, quotient.lift],
  apply setoid.trans,
  exact quotient.mk_out _,
  apply bisim.parl,
  repeat {apply setoid.symm; exact quotient.mk_out _}
end

lemma mcrl2'.quot_par {x y : mcrl2' α} :
quot.out (mcrl2'.mrg.par x y) ≈ (quot.out x) || (quot.out y) :=
begin
  apply quot.induction_on₂ x y,
  intros a b,
  simp [mcrl2_mrg.par, quotient.lift₂, quotient.lift],
  apply setoid.trans,
  exact quotient.mk_out _,
  apply bisim.par,
  repeat {apply setoid.symm; exact quotient.mk_out _}
end

lemma mcrl2'.quot_comm {x y : mcrl2' α} :
quot.out (mcrl2'.mrg.comm x y) ≈ (quot.out x) ∣ (quot.out y) :=
begin
  apply quot.induction_on₂ x y,
  intros a b,
  simp [mcrl2_mrg.comm, quotient.lift₂, quotient.lift],
  apply setoid.trans,
  exact quotient.mk_out _,
  apply bisim.comm,
  repeat {apply setoid.symm; exact quotient.mk_out _}
end

lemma mcrl2'.quot_encap {x  : mcrl2' α} {H : set α} :
quot.out (mcrl2'.encap.encap H x) ≈ encap H (x.out) :=
begin
  apply quot.induction_on x ,
  intro b,
  simp [mcrl2_encap.encap, quotient.lift],
  apply setoid.trans,
  exact quotient.mk_out _,
  apply bisim.encap,
  apply setoid.symm,
  exact quotient.mk_out _
end