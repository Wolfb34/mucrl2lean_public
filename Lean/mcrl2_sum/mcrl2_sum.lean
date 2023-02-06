import .sum_axioms
import .sum
import .quot_out

variables {α : Type}
variables [comm_semigroup_with_zero_and_tau α]

namespace mcrl2

/- The class definition of mcrl2 with the summation operator. -/
class mcrl2_sum (α : Type) (M : Type 1) [comm_semigroup_with_zero_and_tau α] extends mcrl2_encap α M :=
  (sum {β : Type} : set β → (β → M) → M)
  (sum_idem {β : Type} : ∀x (D : set β), (∃d, d ∈ D) → sum D (λa, x) = x)
  (sum_elem {β : Type} : ∀(D : set β) f d, d ∈ D → sum D f = alt (sum D f) (f d))
  (sum_alt {β : Type} : ∀(D : set β) f g : β → M, sum D (λa, alt (f a) (g a)) = alt (sum D f) (sum D g))
  (sum_seq {β : Type} : ∀(D : set β) f x, seq (sum D f) x = sum D (λa, seq (f a) x))
  (sum_parl {β : Type} : ∀(D : set β) f x, parl (sum D f) x = sum D (λa, parl (f a) x))
  (sum_comm {β : Type} : ∀(D : set β) f x, comm (sum D f) x = sum D (λa, comm (f a) x))
  (comm_sum {β : Type} : ∀(D : set β) f x, comm x (sum D f) = sum D (λa, comm x (f a)))
  (encap_sum {β : Type} : ∀H (D : set β) (f : β → M), encap H (sum D f) = sum D (λa, encap H (f a)))
  (sum_ext {β : Type} : ∀(f g : β → M) D, (∀d, (d ∈ D → f d = g d)) → sum D f = sum D g)

variable {β : Type}

/- The instance of mcrl2' with the summation operator. Note that it is noncomputable, because the definition of sum uses quot.out, an operator that requires the axiom of choice. The other proofs are all given using reasoning on the equivalence relation, as opposed to using quotient induction, like the previous proofs. -/
noncomputable instance mcrl2'.sum : mcrl2_sum α (mcrl2' α) := {
  sum := (λβ D f, quotient.mk (sum D (λa, quot.out (f a)))),
  sum_idem := begin
    intros β D x h,
    simp [quotient.mk_eq_iff_out],
    exact mcrl2'.sum_idem h
  end,
  sum_elem := begin
    intros β D f d h,
    simp [quotient.mk_eq_iff_out],
    apply setoid.trans,
    exact mcrl2'.sum_elem h,
    apply setoid.symm,
    apply setoid.trans,
    exact mcrl2'.quot_alt,
    apply setoid.symm,
    apply bisim.alt,
    apply setoid.symm,
    exact quotient.mk_out _,
    exact setoid.refl _
  end,
  sum_alt := begin
    intros β D f g,
    simp [quotient.mk_eq_iff_out, quotient.eq_mk_iff_out],
    apply setoid.trans,
    { apply bisim.sum,
      intros a h,
      exact mcrl2'.quot_alt},
    { apply setoid.symm,
      apply setoid.trans,
      { apply mcrl2'.quot_alt},
      { apply setoid.trans,
        { apply bisim.alt,
          repeat {exact quotient.mk_out _}},
        { apply setoid.symm,
          apply mcrl2'.sum_alt}}}
  end,
  sum_seq := begin
    intros β D f x,
    simp [quotient.mk_eq_iff_out, quotient.eq_mk_iff_out],
    apply setoid.trans,
    { apply mcrl2'.quot_seq},
    { apply setoid.trans,
      { apply bisim.seq,
        { exact quotient.mk_out _},
        { exact setoid.refl _}},
      { apply setoid.trans,
        { apply mcrl2'.sum_seq},
        { apply setoid.symm,
          apply bisim.sum,
          intros a h,
          exact mcrl2'.quot_seq}}}
  end,
  sum_parl := begin
    intros β D f x,
    simp [quotient.mk_eq_iff_out, quotient.eq_mk_iff_out],
    apply setoid.trans,
    { apply mcrl2'.quot_parl},
    apply setoid.trans,
    { apply bisim.parl,
      { exact quotient.mk_out _},
      { exact setoid.refl _}},
    apply setoid.trans,
    { apply mcrl2'.sum_parl,},
    apply bisim.sum,
    intros a h,
    apply setoid.symm,
    apply mcrl2'.quot_parl
  end,
  sum_comm := begin
    intros β D f x,
    simp [quotient.mk_eq_iff_out, quotient.eq_mk_iff_out],
    apply setoid.trans,
    { apply mcrl2'.quot_comm},
    apply setoid.trans,
    { apply bisim.comm,
      { exact quotient.mk_out _},
      { exact setoid.refl _}},
    apply setoid.trans,
    { apply mcrl2'.sum_comm,},
    apply bisim.sum,
    intros a h,
    apply setoid.symm,
    apply mcrl2'.quot_comm
  end,
  comm_sum := begin
    intros β D f x,
    simp [quotient.mk_eq_iff_out, quotient.eq_mk_iff_out],
    apply setoid.trans,
    { apply mcrl2'.quot_comm},
    apply setoid.trans,
    { apply bisim.comm,
      { exact setoid.refl _},
      { exact quotient.mk_out _}},
    apply setoid.trans,
    { apply mcrl2'.comm_sum,},
    apply bisim.sum,
    intros a h,
    apply setoid.symm,
    apply mcrl2'.quot_comm
  end,
  encap_sum := begin
    intros β H D f,
    simp [quotient.mk_eq_iff_out, quotient.eq_mk_iff_out],
    apply setoid.trans,
    { apply mcrl2'.quot_encap},
    apply setoid.trans,
    { apply bisim.encap,
      exact quotient.mk_out _},
    apply setoid.symm,
    apply setoid.trans,
    { apply bisim.sum,
      intros a h,
      apply mcrl2'.quot_encap},
    apply setoid.symm,
    exact mcrl2'.encap_sum
  end,
  sum_ext := begin
    intros β f g D h,
    simp,
    apply mcrl2'.sum_ext,
    intros d h',
    apply (iff.elim_right quotient.out_equiv_out),
    exact h d h'
  end,
  ..mcrl2'.encap
}

end mcrl2
