import .iff_lemmas

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero α]

/- Now we start on axioms for the summation operator.-/
variable {β : Type}

/- Note the presence of the hypothesis h here. -/
lemma transition.sum_idem (A : set β) (h : ∃a, a ∈ A) (x : mcrl2 α) (z a) :
transition (sum A (λa, x)) a z ↔ transition x a z :=
begin
  simp only [transition.sum_iff],
  split,
  { intro h',
    rcases h' with ⟨_, _, h'⟩,
    assumption},
  { intro h',
    cases h,
    exact ⟨h_w, h_h, h'⟩}
end

lemma transition.sum_elem (A : set β)  (f : β → mcrl2 α) (d) (h : d ∈ A) (z a) :
transition (sum A f) a z ↔ transition (sum A f + f d) a z :=
begin
  simp [transition.sum_iff, transition.alt_iff],
  split,
  { intro h,
    apply or.inl,
    assumption},
  { intro h',
    rcases h' with ⟨a', ha', haz⟩ | ⟨haz⟩,
    { exact ⟨a', ha', haz⟩},
    { exact ⟨d, h, haz⟩}}
end

lemma transition.sum_pure (A : set β) (f : β → mcrl2 α) (z a) :
transition (sum A (λa, f a)) a z ↔ transition (sum A f) a z :=
begin
  simp [transition.sum_iff]
end

lemma transition.sum_alt (A : set β) (f g : β → mcrl2 α) (z a) :
transition (sum A (λa, f a + g a)) a z ↔ transition (sum A f + sum A g) a z :=
by simp [transition.sum_iff, transition.alt_iff, and_or_distrib_left, ←exists_or_distrib]


lemma transition.sum_seq (A : set β) (f : β → mcrl2 α) (x z a) :
transition (sum A f ⬝ x) a z ↔ transition (sum A (λa, f a ⬝ x)) a z :=
begin simp [transition.sum_iff, transition.seq_iff, ←exists_and_distrib_left], tauto
end

lemma transition.sum_parl (A : set β) (f : β → mcrl2 α) (x z a) :
transition (sum A f |_ x) a z ↔ transition (sum A (λa, f a |_ x)) a z :=
by simp [transition.sum_iff, transition.parl_iff, ←exists_and_distrib_left, ←and_assoc, and_comm, exists_comm]

lemma transition.sum_comm (A : set β) (f : β → mcrl2 α) (x z a) :
transition (sum A f ∣ x) a z ↔ transition (sum A (λa, f a ∣ x)) a z :=
begin
  simp [transition.sum_iff, transition.comm_iff, ←exists_and_distrib_left, ←and_assoc, ←exists_and_distrib_right],
  tauto
end

lemma transition.comm_sum (A : set β) (f : β → mcrl2 α) (x z a) :
transition (x ∣ (sum A f)) a z ↔ transition (sum A (λa, x ∣ f a)) a z :=
begin
  simp [transition.sum_iff, transition.comm_iff, ←exists_and_distrib_left, ←and_assoc, ←exists_and_distrib_right],
  tauto
end

lemma transition.encap_sum (H : set α) (D : set β) (f z a) :
transition (encap H (sum D f)) a z ↔ transition (sum D (λa, encap H (f a))) a z :=
begin
  simp [transition.encap_iff, transition.sum_iff],
  tauto
end

lemma transition.sum_ext (D : set β) (f g : β → mcrl2 α )
  (h : ∀a' : β, a' ∈ D → ∀z a, (transition (f a') a z ↔ transition (g a') a z)) (z a) :
transition (sum D f) a z ↔ transition (sum D g) a z :=
begin
  simp [transition.sum_iff],
  split,
  { intro h',
    rcases h' with ⟨a', ha', haz⟩,
    apply exists.intro a',
    apply and.intro ha',
    apply iff.elim_left (h a' ha' z a),
    assumption},
  { intro h',
    rcases h' with ⟨a', ha', haz⟩,
    apply exists.intro a',
    apply and.intro ha',
    apply iff.elim_right (h a' ha' z a),
    assumption}
end