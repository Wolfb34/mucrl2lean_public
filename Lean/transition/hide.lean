import .iff_lemmas

open mcrl2

variable {α : Type}
variable [comm_semigroup_with_zero_and_tau α]

lemma transition.hide_deadlock (I : set α) (a z) : transition (abstract I deadlock) a z ↔ transition deadlock a z :=
begin
  simp [transition.abs_iff, transition.deadlock_iff]
end

lemma transition.hide_pass (I : set α) (a : α) (a ∉ I) (a' z) : transition (abstract I (atom a)) a' z ↔ transition (atom a) a' z := 
begin 
  simp [transition.atom_iff, transition.abs_iff, ←and_assoc],
  simp [and_assoc],
  split,
  { intro h,
    rcases h with ⟨rfl, hI, rfl, ha⟩ | ⟨hI, rfl, ha, rfl⟩,
    { contradiction},
    { exact ⟨rfl, by assumption, rfl⟩}},
  { rintro ⟨rfl, h, rfl⟩,
    exact or.inr ⟨H, rfl, h, rfl⟩}
end

lemma transition.hide_abs (I : set α) (a : α) (h₁ : is_action a) (h₂ : a ∈ I) (a' z) : transition (abstract I (atom a)) a' z ↔ transition mcrl2.tau a' z := 
begin 
  simp [transition.atom_iff, transition.abs_iff, transition.tau_iff, ←and_assoc],
  simp [and_assoc],
  split,
  { intro h,
    rcases h with ⟨rfl, hI, rfl, ha⟩ | ⟨hI, rfl, ha, rfl⟩,
    { exact ⟨rfl, rfl⟩},
    { contradiction}},
  { rintro ⟨rfl, rfl⟩,
    exact or.inl ⟨rfl, h₂, rfl, h₁⟩}
end

lemma transition.hide_alt (I : set α) (x y a z) :
transition (abstract I (x + y)) a z ↔ transition ((abstract I x) + (abstract I y)) a z :=
begin
  simp [transition.abs_iff, transition.alt_iff, and_or_distrib_left, exists_or_distrib,   
        or_assoc, or.left_comm]
end

lemma transition.sum_hide (I D : set α) (f a z) :
transition (abstract I (sum D f)) a z ↔ transition (sum D (λa, abstract I (f a))) a z :=
begin
  simp [transition.abs_iff, transition.sum_iff, and_or_distrib_left, exists_or_distrib, ←exists_and_distrib_left],
  split,
  { intro h,
    rcases h with ⟨b, z', c, rfl, hI, rfl, hD, hf⟩ | ⟨x, a', hI, rfl, hD, hf⟩,
    { exact or.inl ⟨c, b, z', hD, rfl, hI, rfl, hf⟩},
      exact or.inr ⟨a', x, hD, hI, rfl, hf⟩},
  { intro h,
    rcases h with ⟨b, c, z', hD, rfl, hI, rfl, hf⟩ | ⟨b, z', hD, hI, rfl, hf⟩,
    { exact or.inl ⟨c, z', b, rfl, hI, rfl, hD, hf⟩},
    { exact or.inr ⟨z', b, hI, rfl, hD, hf⟩}}
end