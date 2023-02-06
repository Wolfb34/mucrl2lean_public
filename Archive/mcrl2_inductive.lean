import tactic

#check (=)

inductive mcrl2 (α : Type) : Type
| atom : α → mcrl2
| seq : mcrl2 → mcrl2 → mcrl2
| alt : mcrl2 → mcrl2 → mcrl2 

instance (α) : has_add (mcrl2 α) := ⟨mcrl2.alt⟩
infix `⬝`:70 := mcrl2.seq

meta def mcrl2.repr : mcrl2 string → string
| (mcrl2.atom a) := a
| (x ⬝ y) := mcrl2.repr x ++ mcrl2.repr y
| (x + y) := "(" ++ mcrl2.repr x ++ " + " ++ mcrl2.repr y ++ ")"

inductive mcrl2_equiv {α : Type} : mcrl2 α → mcrl2 α → Prop
| atom {a} : mcrl2_equiv (mcrl2.atom a) (mcrl2.atom a)
| alt {x y x' y'} (h₁ : mcrl2_equiv x x') (h₂ : mcrl2_equiv y y') :
  mcrl2_equiv (x + y) (x' + y')
| seq {x y x' y'} (h₁ : mcrl2_equiv x x') (h₂ : mcrl2_equiv y y') :
  mcrl2_equiv (x ⬝ y) (x' ⬝ y')
| trans {x y z} (h₁ : mcrl2_equiv x y) (h₂ : mcrl2_equiv y z) :
  mcrl2_equiv x z
| comm {x y} (h : mcrl2_equiv x y) : mcrl2_equiv y x 
| alt_comm {x y} : mcrl2_equiv (x + y) (y + x)
| alt_idem {x} : mcrl2_equiv (x + x) x
| alt_assoc {x y z} : mcrl2_equiv (x + (mcrl2.alt y z)) ((x + y) + z)
| seq_rdist {x y z} : mcrl2_equiv ((x + y) ⬝ z) (x ⬝ z + y ⬝ z)
| seq_assoc {x y z} : mcrl2_equiv ((x ⬝ y) ⬝ z) (x ⬝ (y ⬝ z))

theorem mcrl2_equiv.reflexive {α : Type} : reflexive (λa b : mcrl2 α, mcrl2_equiv a b) :=
begin
  intro x,
  induction x,
  { exact mcrl2_equiv.atom},
  { apply mcrl2_equiv.seq,
    repeat {assumption}},
  { apply mcrl2_equiv.alt,
    repeat {assumption}}
end

#check option.rel

theorem mcrl2_equiv.symmetric {α : Type} : symmetric (λa b : mcrl2 α, mcrl2_equiv a b) :=
begin
  intros x y,
  intro h,
  exact mcrl2_equiv.comm h
end

theorem mcrl2_equiv.transitive {α : Type} : transitive (λa b : mcrl2 α, mcrl2_equiv a b) :=
begin
  intros x y z h h',
  exact mcrl2_equiv.trans h h'
end

@[instance] def setoid_mcrl2 {α : Type} : setoid (mcrl2 α) :=
{ r := (λa b, mcrl2_equiv a b),
  iseqv :=
    begin
      repeat {apply and.intro},
      { exact mcrl2_equiv.reflexive},
      { exact mcrl2_equiv.symmetric},
      { exact mcrl2_equiv.transitive}
    end
}

lemma setoid_iff {α : Type} (a b : mcrl2 α) : 
a ≈ b ↔ mcrl2_equiv a b :=
by refl

def mcrl2' (α : Type)  := quotient $ @setoid_mcrl2 α 

lemma mcrl2'_alt_comm {α} (a b : mcrl2 α) : ⟦mcrl2.alt a b⟧ = ⟦mcrl2.alt b a⟧ :=
begin
apply quotient.sound,
apply mcrl2_equiv.alt_comm
end

lemma mcrl2'_alt_assoc {α} (a b c: mcrl2 α) : ⟦mcrl2.alt a (mcrl2.alt b c)⟧ = ⟦mcrl2.alt (mcrl2.alt a b) c⟧ :=
begin
apply quotient.sound,
apply mcrl2_equiv.alt_assoc
end

#check quot.lift_on₂_mk
class mcrl2_base (α M : Type) :=
  (atom : α → M)
  (alt : M → M → M)
  (seq : M → M → M)
  (alt_comm : ∀x y, alt x y = alt y x)
  (alt_assoc : ∀x y z, alt x (alt y z) = alt (alt x y) z)
  (alt_idem : ∀x, alt x x = x)
  (seq_dist : ∀x y z, seq (alt x y) z = alt (seq x z) (seq y z))
  (seq_assoc : ∀x y z, seq (seq x y) z = seq x (seq y z))

instance (α) : mcrl2_base α (mcrl2' α) := {
  atom := λa, ⟦mcrl2.atom a⟧,
  alt := quotient.lift₂ (λa b, ⟦a + b⟧) 
         begin
          intros a b a' b' ha hb,
          apply quotient.sound,
          apply mcrl2_equiv.alt,
          { exact ha},
          { exact hb}
        end,
  seq := quotient.lift₂ (λa b, ⟦a ⬝ b⟧) 
         begin
          intros a b a' b' ha hb,
          apply quotient.sound,
          apply mcrl2_equiv.seq,
          { exact ha},
          { exact hb}
        end,
  alt_comm := begin
    intros x y,
    apply quot.induction_on₂ x y,
    simp,
    apply mcrl2_equiv.alt_comm    
  end,
  alt_assoc := begin
    intros x y z,
    apply quot.induction_on₃ x y z,
    intros a b c,
    apply quotient.sound,
    exact mcrl2_equiv.alt_assoc
  end,
  alt_idem := begin
    intro x,
    apply quot.induction_on x,
    intro a, 
    apply quotient.sound,
    exact mcrl2_equiv.alt_idem
  end,
  seq_dist := begin
    intros x y z,
    apply quot.induction_on₃ x y z,
    intros a b c,
    apply quotient.sound,
    exact mcrl2_equiv.seq_rdist
  end,
  seq_assoc := begin
    intros x y z,
    apply quot.induction_on₃ x y z,
    intros a b c,
    apply quotient.sound,
    exact mcrl2_equiv.seq_assoc
  end
}


inductive testtype : Type 
| a : testtype
| b : testtype

example : mcrl2' testtype := mcrl2_base.atom testtype.a


example : mcrl2 testtype :=
(mcrl2.atom testtype.a) ⬝ (mcrl2.atom testtype.b)

example : mcrl2_base unit unit := 
{ atom := λ_, (),
  alt := λ_ _, (),
  seq := λ_ _, (),
  alt_comm := by intros x y; refl,
  alt_assoc := by intros x y z; refl,
  alt_idem := begin intro x, cases x, refl end,
  seq_dist := by intros x y z; refl,
  seq_assoc := by intros x y z; refl}

inductive mcrl2_mrg (α : Type) : Type
| base : mcrl2 α → mcrl2_mrg
| atom : α → mcrl2_mrg
| seq : mcrl2_mrg → mcrl2_mrg → mcrl2_mrg
| alt : mcrl2_mrg → mcrl2_mrg → mcrl2_mrg 
| par_left : mcrl2_mrg → mcrl2_mrg → mcrl2_mrg 
| comm : mcrl2_mrg → mcrl2_mrg → mcrl2_mrg 
| par : mcrl2_mrg → mcrl2_mrg → mcrl2_mrg 
| deadlock : mcrl2_mrg



inductive mcrl2_mrg_equiv {α : Type} (γ : α → α → option α) : 
mcrl2_mrg α → mcrl2_mrg α → Prop
| base : mcrl2_mrg_equiv
| par_main {x y} : mcrl2_mrg_equiv (mcrl2_mrg.par x y) 
  ((mcrl2_mrg.par_left x y + mcrl2_mrg.par_left y x) + mcrl2_mrg.comm x y)
| par_left_atom {x a} : mcrl2_mrg_equiv (mcrl2_mrg.par_left (mcrl2_mrg.atom a) x) 
  (mcrl2_mrg.seq (mcrl2_mrg.atom a) x)
| par_left_seq {x y a} : mcrl2_mrg_equiv 
  (mcrl2_mrg.par_left (mcrl2_mrg.seq (mcrl2_mrg.atom a) y) x) 
  (mcrl2_mrg.seq (mcrl2_mrg.atom a) (mcrl2_mrg.par x y))
| par_left_assoc {x y z} : mcrl2_mrg_equiv
  (mcrl2_mrg.par_left (mcrl2_mrg.alt x y ) z)
  (mcrl2_mrg.alt (mcrl2_mrg.par_left x z) (mcrl2_mrg.par_left y z))
| comm_succ {a b c} (h : γ a b = some c) : mcrl2_mrg_equiv 
  (mcrl2_mrg.comm (mcrl2_mrg.atom a) (mcrl2_mrg.atom b))
  (mcrl2_mrg.atom c)
| comm_fail {a b} (h : γ a b = none) : mcrl2_mrg_equiv
  (mcrl2_mrg.comm (mcrl2_mrg.atom a) (mcrl2_mrg.atom b))
  (mcrl2_mrg.deadlock)
| comm_seql {a b x} : mcrl2_mrg_equiv
  (mcrl2_mrg.comm (mcrl2_mrg.seq (mcrl2_mrg.atom a) x) (mcrl2_mrg.atom b))
  (mcrl2_mrg.seq (mcrl2_mrg.comm (mcrl2_mrg.atom a) (mcrl2_mrg.atom b)) x)
| comm_seqr {a b x} : mcrl2_mrg_equiv
  (mcrl2_mrg.comm (mcrl2_mrg.atom a) (mcrl2_mrg.seq (mcrl2_mrg.atom b) x) )
  (mcrl2_mrg.seq (mcrl2_mrg.comm (mcrl2_mrg.atom a) (mcrl2_mrg.atom b)) x)
| comm_seq_two {a b x y} : mcrl2_mrg_equiv
  (mcrl2_mrg.comm 
    (mcrl2_mrg.seq (mcrl2_mrg.atom a) x)
    (mcrl2_mrg.seq (mcrl2_mrg.atom b) y))
  (mcrl2_mrg.seq
    (mcrl2_mrg.comm (mcrl2_mrg.atom a) (mcrl2_mrg.atom b))
    (mcrl2_mrg.par x y))
| comm_distl {x y z} : mcrl2_mrg_equiv 
  (mcrl2_mrg.comm (x + y) z)
  ((mcrl2_mrg.comm x z) + (mcrl2_mrg.comm y z))
| comm_distr {x y z} : mcrl2_mrg_equiv
  (mcrl2_mrg.comm x (y + z))
  ((mcrl2_mrg.comm x y) + (mcrl2_mrg.comm x z))