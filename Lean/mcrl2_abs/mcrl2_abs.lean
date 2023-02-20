import .rb_bisim
import ..mcrl2_sum.mcrl2_sum

variables {α : Type}
variables [comm_semigroup_with_zero_and_tau α]

namespace mcrl2

@[instance] def setoid_bmcrl2 : setoid (mcrl2 α) :=
{r     := rb_bisim α,
 iseqv := 
  begin 
    repeat {apply and.intro},
    { apply rb_reflexive},
    { apply rb_symmetric},
    { apply rb_transitive}
  end
}

def bmcrl2' (α : Type) [comm_semigroup_with_zero_and_tau α] := quotient $ (@setoid_bmcrl2 α _) 

class mcrl2_abs (α : Type) (M : Type 1) [comm_semigroup_with_zero_and_tau α] extends mcrl2_sum α M :=
(tau : M)
(abs : set α → M → M)
(seq_tau : ∀x, seq x tau = x)
(tau_keep : ∀x y z, seq x (alt (seq tau (alt y z) ) y) = seq x (alt y z))
(hide_deadlock : ∀I, abs I deadlock = deadlock)
(hide_pass : ∀I a, a ∉ I → abs I (atom a) = atom a)
(hide_fail : ∀I a, a ∈ I → abs I (atom a) = tau)
(hide_alt : ∀I x y, abs I (alt x y) = alt (abs I x) (abs I y))
(hide_seq : ∀I x y, abs I (seq x y) = seq (abs I x) (abs I y))
(hide_sum: ∀I D : set α, ∀f, abs I (sum D f) = sum D (λa, abs I (f a)))


lemma bisim.abs (x₁ x₂ : mcrl2 α) (I) (h : x₁ ≈ x₂) :
mcrl2.abstract I x₁ ≈ mcrl2.abstract I x₂ :=
begin
  rcases h with ⟨R, hR, R_bisim⟩,
  
end



end mcrl2