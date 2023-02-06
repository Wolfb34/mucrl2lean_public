import ..transition.transition

/- Defining the six channels of the ABP.-/
@[derive decidable_eq]
inductive Int_Channels : Type 
| B : Int_Channels
| C : Int_Channels

@[derive decidable_eq]
inductive Ack_Channels : Type 
| E : Ack_Channels
| F : Ack_Channels

@[derive decidable_eq]
inductive Ext_Channels : Type
| A : Ext_Channels
| D : Ext_Channels


/- The Args type denotes the arguments of sending and receiving, according to which channel is doing the actions.-/
@[derive decidable_eq]
inductive Args (α : Type) [decidable_eq α] : Type
| Int : Int_Channels → option (α × bool) → Args
| Ext : Ext_Channels → α → Args
| Ack : Ack_Channels → option bool → Args

/- An action is a send, receive or communication with a corresponding argument, or the j filler action.-/
inductive Act (α : Type) [decidable_eq α] : Type
| zero : Act
| j : Act
| r : Args α → Act
| s : Args α → Act
| c : Args α → Act

variable {α : Type}
variable [decidable_eq α]

/- Here we set up the comm_semigroup_with_zero for the actions of the ABP-/
namespace Act

def mul : Act α → Act α → Act α
| (r x) (s y) := if x = y then c x else zero
| (s x) (r y) := if x = y then c x else zero
| _ _ := zero

lemma mul_zero (x : Act α) :
mul x zero = zero := by cases x; refl

lemma zero_mul (x : Act α) :
mul zero x = zero := by cases x; refl

lemma mul_comm :
commutative (@mul α _) :=
begin
  intros x y,
  cases x; cases y; unfold mul; split_ifs,
  repeat {refl},
  repeat {assumption},
  repeat {simp [h, h_1] at *, assumption}
end

lemma mul_assoc :
associative (@mul α _) :=
begin
  intros x y z,
  cases x; cases y; cases z; unfold mul; split_ifs; refl
end

instance semigroup : comm_semigroup_with_zero (Act α) := {
   zero := zero,
   mul := mul,
   mul_assoc := mul_assoc,
   mul_zero := mul_zero,
   zero_mul := zero_mul,
   mul_comm := mul_comm
}

end Act