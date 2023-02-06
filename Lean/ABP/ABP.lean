import ..mcrl2_sum.mcrl2_sum
import .Actions

variable {α : Type}
variable [decidable_eq α]

/- Shorthand for mcrl2 actions. -/
def Ext.recv : Ext_Channels → α → mcrl2 (Act α)
| I d := mcrl2.atom (Act.r (Args.Ext I d))

def Ext.send : Ext_Channels → α → mcrl2 (Act α)
| I d := mcrl2.atom (Act.s (Args.Ext I d))

def Int.recv : Int_Channels → α → bool → mcrl2 (Act α)
| I d b := mcrl2.atom (Act.r (Args.Int I (d, b)))

def Int.send : Int_Channels → α → bool → mcrl2 (Act α)
| I d b := mcrl2.atom (Act.s (Args.Int I (d, b)))

def Int.recv_fail : Int_Channels → mcrl2 (Act α)
| I := mcrl2.atom (Act.r (Args.Int I none))

def Int.send_fail : Int_Channels → mcrl2 (Act α)
| I := mcrl2.atom (Act.s (Args.Int I none))

def Ack.recv : Ack_Channels → option bool → mcrl2 (Act α)
| I b := mcrl2.atom (Act.r (Args.Ack I b))

def Ack.send : Ack_Channels → option bool → mcrl2 (Act α)
| I b := mcrl2.atom (Act.s (Args.Ack I b))

def Act.fill : mcrl2 (Act α) := mcrl2.atom Act.j

open Ext_Channels
open Int_Channels
open Ack_Channels

/- The type definition used to define the ABP. -/
inductive Step (α : Type) : Type
| S (b : bool) (n : nat) : Step
| T (d : α) (b : bool) (n : nat) : Step
| R (b : bool) (n : nat) : Step
| K (n : nat) : Step
| L (n : nat) : Step
| Fin (n : nat) : Step

/- This redefinition is necessary to automatically prove the definition decreasing. -/
def Step.sizeof' : Step α → nat 
| (Step.S _ n) := n
| (Step.T _ _ n) := n
| (Step.R _ n) := n
| (Step.K n) := n
| (Step.L n) := n
| (Step.Fin n) := n

instance : has_sizeof (Step α) := {
  sizeof := Step.sizeof'
}

/- Our old definition of the ABP with mutual recursion. -/
-- mutual def S, T, R, K, L, Fin
-- with S : bool → nat → mcrl2 (Act α)
-- | b n := mcrl2.sum D (λd, (Ext.recv A d) ⬝
--                            (Int.send B d b) ⬝
--                            (T d b n))
-- with T : α → bool → nat → mcrl2 (Act α)
-- | d b 0 := (Ack.send F b) + 
--            ((Ack.recv F (bnot b)) + (Ack.recv F 0)) ⬝
--            (Int.send B d b) ⬝ (T d b 0)           
-- | d b n := (Ack.send F b) ⬝ (S (not b) (n - 1)) +
--            ((Ack.recv F (bnot b)) + (Ack.recv F 0)) ⬝
--            (Int.send B d b) ⬝ (T d b n)
-- with R : bool → mcrl2 (Act α)
-- | b := (mcrl2.sum D (λd, (Int.recv C d b) ⬝ (Ext.send D d) ⬝ R (bnot b))) +
--        (mcrl2.sum D (λd, ((Int.recv C d (bnot b)) + (Int.recv_fail C)) ⬝ (Ack.send E (bnot b)) ⬝ R b))
-- with K : mcrl2 (Act α) = mcrl2.sum D        (λd,  
--                          mcrl2.sum {tt, ff} (λb, 
--                     (Int.recv B d b) ⬝ 
--                     (Act.fill ⬝ (Int.send C d b) + 
--                      Act.fill ⬝ (Int.send_fail C)))) ⬝ K
-- with L : mcrl2 (Act α) = mcrl2.sum {tt, ff} (λb, 
--   (Ack.recv E b) ⬝ 
--   (Act.fill ⬝ (Ack.send F b) + Act.fill ⬝ (Ack.send F 0))) ⬝ L
-- with Fin : nat → mcrl2.mcrl2' (Act α)
-- | n := ⟦mcrl2.encap H (S ff n || R ff || K || L)⟧ 

/- Given a set of data D, this models the ABP, where the channels receive and send data from D. -/
def ABP (α : Type) [decidable_eq α]  (D : set α) : Step α → mcrl2 (Act α)
| (Step.S b 0) := 
  mcrl2.sum D (λd, (Ext.recv A d) ⬝                  
                   (Int.send B d b))
| (Step.S b (nat.succ n)) := 
  mcrl2.sum D (λd, (Ext.recv A d) ⬝
                   (Int.send B d b) ⬝
                   (ABP (Step.T d b n)))
| (Step.T d b 0) := (Ack.send F b) + 
                    ((Ack.recv F (bnot b)) + (Ack.recv F none)) ⬝
                    (Int.send B d b)
| (Step.T d b (nat.succ n)) := 
  (Ack.send F b) ⬝ (ABP (Step.S (not b) n)) +
  ((Ack.recv F (bnot b)) + (Ack.recv F none)) ⬝
  (Int.send B d b) ⬝ (ABP (Step.T d b n))
| (Step.R b 0) := 
  (mcrl2.sum D (λd, (Int.recv C d b) ⬝ 
                    (Ext.send Ext_Channels.D d))) +
  (mcrl2.sum D (λd, ((Int.recv C d (bnot b)) + (Int.recv_fail C)) ⬝ 
                    (Ack.send E (bnot b))))
| (Step.R b (nat.succ n)) := 
  (mcrl2.sum D (λd, (Int.recv C d b) ⬝ 
                    (Ext.send Ext_Channels.D d) ⬝ ABP (Step.R (bnot b) n))) +
  (mcrl2.sum D (λd, ((Int.recv C d (bnot b)) + (Int.recv_fail C)) ⬝ 
                    (Ack.send E (bnot b)) ⬝ ABP (Step.R b n)))
| (Step.K 0) := 
  mcrl2.sum D (λd,  
  mcrl2.sum {tt, ff} (λb, (Int.recv B d b) ⬝ 
                          (Act.fill ⬝ (Int.send C d b) + 
                           Act.fill ⬝ (Int.send_fail C))))
| (Step.K (nat.succ n)) :=
  mcrl2.sum D (λd,  
  mcrl2.sum {tt, ff} (λb, (Int.recv B d b) ⬝ 
                          (Act.fill ⬝ (Int.send C d b) + 
                           Act.fill ⬝ (Int.send_fail C)))) ⬝ ABP (Step.K n)
| (Step.L 0) :=
  mcrl2.sum {↑tt, ↑ff} (λb, (Ack.recv E b) ⬝ 
                            (Act.fill ⬝ (Ack.send F b) + 
                             Act.fill ⬝ (Ack.send F none)))            
| (Step.L (nat.succ n)) := 
  mcrl2.sum {↑tt, ↑ff} (λb, (Ack.recv E b) ⬝ 
                            (Act.fill ⬝ (Ack.send F b) + 
                             Act.fill ⬝ (Ack.send F none))) ⬝ (ABP (Step.L n))
| (Step.Fin 0) := mcrl2.deadlock                                        
| (Step.Fin (nat.succ n)) := 
  (ABP (Step.S ff n) || ABP (Step.R ff n) || ABP (Step.K n) || ABP (Step.L n))

/- The set used to force communication via encapsulation.-/
inductive H : set (Act α)
| r {x} (h : ∀I d, x ≠ Args.Ext I d) : H (Act.r x)
| s {x} (h : ∀I d, x ≠ Args.Ext I d) : H (Act.s x) 

def ABP_True {β : Type} [decidable_eq β] : set β → nat → mcrl2 (Act β)
| X n := mcrl2.encap H (ABP β X (Step.Fin n))

@[derive decidable_eq]
inductive Data : Type
| d₁ | d₂

def Data.ABP : mcrl2 (Act Data) := ABP_True {Data.d₁, Data.d₂} 1

