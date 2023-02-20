import tactic
import tactic.induction
import data.option.basic
import ..mcrl2

open mcrl2

variables {α : Type}

variables [comm_semigroup_with_zero α]

/- The seq' operator is used in the rule for x ⬝ y in order to identify the cases for x terminating and not terminating.-/
def seq' : option (mcrl2 α) → mcrl2 α → option (mcrl2 α)
| none y := y
| (some x) y := x ⬝ y

@[simp] lemma seq'_none_coe (y : mcrl2 α) : seq' none (y : mcrl2 α) = y := rfl
@[simp] lemma seq'_coe_coe (x y : mcrl2 α) : seq' (x : option (mcrl2 α)) y = x ⬝ y := rfl

/- The par' operator is used in rules on parallel operators (which include ||, |_ and |)
 to identify all the cases for terminating and not terminating processes.-/
def par' : option (mcrl2 α) → option (mcrl2 α) → option (mcrl2 α)
| none none := none
| (some x) none := x
| none (some y) := y
| (some x) (some y) := x || y -- or `x |_ y + y |_ x + x ∣ y`

@[simp] lemma par'_none_none : (par' none none : option (mcrl2 α)) = none := rfl
@[simp] lemma par'_coe_none (x : mcrl2 α) : par' (x : option (mcrl2 α)) none = x := rfl
@[simp] lemma par'_none_coe (y : mcrl2 α) : par' none (y : option (mcrl2 α)) = y := rfl
@[simp] lemma par'_coe_coe (x y : mcrl2 α) : par' (x : option (mcrl2 α)) y = x || y := rfl


/- The main definition of transitions. -/
inductive transition
: mcrl2 α → α → option (mcrl2 α) → Prop
| atom {a} (h : a ≠ 0) : transition (atom a) a none
| altl {x y z a} (h : transition x a z) :
  transition (x + y) a z
| altr {x y z a} (h : transition y a z) :
  transition (x + y) a z
| sum {β : Type} {f : β → mcrl2 α} {a' z a A} (ha' : a' ∈ A) (h : transition (f a') a z) :
  transition (sum A f) a z
| seq {x y z a} (h : transition x a z) : transition (x ⬝ y) a (seq' z y)
| encap_pass {x y A} {a : α} (h₁ : a ∉ A) (h₂: transition x a y) :
  transition (encap A x) a (encap A <$> y)
| par_l {x x' y a} (h : transition x a x') : transition (x || y) a (par' x' y)
| par_r {x y y' a} (h : transition y a y') : transition (x || y) a (par' x y')
| par_comm {x y x' y' a b} (h₁ : transition x a x')
  (h₂ : transition y b y') (h₃ : a * b ≠ 0) :
  transition (x || y) (a * b) (par' x' y')
| parl {x x' y a} (h : transition x a x') : transition (x |_ y) a (par' x' y)
| comm {x y x' y' a b}  (h₁ : transition x a x')
  (h₂ : transition y b y') (h₃ : a * b ≠ 0) :
  transition (x ∣ y) (a * b) (par' x' y')
