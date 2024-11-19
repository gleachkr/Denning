/- SLIDE

*A Lattice Model of Secure Information Flow*

Dorothy Denning

-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Defs
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Basic

/- SLIDE

The Basic Challenge:

  “ … access control mechanisms are designed to control immediate access to
  objects, without taking into account information flow paths implied by a given,
  outstanding collection of access rights.”

But, 

  “ … secruity requires that processes be *unable* to transfer data from files
  of higher security classification to files (or users) of lower ones. Not only
  must a user be prevented from directly reading a file whose security
  classification exceeds his own, but he must be inhibited from indirectly
  accessing such information by collaborating in arbitrarily ingenious ways
  with other users who have authority to access the information.”

-/


/- SLIDE

What is Information Flow?

-/

class InformationFlowModel (N P SC: Type) extends AddCommSemigroup SC, LE SC where
  class_of_obj : N → SC
  class_of_proc : P → SC

/- 

We have a type of security classes SC, a type of objects N (these might be
considered as files, segments, variables, or users). We also have a type of
processes P, “active agents responsible for all information flow”.

1. Each object and process can be assigned a security class

2. Security classes are things like "CUI" or "Top Secret" or "Nuclear Policy".
Some are more secure than others, so we have a notion of ≤ such that `CUI ≤ Top
Secret".

3. We can consider combined security classes, something that is both Top Secret
AND Nuclear Policy. So we have a notion of `+`, which is commutative and
associative.

-/

/-SLIDE





# When is Information Flow Permissible?

Intuitively, an information flow is permissible when it passes information from
a lower security class to a higher security class. 

It's OK to incorporate facts about the news of the day, or meterological data
into a Top Secret report. It's not OK to incorporate facts from a Top Secret
report into your news broadcast.





-/

/-SLIDE

This has some consequences for how we think about the security classes.

-/
class ProperInformationFlowModel (N P SC : Type) extends 
  InformationFlowModel N P SC, 
  IsPartialOrder SC le,
  /- ↑ ≤ needs to be a partial order. Reflexivity because it's OK to move things
  within the same security class, transitivity because anything you're barred
  from doing in one move should be imposssible to do in two, and antisymmetry
  because otherwise some classes would be redundant. -/
  Fintype SC

  where
  bot : SC
  is_least : IsLeast Set.univ bot
  /- ↑ public information is less secure than anything -/

  is_decidable_rel : DecidableRel le
  is_decidable_eq : DecidableEq SC
  /- ↑ ≤ and = need to be decidable for this to be at all practical. -/

  plus_lt_l: ∀x y : SC, x ≤ x + y
  plus_lt_r: ∀x y : SC, y ≤ x + y
  plus_ub : ∀x y z : SC, x ≤ z ∧ y ≤ z → x + y ≤ z
  /- ↑ class combination needs to be a LUB. You need to be able to put Top
     Secret information into a Top Secret + Nuclear report, and if someone is
     allowed to read Top Secret and Nuclear, they're allowed to read Top Secret + Nuclear 
  -/






instance [model : ProperInformationFlowModel N P SC] : Std.Commutative (model.add)  where
  comm := add_comm

instance [model : ProperInformationFlowModel N P SC] : Std.Associative (model.add)  where
  assoc := add_assoc

instance [model : ProperInformationFlowModel N P SC] : DecidableRel (model.le) := 
  model.is_decidable_rel

/--SLIDE 





Those properties happen to entail that the security classes have a natural
*Bounded Lattice* structure. A bounded lattice is a partial order equipped with
a least upper bound and a greatest lower bound operation 

We've got the LUB, how do we get the GLB?





-/

/-SLIDE

We start by considering the sum of a finite set of security classes, the
combination of all members of the set.

-/

def ProperInformationFlowModel.sum
  (model : ProperInformationFlowModel N P SC) 
  (X : Finset SC) 
  : SC := Finset.fold model.add model.bot id X

/- 

This is basically a fold, over a finite set, rather than a list. It's
well-defined because + is commutative and associative.

-/

/-SLIDE

The sum of a finite set of security classes is an upper bound on the set

-/

theorem ProperInformationFlowModel.sum.isUB 
  (model : ProperInformationFlowModel N P SC) 
  (X : Finset SC)
  : x ∈ X → x ≤ model.sum X := by
  intro hyp --consider an arbitrary x in X
  have _ := model.is_decidable_eq
  have not_in := Finset.not_mem_erase x X -- It's not in X - {x}
  have decomp : X = (X.erase x).cons x not_in := by -- so X = {x} ∪ X - {x}
    apply Finset.ext_iff.mpr
    intro a
    constructor
    case mp => cases model.is_decidable_eq x a; repeat aesop
    case mpr => repeat aesop
  rw [decomp]; unfold ProperInformationFlowModel.sum
  rw [Finset.fold_cons] -- and sum X = x + sum X - {x}
  apply model.plus_lt_l -- so x ≤ sum X by plus_lt_l

/-SLIDE

It's also a smaller than any other upper bound.

-/

theorem ProperInformationFlowModel.sum.isMinimal
  (model : ProperInformationFlowModel N P SC) 
  (X : Finset SC)
  : (∀x ∈ X, x ≤ y) → model.sum X ≤ y := by
  have _ := model.is_decidable_eq
  -- we argue by induction the construction of the set
  apply @Finset.induction_on _ _ model.is_decidable_eq X
  -- for base case, it's immediate because we start the fold from the bottom element.
  · unfold ProperInformationFlowModel.sum
    simp
    apply model.is_least.2
    trivial
  -- for the indiction case…
  · intro x X not_in hyp₂ hyp
    unfold ProperInformationFlowModel.sum
    aesop
    -- we recognize that sum x ∪ X, where x isn't in X, is x + sum X
    apply model.plus_ub
    -- and the result follows from plus_ub
    aesop




/--SLIDE

We can then define the GLB of two security classes as the sum of everything
less secure than both classes.

-/

@[simp]
def ProperInformationFlowModel.inf
  (model : ProperInformationFlowModel N P SC)
  (a b : SC) : SC := model.sum { x | x ≤ a ∧ x ≤ b}

/-

This has some intuition behind it. The most secure class that can flow into
both A and B will need to be at least as secure as anything that can flow into
both A and B. So it should be the LUB of all classes that can flow into A and
B.

-/


/--SLIDE

Once you've got those definitions, you can fairly straightforwardly prove that
the security classes compose a lattice. We do it here with the algebraic
definition of a lattice - we need sup and inf to obey the axioms

 sup_comm : ∀ (a b : α), a ⊔ b = b ⊔ a

 sup_assoc : ∀ (a b c : α), a ⊔ b ⊔ c = a ⊔ (b ⊔ c)

 inf_comm : ∀ (a b : α), a ⊓ b = b ⊓ a 

 inf_assoc : ∀ (a b c : α), a ⊓ b ⊓ c = a ⊓ (b ⊓ c)

 sup_inf_self : ∀ (a b : α), a ⊔ a ⊓ b = a

 inf_sup_self : ∀ (a b : α), a ⊓ (a ⊔ b) = a

-/

def lattice_of 
  (model : ProperInformationFlowModel N P SC) 
  : Lattice SC := by
    apply @Lattice.mk' SC ⟨model.add⟩ ⟨model.inf⟩

    /- The proofs can mostly be automated using the LUB properies of sum -/




    case sup_comm => exact add_comm
    case sup_assoc => exact add_assoc
    case inf_comm => 
      intro a b; simp
      suffices 
        ({ x | x ≤ a ∧ x ≤ b} : Finset SC) 
        = 
        ({ x | x ≤ b ∧ x ≤ a} : Finset SC) 
      by rw [this]
      apply Finset.ext_iff.mpr
      aesop
    case inf_assoc =>
      intro a b c; simp
      suffices 
        ({x | x ≤ model.sum { x | x ≤ a ∧ x ≤ b} ∧ x ≤ c} : Finset SC)
        = 
        ({x | x ≤ a ∧ x ≤ model.sum { x | x ≤ b ∧ x ≤ c}} : Finset SC) 
        by rw [this]
      apply Finset.ext_iff.mpr
      aesop (add 
        safe ProperInformationFlowModel.sum.isMinimal,
        safe ProperInformationFlowModel.sum.isUB,
        unsafe model.trans)
    case sup_inf_self =>
      intro a b; simp
      apply model.antisymm
      · apply model.plus_ub; refine ⟨model.reflexive a,?_⟩
        aesop (add 
          safe ProperInformationFlowModel.sum.isMinimal, 
          safe ProperInformationFlowModel.sum.isUB, 
          unsafe model.trans
        )
      · apply model.plus_lt_l
    case inf_sup_self =>
      intro a b; simp
      apply model.antisymm
      · aesop (add safe ProperInformationFlowModel.sum.isMinimal, safe ProperInformationFlowModel.sum.isUB, unsafe model.trans)
      · apply ProperInformationFlowModel.sum.isUB
        simp; constructor
        · exact model.reflexive a
        · exact model.plus_lt_l a b

/-SLIDE

So, practically speaking, what does a security lattice look like? 

We might start from a fundamental set of orthogonal security groups. Maybe
access to medical, financial and criminal information about some person.

-/

inductive SecGroups
| med
| fin
| crim
deriving DecidableEq

/- 

we can model our security classes as finite sets of security groups with the meaning that
objects in this class are allowed to store information from any of the security
groups in this set, including combined information.

-/

instance : Add (Finset SecGroups) where
  add x y := x ∪ y

/- security class combination is then just union -/





/- SLIDE

We can then pretty easily derive a proper information flow model for this
notion of security group.

-/


example : ProperInformationFlowModel α β (Finset SecGroups)  where
  add_comm := by 
    intro a b
    apply Finset.ext_iff.mpr
    simp [HAdd.hAdd, Add.add]
    aesop
  add_assoc := by
    intro a b c
    apply Finset.ext_iff.mpr
    simp [HAdd.hAdd, Add.add]
  bot := {}
  class_of_obj := λ_ => {}
  class_of_proc := λ_ => {}
  elems := Finset.powerset {SecGroups.med, SecGroups.fin, SecGroups.crim}
  complete := by intro x; simp; intro y; cases y; repeat aesop
  is_least := by simp
  is_decidable_rel := Finset.instDecidableRelSubset
  is_decidable_eq := Finset.decidableEq
  plus_lt_l := by simp [HAdd.hAdd, Add.add]; intro x y z; aesop
  plus_lt_r := by simp [HAdd.hAdd, Add.add]; intro x y z; aesop
  plus_ub := by simp [HAdd.hAdd, Add.add]; intro x y z h₁ h₂ w; aesop

/-SLIDE 

Once you've got a security model, what should you do with it?

Denning gestures at the idea of statically verifying “an abstract
representation of programs that preserves the flows but not necessarily all of
the original structure”

-/

inductive NAbstractIdent where
| NLit : Nat → NAbstractIdent
| NVar : Char → NAbstractIdent
| Plus : NAbstractIdent → NAbstractIdent → NAbstractIdent
| Times : NAbstractIdent → NAbstractIdent → NAbstractIdent

inductive BAbstractIdent where
| BLit : Bool → BAbstractIdent
| BVar : Char → BAbstractIdent
| Eq : NAbstractIdent → NAbstractIdent → BAbstractIdent

inductive AbstractProgram where 
| NAssign : Char → NAbstractIdent → AbstractProgram
| BAssign : Char → BAbstractIdent → AbstractProgram
| Print : String → AbstractProgram
| Compose : AbstractProgram → AbstractProgram → AbstractProgram
| While : BAbstractIdent → AbstractProgram → AbstractProgram
| Cond : BAbstractIdent → AbstractProgram → AbstractProgram → AbstractProgram

/-SLIDE
We use our identifiers to calculate a security classes for each expression,
based on the security classes of its parts.
-/

def NAbstractIdent.class_of [model: ProperInformationFlowModel Char Char α] : NAbstractIdent → α 
| NLit _ => model.bot
| NVar c => model.class_of_obj c
| Plus a b => a.class_of + b.class_of
| Times a b => a.class_of + b.class_of

def BAbstractIdent.class_of [model: ProperInformationFlowModel Char Char α] : BAbstractIdent → α 
| BLit _ => model.bot
| BVar c => model.class_of_obj c
| Eq a b => a.class_of + b.class_of

/-
To access the output of a functional expression, you need to be permitted to
access all inputs (since you might be able to figure out the inputs from the
output). So we use the combined classes of all the inputs.
-/





open AbstractProgram
open NAbstractIdent
open BAbstractIdent




/-SLIDE 

We can generate a list of all the objects that a given program explicitly
deposits information into.

-/

def AbstractProgram.flowTo (model : ProperInformationFlowModel Char Char α) : AbstractProgram → Finset Char
| Print _ => {}
| Compose p₁ p₂ => flowTo model p₁ ∪ flowTo model p₂
| BAssign c _ => {c}
| NAssign c _ => {c}
| Cond _ p₁ p₂ => flowTo model p₁ ∪ flowTo model p₂ --?
| While _ p₁ => flowTo model p₁

/-SLIDE

The security requirements for a program are then mostly pretty clear:

-/

def isSecure (model : ProperInformationFlowModel Char Char α) : AbstractProgram → Bool
-- “an elementary statement S is secure if any explcit flow caused by S is secure”
| BAssign c i => model.class_of_obj c ≥ i.class_of
| NAssign c i => model.class_of_obj c ≥ i.class_of
| Print _ => true
-- “S = S₁;S₂ is secure if both S₁ and S₂ are individually secure”
| Compose p₁ p₂ => isSecure model p₁ ∧ isSecure model p₂


--SLIDE
| Cond b p₁ p₂ => isSecure model p₁ ∧ isSecure model p₂ 
  ∧ ∀x, x ∈ flowTo model p₁ ∪ flowTo model p₂ → b.class_of ≤ model.class_of_obj x
| While b p  => isSecure model p
  ∧ ∀x, x ∈ flowTo model p → b.class_of ≤ model.class_of_obj x

/-
The main subtlety is related to control flow. Control flow leaks information.

Even if the value of a condition C is not deposited in a variable, the value of
the variable can still depend on the condition, if that value was assigned
because of control flow depending on C.

  if C then x := True else x := False ≡ x := C

So, for conditional statements, Denning says:

“S = c:S₁,… is secure if each Sₖ is secure and all implicit flows from c are secure.

Let b₁,… be the objects into which S specifies explicit flows. Then all
implicit flow is secure if c ≤ bₖ [for each k] or equivalently c ≤ inf b₁,…

-/


/-SLIDE 

  This, for me, is the most interesting part. There's a kind of duality
  between construction and control: a variable needs to be more secure than
  everything it is constructed out of, and less secure than anything it controls.

  Because: you can infer the components from the construct, and you can infer
  the controller from the controlled.

-/

/-SLIDE

You can implement a proper information flow for the above pretty easily

-/

def ex2 : ProperInformationFlowModel Char Char (Finset SecGroups)  where
  add_comm := by 
    intro a b
    apply Finset.ext_iff.mpr
    simp [HAdd.hAdd, Add.add]
    aesop
  add_assoc := by
    intro a b c
    apply Finset.ext_iff.mpr
    simp [HAdd.hAdd, Add.add]
  bot := {}
  class_of_obj x := match x with
  | 'a' | 'b' | 'c' => {SecGroups.crim, SecGroups.med}
  | _ => {}
  class_of_proc := λ_ => {}
  elems := Finset.powerset {SecGroups.med, SecGroups.fin, SecGroups.crim}
  complete := by intro x; simp; intro y; cases y; repeat aesop
  is_least := by simp
  is_decidable_rel := Finset.instDecidableRelSubset
  is_decidable_eq := Finset.decidableEq
  plus_lt_l := by simp [HAdd.hAdd, Add.add]; intro x y z; aesop
  plus_lt_r := by simp [HAdd.hAdd, Add.add]; intro x y z; aesop
  plus_ub := by simp [HAdd.hAdd, Add.add]; intro x y z h₁ h₂ w; aesop

/-SLIDE 

and you can then go on to check some actual mini-programs 

-/

#check isSecure ex2 (Print "hello")

#check isSecure ex2 (NAssign 'a' (NVar 'z'))

#check isSecure ex2 (NAssign 'a' (NLit 1))

#check isSecure ex2 (NAssign 'z' (NVar 'a'))

#check isSecure ex2 (Cond (Eq (NVar 'a') (NLit 1)) 
  (NAssign 'z' (NLit 1)) 
  (NAssign 'z' (NLit 0)))

#check isSecure ex2 (Cond (Eq (NVar 'z') (NLit 1)) 
  (NAssign 'a' (NLit 1)) 
  (NAssign 'a' (NLit 0)))

/-SLIDE 

There are some things about the above that need filling in.

-/

#check isSecure ex2 (Cond (Eq (NVar 'a') (NLit 1)) 
  (Print "1") 
  (Print "0")) --oops

/- ↑ Really, IO needs to be treated as an object -/

#check isSecure ex2 (Cond (Eq (NVar 'z') (NVar 'z')) 
  (Cond (Eq (NVar 'z') (NLit 1)) 
    (NAssign 'a' (NLit 1)) 
    (NAssign 'a' (NLit 0))) 
  (Print "impossible")) --oops

/- ↑ And we need a better analysis of implicit flow, there's something I'm not
   getting in Dennings literal definition -/











