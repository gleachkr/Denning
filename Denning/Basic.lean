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

class InformationFlowModel (N P SC: Type) extends AddCommSemigroup SC, LE SC where
  class_of_obj : N → SC
  class_of_proc : P → SC

class ProperInformationFlowModel (N P SC : Type) extends 
  InformationFlowModel N P SC, 
  IsPartialOrder SC le,
  Fintype SC
  where
  bot : SC
  is_least : IsLeast Set.univ bot
  is_decidable_rel : DecidableRel le
  is_decidable_eq : DecidableEq SC
  plus_lt_l: ∀x y : SC, x ≤ x + y
  plus_lt_r: ∀x y : SC, y ≤ x + y
  plus_ub : ∀x y z : SC, x ≤ z ∧ y ≤ z → x + y ≤ z

instance [model : ProperInformationFlowModel N P SC] : Std.Commutative (model.add)  where
  comm := add_comm

instance [model : ProperInformationFlowModel N P SC] : Std.Associative (model.add)  where
  assoc := add_assoc

instance [model : ProperInformationFlowModel N P SC] : DecidableRel (model.le) := 
  model.is_decidable_rel


def ProperInformationFlowModel.sum
  (model : ProperInformationFlowModel N P SC) 
  (X : Finset SC) 
  : SC := Finset.fold model.add model.bot id X

theorem ProperInformationFlowModel.sum.isUB 
  (model : ProperInformationFlowModel N P SC) 
  (X : Finset SC)
  : x ∈ X → x ≤ model.sum X := by
  intro hyp
  have _ := model.is_decidable_eq
  have not_in := Finset.not_mem_erase x X 
  have decomp : X = (X.erase x).cons x not_in := by
    apply Finset.ext_iff.mpr
    intro a
    constructor
    case mp => cases model.is_decidable_eq x a; repeat aesop
    case mpr => repeat aesop
  rw [decomp]; unfold ProperInformationFlowModel.sum
  rw [Finset.fold_cons]
  apply model.plus_lt_l

theorem ProperInformationFlowModel.sum.isMinimal
  (model : ProperInformationFlowModel N P SC) 
  (X : Finset SC)
  : (∀x ∈ X, x ≤ y) →  model.sum X ≤ y := by
  have _ := model.is_decidable_eq
  apply @Finset.induction_on _ _ model.is_decidable_eq X
  · unfold ProperInformationFlowModel.sum
    simp
    apply model.is_least.2
    trivial
  · intro a s not_in hyp₂
    intro hyp
    unfold ProperInformationFlowModel.sum
    simp
    aesop
    apply model.plus_ub
    aesop

@[simp]
def ProperInformationFlowModel.inf
  (model : ProperInformationFlowModel N P SC)
  (a b : SC) : SC := model.sum { x | x ≤ a ∧ x ≤ b}
  
def lattice_of 
  (model : ProperInformationFlowModel N P SC) 
  : Lattice SC := by
    apply @Lattice.mk' SC ⟨model.add⟩ ⟨model.inf⟩
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
      aesop (add safe ProperInformationFlowModel.sum.isMinimal, safe ProperInformationFlowModel.sum.isUB, unsafe model.trans)
    case sup_inf_self =>
      intro a b; simp
      apply model.antisymm
      · apply model.plus_ub; refine ⟨model.reflexive a,?_⟩
        aesop (add safe ProperInformationFlowModel.sum.isMinimal, safe ProperInformationFlowModel.sum.isUB, unsafe model.trans)
      · apply model.plus_lt_l
    case inf_sup_self =>
      intro a b; simp
      apply model.antisymm
      · aesop (add safe ProperInformationFlowModel.sum.isMinimal, safe ProperInformationFlowModel.sum.isUB, unsafe model.trans)
      · apply ProperInformationFlowModel.sum.isUB
        simp; constructor
        · exact model.reflexive a
        · exact model.plus_lt_l a b

inductive SecGroups
| med
| fin
| crim
deriving DecidableEq

instance : Add (Finset SecGroups) where
  add x y := x ∪ y

example : ProperInformationFlowModel Bool Bool (Finset SecGroups)  where
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

inductive NAbstractIdent where
| NLit : Nat → NAbstractIdent
| NVar : Char → NAbstractIdent
| Plus : NAbstractIdent → NAbstractIdent → NAbstractIdent
| Times : NAbstractIdent → NAbstractIdent → NAbstractIdent

def NAbstractIdent.class_of [model: ProperInformationFlowModel Char Char α] : NAbstractIdent → α 
| NLit _ => model.bot
| NVar c => model.class_of_obj c
| Plus a b => a.class_of + b.class_of
| Times a b => a.class_of + b.class_of

inductive BAbstractIdent where
| BLit : Bool → BAbstractIdent
| BVar : Char → BAbstractIdent
| Eq : NAbstractIdent → NAbstractIdent → BAbstractIdent

def BAbstractIdent.class_of [model: ProperInformationFlowModel Char Char α] : BAbstractIdent → α 
| BLit _ => model.bot
| BVar c => model.class_of_obj c
| Eq a b => a.class_of + b.class_of

inductive AbstractProgram where 
| NAssign : Char → NAbstractIdent → AbstractProgram
| BAssign : Char → BAbstractIdent → AbstractProgram
| Print : String → AbstractProgram
| Compose : AbstractProgram → AbstractProgram → AbstractProgram
| Cond : BAbstractIdent → AbstractProgram → AbstractProgram → AbstractProgram

open AbstractProgram
open NAbstractIdent
open BAbstractIdent

def AbstractProgram.flowTo (model : ProperInformationFlowModel Char Char α) : AbstractProgram → Finset Char
| Print _ => {}
| Compose p₁ p₂ => flowTo model p₁ ∪ flowTo model p₂
| BAssign c _ => {c}
| NAssign c _ => {c}
| Cond _ p₁ p₂ => flowTo model p₁ ∪ flowTo model p₂ --?

def isSecure (model : ProperInformationFlowModel Char Char α) : AbstractProgram → Bool
| Print _ => true
| Compose p₁ p₂ => isSecure model p₁ ∧ isSecure model p₂
| BAssign c i => model.class_of_obj c ≥ i.class_of
| NAssign c i => model.class_of_obj c ≥ i.class_of
| Cond b p₁ p₂ => isSecure model p₁ ∧ isSecure model p₂ 
  ∧ ∀x, x ∈ flowTo model p₁ ∪ flowTo model p₂ → b.class_of ≤ model.class_of_obj x

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

#check isSecure ex2 (Cond (Eq (NVar 'z') (NVar 'z')) 
  (Cond (Eq (NVar 'z') (NLit 1)) 
    (NAssign 'a' (NLit 1)) 
    (NAssign 'a' (NLit 0))) 
  (Print "impossible")) --oops

#check isSecure ex2 (Cond (Eq (NVar 'a') (NLit 1)) 
  (Print "1") 
  (Print "0")) --oops
