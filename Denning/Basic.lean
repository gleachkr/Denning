import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Defs
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Insert

class InformationFlowModel (N P SC: Type) extends AddCommSemigroup SC, LE SC where
  class_of_obj : N → SC
  class_of_proc : P → SC

--Denning's definition of the class of the "result" of a binary function is
--pretty darn confusing. She says that the class of the output of a function is
--the sum of the classes of the inputs to the function. But one output can
--result from many functions, and many function invocations, so this isn't
--unique. Maybe it suggests some kind of hidden monadic structure.

-- read the LT as "is less secure/sensitive"

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

def ProperInformationFlowModel.joint_lbs 
  (model : ProperInformationFlowModel N P SC) 
  (a b : SC) 
  : Finset SC := { x | x ≤ a ∧ x ≤ b}

@[simp]
def ProperInformationFlowModel.inf
  (model : ProperInformationFlowModel N P SC)
  (a b : SC) : SC := model.sum (model.joint_lbs a b)
  
def lattice_of 
  (model : ProperInformationFlowModel N P SC) 
  : Lattice SC := by
    apply @Lattice.mk' SC ⟨model.add⟩ ⟨model.inf⟩
    case sup_comm => exact add_comm
    case sup_assoc => exact add_assoc
    case inf_comm => 
      intro a b
      simp
      suffices model.joint_lbs a b = model.joint_lbs b a by rw [this]
      unfold ProperInformationFlowModel.joint_lbs
      apply Finset.ext_iff.mpr
      intro c; constructor
      case mp => aesop
      case mpr => aesop
    case inf_assoc =>
      intro a b c
      simp
      sorry
    case sup_inf_self =>
      intro a b; simp
      apply model.antisymm
      · apply model.plus_ub
        refine ⟨model.reflexive a,?_⟩
        sorry -- need to show that sum is actually LUB
      · apply model.plus_lt_l
    case inf_sup_self =>
      intro a b; simp
      sorry -- basically will need to show that LUB of { x ≤ a } = a
