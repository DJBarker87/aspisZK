import R1Z.PV_RW_CursorLoop
set_option autoImplicit false
namespace R1Z.PV_RW_CursorFuel
open PV_RW_Cursor PV_RW_Outcome PV_RW_CursorLoop

def identityStep {E T S : Type} (_ : T) (state : S) : Outcome E S := .ok state

theorem list_identity {E T S : Type} (values : List T) (state : S) :
    listRun (@identityStep E T S) values state=.ok state := by
  induction values with
  | nil => rfl
  | cons value tail ih => exact ih

theorem insufficient {E T S : Type} (fuel : Nat) (cursor : Cursor T) (state : S)
    (short : fuel≤(remaining cursor).length) :
    bounded (@identityStep E T S) fuel cursor state=.div := by
  induction fuel generalizing cursor with
  | zero => rfl
  | succ fuel ih =>
    have active : cursor.index<cursor.values.length := by
      simp only [remaining,List.length_drop] at short
      omega
    rw [PV_RW_CursorLoop.bounded,PV_RW_Cursor.some_step cursor active]
    change bounded (@identityStep E T S) fuel {cursor with index := cursor.index+1} state=.div
    apply ih
    simp only [remaining,List.length_drop] at short ⊢
    omega

theorem sufficient_iff {E T S : Type} (fuel : Nat) (cursor : Cursor T) (state : S) :
    bounded (@identityStep E T S) fuel cursor state=.ok state ↔
      (remaining cursor).length<fuel := by
  constructor
  · intro success
    by_cases enough : (remaining cursor).length<fuel
    · exact enough
    · have fail := insufficient (E:=E) fuel cursor state (by omega)
      rw [fail] at success
      cases success
  · intro enough
    rw [complete _ _ _ _ enough,list_identity]

theorem sixteen_requires_seventeen {E T S : Type} (values : List T) (shape : values.length=16)
    (state : S) :
    bounded (@identityStep E T S) 16 ⟨values,0⟩ state=.div ∧
      bounded (@identityStep E T S) 17 ⟨values,0⟩ state=.ok state := by
  constructor
  · apply insufficient
    simp only [remaining,List.drop_zero,shape]
    omega
  · apply (sufficient_iff _ _ _).mpr
    simp only [remaining,List.drop_zero,shape]
    omega
#print axioms list_identity
#print axioms insufficient
#print axioms sufficient_iff
#print axioms sixteen_requires_seventeen
end R1Z.PV_RW_CursorFuel
