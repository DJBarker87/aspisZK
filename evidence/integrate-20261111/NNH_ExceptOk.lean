import NNH_ReturnedRE
import NNH_Tx1ReturnedValues
set_option autoImplicit false
namespace NNH_ExceptOk
open RSL

theorem bind {E A B : Type} (x : Except E A) (k : A → Except E B) (out : B)
 (success : NNH_ReturnedRE.bindValue x k=.ok out) : ∃ a,x=.ok a ∧ k a=.ok out := by
 cases x with
 | error e => cases success
 | ok a => exact ⟨a,rfl,success⟩

theorem unmap (V : VLib) (r : Except V.VErr Bytes) (out : Bytes)
 (success : NNH_Tx1ReturnedValues.mapVErrValue V r=.ok out) : r=.ok out := by
 cases r with
 | error e => cases success
 | ok value => exact congrArg Except.ok (Except.ok.inj success)
#print axioms bind
#print axioms unmap
end NNH_ExceptOk
