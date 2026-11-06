import NJL_TagRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagForward
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open NJL_TagRawTrace (Selectors)
/-- K035/K036: deployed forwarding arm, SAME immutable borrowed Selectors,
exact coordinate, one call, unchanged4word reply. Scratch is unused. -/
def Cut (s seen : Selectors) (coordinate observed calls : Nat) (reply output : NQ) : Prop :=
 calls=1 ∧ observed=coordinate ∧ seen=s ∧ output=reply
def reference (_scratch : Slice NQ) (c : Fin 30) (s : Selectors) : Result NQ := NJL_TagRoot.reference s c
/-- Closed child216 is applied internally to the SAME selectors/coordinate;
no child success, result equality or operation dictionary is a premise. -/
theorem source (scratch : Slice NQ) (c : Fin 30) (s : Selectors) (hs : FIw_ArrayValue.canonical s.high) :
 ∃ after,reference scratch c s=ok (NJB_Words.value after) ∧
 Cut s s c.val c.val 1 (NJB_Words.value after) (NJB_Words.value after) ∧
 NJL_TagChunks.Trace s (NJL_TagPartition.chunks 68 (NJL_TagData.indices c)) NJL_TagRoot.zero after ∧
 Canon (NJB_Words.value after) ∧ decode (NJB_Words.value after)=NJL_TagMeaning.model s (NJL_TagData.indices c) := by
 obtain ⟨after,call,_,trace,ha,value⟩ := NJL_TagRoot.source s c hs
 exact ⟨after,call,⟨rfl,rfl,rfl,rfl⟩,trace,ha,value⟩
#print source
#print axioms source
end AspisR1.NJL_TagForward
end
