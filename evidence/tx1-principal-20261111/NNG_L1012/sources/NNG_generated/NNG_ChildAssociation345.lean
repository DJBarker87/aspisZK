import NNG_ReturnAssociation345
import NNG_BindAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ChildAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

def finish (bytes : Slice U8) (checkpoint : alloc.vec.Vec U8) : Code Ret :=
 if alloc.vec.Vec.len checkpoint != Slice.len bytes then pure (.Err .InvalidAccountData)
 else pure (.Ok checkpoint)

theorem source (pub : Public) (publicBytes proof bytes : Slice U8) (k : Usize)
 (env : RSL.Env) (bound : k.val≤UScalar.cMax .Usize) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_TreeTail345.tryChild (pub,publicBytes,proof,k)
  (NNG_ChildSource345.call env pub publicBytes proof k) (finish bytes))=
 NNG_Obs345.tryObs (NNG_Producer328.producer (NNG_ChildSource345.args pub publicBytes proof k) env)
  (NNG_Phases345.stepReturn (LIB_Carriers.bytes bytes).length) := by
 unfold NNG_TreeTail345.tryChild
 change observation _ _ (NMT_CallTree.bind _ _) = _
 have step := NNG_BindAssociation345.source NNG_ChildSource345.port NNG_ChildSource345.port
  (NNG_Events345.events env)
  (invoke "TX1:328/first_decoded" (pub,publicBytes,proof,k) (NNG_ChildSource345.call env pub publicBytes proof k))
  (fun r=>match r with | .Ok b=>finish bytes b | .Err e=>pure (.Err e))
  (fun r=>match r with
   | .ok b=>NNG_Phases345.stepReturn (LIB_Carriers.bytes bytes).length b
   | .error e=>NNG_Pure345.silent (.error e))
  (fun r=>by
   cases r with
   | Err e=>rfl
   | Ok b=>exact NNG_ReturnAssociation345.source b bytes env)
 refine step.trans ?_
 rw [NNG_Events345.observation env pub publicBytes proof k bound]
 rfl
#print axioms source
end AspisR1.NNG_ChildAssociation345
