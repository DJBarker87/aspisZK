import NNG_ProjectFrames345
import NNG_Events345
import NNG_TryAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DecodeAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

theorem source {W : Type} (s : PublicData W) (env : RSL.Env)
 (next : Decoded W → Code Ret)
 (tail : NNG_Phases345.Decoded LIB_Instances.VL LIB_Instances.C → RSL.Obs (Except RSL.ProgramError RSL.Bytes))
 (later : ∀ st (hd : decodeCall s.publicData=ok (.Ok st)),
  observation NNG_ChildSource345.port (NNG_Events345.events env) (next ⟨s,st⟩)=
   tail (NNG_ProjectFrames345.decoded ⟨s,st⟩ hd)) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_TreeBase345.tryCode ((NNG_Calls345.calls env).c12 s.publicData) (fun st=>next ⟨s,st⟩))=
 NNG_Phases345.stepDecode LIB_Instances.VL LIB_Instances.C (fun _=>true)
  (NNG_ProjectFrames345.publicData s) tail := by
 have after (r : Option Statement) (h : LIBC_S1.decode (LIB_Carriers.bytes s.publicData)=r) :
   observation NNG_ChildSource345.port (NNG_Events345.events env)
    (NNG_TreeBase345.tryCode (ok (NNG_DecoderGraph345.reply r)) (fun st=>next ⟨s,st⟩))=
   NNG_Phases345.afterDecode LIB_Instances.VL LIB_Instances.C (fun _=>true)
    (NNG_ProjectFrames345.publicData s) tail r h := by
  cases r with
  | none=>rfl
  | some st=>
   have hd : decodeCall s.publicData=ok (.Ok st) := by
    rw [NNG_DecoderGraph345.source,h];rfl
   exact later st hd
 change observation _ _ (NNG_TreeBase345.tryCode (decodeCall s.publicData) _) = _
 rw [NNG_DecoderGraph345.source]
 unfold NNG_Phases345.stepDecode
 have allocation : NNG_Pure345.allocationIf
   (LIB_Instances.C.decodeReachesAlloc (NNG_ProjectFrames345.publicData s).publicData) true=
   NNG_Pure345.silent (.ok ()) := by
  cases LIB_Instances.C.decodeReachesAlloc (NNG_ProjectFrames345.publicData s).publicData <;> rfl
 rw [allocation]
 exact after _ rfl
#print axioms source
end AspisR1.NNG_DecodeAssociation345
