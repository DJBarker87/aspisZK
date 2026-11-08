import NNG_ProjectFrames345
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
 change observation _ _ (NNG_TreeBase345.tryCode (decodeCall s.publicData) _) = _
 rw [NNG_DecoderGraph345.source]
 unfold NNG_Phases345.stepDecode
 change _=NNG_Obs345.tryObs (NNG_Pure345.allocationIf (LIBC_S1.reaches (LIB_Carriers.bytes s.publicData)) true) _
 cases reached : LIBC_S1.reaches (LIB_Carriers.bytes s.publicData) <;>
  cases decoded : LIBC_S1.decode (LIB_Carriers.bytes s.publicData) with
  | none=>rfl
  | some st=>
   have hd : decodeCall s.publicData=ok (.Ok st) := by
    rw [NNG_DecoderGraph345.source,decoded];rfl
   exact later st hd
#print axioms source
end AspisR1.NNG_DecodeAssociation345
