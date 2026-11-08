import NNG_Producer094
import NNG_Silent094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Terminal094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136
/-- The deployed final mark is silent and returns the SAME byte vector. -/
theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit) (bytes : alloc.vec.Vec U8)
 (observer : s.observer=none) :
 RSL.RE.pure (LIB_Carriers.bytes bytes.deref) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_markCheckpointWrite (NNG_InstalledCalls094.calls env) s bytes)) := by
 unfold NNG_Tree094.f_markCheckpointWrite
 dsimp only
 rw [observer]
 change RSL.RE.pure (LIB_Carriers.bytes bytes.deref) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NMT_CallTree.bind (invoke "verifier.mark" ((none : Option (verifier.Phase → Result Unit)),verifier.Phase.CheckpointWrite) (.ok ()))
    (fun _=>pure (.Ok bytes))))
 rw [NNG_Silent094.invoke_ok NNG_Producer094.port env _ _ _ _
  (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))]
 rfl
#print axioms source
end AspisR1.NNG_Terminal094
