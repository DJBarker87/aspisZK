import Port10AUTH_TerminalCut

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_VerifyProjection
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect MultiproofConeRef

theorem log {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (root : Digest) (s : reference.Scratch) (nodes : Slice U8) :
    (Port9OR_Code.trace D hash (Port9OR_BatchStep.verify root s.idx s.val s.n nodes)).1=
      (Port9OR_Code.trace D hash (Port9OR_P6Verify.code root {s with «at»:=0#usize} nodes)).1 := by
  unfold Port9OR_BatchStep.verify
  simp only [Port9OR_BatchStep.pair_match]
  exact Port10AUTH_TerminalCut.map_log D hash
    (Port9OR_P6Verify.code root {s with «at»:=0#usize} nodes)
    (fun (out : Bool × reference.Scratch) => (out.1,out.2.idx,out.2.val))

#print axioms log
end AspisR1.Port10AUTH_VerifyProjection
end
