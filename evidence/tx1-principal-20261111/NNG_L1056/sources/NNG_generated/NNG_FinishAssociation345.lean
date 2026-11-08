import NNG_TailAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136
abbrev LogicalProof := NNG_Phases345.ProofData LIB_Instances.VL LIB_Instances.C

def finish (p : LogicalProof) (env : RSL.Env) : RSL.Obs (Except RSL.ProgramError RSL.Bytes) :=
 NNG_Phases345.stepProofGuard LIB_Instances.VL LIB_Instances.C p
 (fun p=>NNG_Phases345.stepFirst LIB_Instances.VL LIB_Instances.C NNG_Producer328.producer p env)

theorem source {W : Type} (s : ProofData W) (env : RSL.Env)
 (hd : decodeCall s.publicData=ok (.Ok s.statement))
 (hv : validateCall s.statement=ok (.Ok ())) (route : s.data.val.length=2) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_TreeTail345.bounds (NNG_Calls345.calls env) s)=
 finish (NNG_ProjectFrames345.proofData s hd hv) env :=
 NNG_TailAssociation345.source s env hd hv route
#print axioms source
end AspisR1.NNG_FinishAssociation345
