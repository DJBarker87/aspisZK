import NNG_MiddleAssociation345
import NNG_FinishAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_MiddleFixed345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136
abbrev LogicalDecoded := NNG_Phases345.Decoded LIB_Instances.VL LIB_Instances.C

def middle (d : LogicalDecoded) (env : RSL.Env) : RSL.Obs (Except RSL.ProgramError RSL.Bytes) :=
 NNG_Phases345.stepValidate LIB_Instances.VL LIB_Instances.C d fun v=>
 NNG_Phases345.stepEncode LIB_Instances.VL LIB_Instances.C v fun c=>
 NNG_Phases345.stepProofData LIB_Instances.VL LIB_Instances.C (fun _=>true) c
  (fun p=>NNG_FinishAssociation345.finish p env)

theorem source {W : Type} (s : Decoded W) (env : RSL.Env)
 (hd : decodeCall s.publicData=ok (.Ok s.statement)) (route : s.data.val.length=2) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_TreeBase345.middle (NNG_Calls345.calls env) s (NNG_TreeTail345.bounds (NNG_Calls345.calls env)))=
 middle (NNG_ProjectFrames345.decoded s hd) env := by
 exact NNG_MiddleAssociation345.source s env hd (NNG_TreeTail345.bounds (NNG_Calls345.calls env))
  (fun p=>NNG_FinishAssociation345.finish p env)
  (fun hv candidate proof=>NNG_FinishAssociation345.source ⟨⟨s,candidate⟩,proof⟩ env hd hv route)
#print axioms source
end AspisR1.NNG_MiddleFixed345
