import NNG_DecodeAssociation345
import NNG_PrefixEquations345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreludeAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136
abbrev LogicalDecoded := NNG_Phases345.Decoded LIB_Instances.VL LIB_Instances.C

def canonical (s : NNG_Phases345.Parent)
 (tail : LogicalDecoded → RSL.Obs (Except RSL.ProgramError RSL.Bytes)) :=
 NNG_Phases345.stepDistinct s fun s=>
 NNG_Phases345.stepReadonlyProof s fun s=>
 NNG_Phases345.stepReadonlyPublic s fun s=>
 NNG_Phases345.stepCheckpoint (fun _=>true) s fun s=>
 NNG_Phases345.stepCheckpointData (fun _=>true) s fun s=>
 NNG_Phases345.stepZero s fun s=>
 NNG_Phases345.stepPublicData (fun _=>true) s fun s=>
 NNG_Phases345.stepDecode LIB_Instances.VL LIB_Instances.C (fun _=>true) s tail

theorem source {W : Type} (s : Selected W) (env : RSL.Env)
 (next : Decoded W → Code Ret) (tail : LogicalDecoded → RSL.Obs (Except RSL.ProgramError RSL.Bytes))
 (later : ∀ ck pub st (hd : decodeCall pub=ok (.Ok st)),
  observation NNG_ChildSource345.port (NNG_Events345.events env) (next ⟨⟨⟨s,ck⟩,pub⟩,st⟩)=
   tail (NNG_ProjectFrames345.decoded ⟨⟨⟨s,ck⟩,pub⟩,st⟩ hd)) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_TreeBase345.prelude (NNG_Calls345.calls env) s next)=
 canonical (NNG_ProjectFrames345.selected s) tail := by
 unfold NNG_TreeBase345.prelude canonical NNG_Phases345.stepDistinct
 rw [← NNG_PrefixEquations345.distinct s env]
 apply NNG_TryAssociation345.source id
 intro u _
 cases u
 unfold NNG_Phases345.stepReadonlyProof
 rw [← NNG_PrefixEquations345.readonly s.proofAccount env]
 apply NNG_TryAssociation345.source id
 intro u _
 cases u
 unfold NNG_Phases345.stepReadonlyPublic
 rw [← NNG_PrefixEquations345.readonly s.publicAccount env]
 apply NNG_TryAssociation345.source id
 intro u _
 cases u
 unfold NNG_Phases345.stepCheckpoint
 rw [← NNG_PrefixEquations345.checkpoint s.checkpointAccount s.program env]
 apply NNG_TryAssociation345.source id
 intro u _
 cases u
 unfold NNG_Phases345.stepCheckpointData
 rw [← NNG_PrefixEquations345.data s.checkpointAccount env]
 apply NNG_TryAssociation345.source (fun b : Slice U8=>LIB_Carriers.bytes b)
 intro ck _
 unfold NNG_Phases345.stepZero
 rw [← NNG_PrefixEquations345.zero ck env]
 apply NNG_TryAssociation345.source id
 intro u _
 cases u
 unfold NNG_Phases345.stepPublicData
 rw [← NNG_PrefixEquations345.data s.publicAccount env]
 apply NNG_TryAssociation345.source (fun b : Slice U8=>LIB_Carriers.bytes b)
 intro pub _
 exact NNG_DecodeAssociation345.source ⟨⟨s,ck⟩,pub⟩ env next tail (later ck pub)
#print axioms source
end AspisR1.NNG_PreludeAssociation345
