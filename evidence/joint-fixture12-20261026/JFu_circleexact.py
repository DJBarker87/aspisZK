from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
s='''import JFu_CircleParameters
import JFu_CirclePair
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_CircleExact
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.SamplerCirclePolicy

def z0 := JFu_CircleAlgebra.nativePoint (point JFu_CircleParameters.t25)
def z1 := JFu_CircleAlgebra.nativePoint (point JFu_CircleParameters.t26)
'''
for i,z in [(25,'z0'),(26,'z1')]:
 s+=f'''theorem value{i} : F3M_CircleSource.source (encodeState JFu_Q{i}Source.block) .{'First' if i==25 else 'Second'}=ok {z} :=
  JFu_CircleAlgebra.source _ _ JFu_CircleParameters.q{i} JFu_CircleParameters.sample{i}
    JFu_CircleParameters.canon{i} JFu_CircleParameters.outside{i}
#print axioms value{i}
theorem canonical{i} : SAP_CanonicalCarrier.CanonK {z}.x ∧ SAP_CanonicalCarrier.CanonK {z}.y :=
  SAP_CircleCanonical.source _ _ _ value{i}
#print axioms canonical{i}
theorem circle{i} {{Hash : Type}} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState {'JFm_Q24Source' if i==25 else 'JFu_Q25Source'}.ratchet,hash,{i}#u8⟩ : r1_wire.SemanticTranscript Hash)
      JFu_Q{i}Source.record=ok (.Ok {z},
        (⟨encodeState JFu_Q{i}Source.ratchet,hash,{i+1}#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  try dsimp only
  simp only [FinishModel.circle_validated,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,JFu_Q{i}Source.record,bind_tc_ok]
  rw [JFu_Q{i}Source.source,bind_tc_ok]
  change (do let p ← F3M_CircleSource.source (encodeState JFu_Q{i}Source.block) .{'First' if i==25 else 'Second'}
             ok ((core.result.Result.Ok p : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),
               (⟨encodeState JFu_Q{i}Source.ratchet,hash,{i+1}#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [value{i},bind_tc_ok]
#print axioms circle{i}
'''
s+='''theorem different : z0 ≠ z1 :=
  JFu_CircleAlgebra.distinct _ _ JFu_CircleParameters.outside25 JFu_CircleParameters.outside26
    JFu_CircleParameters.different

theorem inequality : FinishModel.pointEq z0 z1=ok false :=
  JFu_CircleAlgebra.comparison _ _ different

#print axioms different
#print axioms inequality
end AspisR1.JFu_CircleExact
end
'''
f=R/'lean/JFu_CircleExact.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
