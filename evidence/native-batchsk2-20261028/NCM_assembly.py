"""Generate explicit, unbundled conditional batch assembly statements."""
from pathlib import Path
import sys
from NCM_params import PARAMS,ARGS
R=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/lean'
CHECK='--check' in sys.argv
def emit(path,text):
 if CHECK:
  assert path.read_text()==text, 'generated statement drift: '+str(path)
 else:path.write_text(text)
header='''import NCM_BatchCore

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Assembly
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCM_BatchTypes
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Whole observation is a CONCLUSION only. Rejected scratch is not used as
an accepted next input, and the native rejected prefix remains in the log. -/
def Claim {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (ops : Ops) (batch : Nat) (folded : NCE_VerifierCuts.Digest)
    (s : Carrier) (parsed : OraclePortCompactDraft.Parsed) : Prop :=
  let source := NCM_BatchCore.execute D hash H ops batch folded s
  let target := NCE_FirstFailure.observe H (NCM_BatchCore.slot parsed s)
    [(batch,0),(batch,1),(batch,2)] Port4B_BatchJoin.initial
  source.1 = target.1 ∧ source.2.1 = target.2.1.map Prod.snd ∧
  source.2.2.prepared = s.prepared ∧ source.2.2.proof = s.proof ∧
  source.2.2.log = s.log++source.1 ∧
  (source.2.1 = none → source.2.2.scratch = target.2.2)

/-- Conditional same-execution batch theorem. The ONLY native hypotheses are
these 18 named NCE per-step families. The two redundant weak families remain
visible for the requested statement audit; neither is claimed discharged. -/
theorem bridge {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (oracle : ∀ input, D.digest hash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (ops : Ops) (base : Port3_NativeBatchBody.Ops)
'''
body='''
    (batch : Nat) (bb : batch < 2) (s : Carrier)
    (parsed : OraclePortCompactDraft.Parsed) (folded : NCE_VerifierCuts.Digest)
    (inputs : Inputs s parsed folded) : Claim D hash H ops batch folded s parsed := by
  have related := NCM_OuterRefinement.refinement H (NCM_BatchCore.child D hash H ops batch folded)
    (NCM_BatchCore.slot parsed s) batch (Good s) [0,1,2]
    (by
      intro kind member current good
      have kb : kind < 3 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        omega
      exact NCM_BatchCore.child_agrees D hash H oracle ops base NATIVE_ARGS
        batch bb s current parsed folded inputs good kind kb)
    (NCM_BatchCore.initial s) ⟨rfl,rfl⟩
  rw [←NCM_OuterRefinement.control ops.start ops.after0 ops.after1 ops.finish outer
    (NCM_BatchCore.child D hash H ops batch folded) (NCM_BatchCore.initial s)] at related
  rcases related with ⟨reads,first,good,log,final⟩
  exact ⟨reads,first,good.1,good.2,log,final⟩

#print Claim
#print bridge
#print axioms bridge
end AspisR1.NCM_Assembly
end
'''.replace('NATIVE_ARGS',ARGS)
emit(R/'NCM_Assembly.lean',header+PARAMS+body)
for module,batch in [('NCM_Batch',0),('NCM_U09',1)]:
 text=f'''import NCM_Assembly

set_option autoImplicit false
noncomputable section
namespace AspisR1.{module}
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCM_BatchTypes
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- {'TX1 batch 0' if batch==0 else 'TX2 U09 batch 1'}: exact accept/first-error and chronological-prefix
observation from the SAME Prepared/proof/caller; 18 explicit native step
families only, plus runtime oracle interpretation and original input facts. -/
theorem bridge {{X : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (oracle : ∀ input, D.digest hash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (ops : Ops) (base : Port3_NativeBatchBody.Ops)
'''+PARAMS+f'''
    (s : Carrier) (parsed : OraclePortCompactDraft.Parsed) (folded : NCE_VerifierCuts.Digest)
    (inputs : Inputs s parsed folded) : NCM_Assembly.Claim D hash H ops {batch} folded s parsed :=
  NCM_Assembly.bridge D hash H oracle ops base {ARGS} {batch} (by decide) s parsed folded inputs

#print bridge
#print axioms bridge
end AspisR1.{module}
end
'''
 emit(R/(module+'.lean'),text)
