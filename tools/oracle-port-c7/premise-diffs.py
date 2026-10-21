#!/usr/bin/env python3
"""Generate type-checked fibre adapters and deletion-only signature diffs."""
from pathlib import Path
import difflib,json
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
E=BASE/'evidence/oracle-port-draft-20261021'
header='''import OraclePortStoredConsumerC7

/-! Controlled same-carrier premise deletion audit. The normalization from
v3's pure pair carrier to fixed stored-input fibres is a separate change.
These adapters do not claim source equality with frozen Rust. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortPremiseDeletionC7
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortStoredReductionC7 OraclePortStoredConsumerC7
open RecordedBinaryExperimentBin (SourceInputs)
open RawRecordedOracleExtractionMassBin

'''
common='''    (D : LiteralByteProtocol.Decoder) (s : Bytes) (P : OraclePortStoredExperimentC4.Prover)
    (Q : Nat) (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (source : (Bytes → State) → SourceInputs)
'''
guard='''    (h_R16_instance : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
      OraclePortAdmission.InstanceFields D (dV s) (pairProver s P) H (source H))
'''
base='''    ({name} : ∀ H,
      ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
        (eval H (OraclePortExperiment.recorded D (dV s) (pairProver s P))) →
      FS2.accepts (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))) →
{body})
'''
rows='OraclePortConsumer.compiledRows D (dV s) (pairProver s P) H'
items=[('h_R16_instance',guard)]
items += [(name,base.format(name=name,body=body)) for name,body in [
('h_R13',f'      LiteralMatchingData.read ({rows}) = some (source H).data'),
('h_R14_backend',f'''      LiteralPairingChecks.checks ({rows}) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho)'''),
('h_R15_writer','''      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j)'''),
('h_R3_semantic',f'''      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        ({rows}) (source H).data'''),
('h_Rwire_tag','''      (eval H (OraclePortExperiment.original D (dV s) (pairProver s P))).2.1.1.tag = 2''')]]
conclusion='''    CleanAcceptedModel D (OraclePortExperiment.recorded D (dV s) (pairProver s P)) (bad Q)'''
proof=''' :=
  OraclePortStoredConsumerC7.fibre_clean D s P Q hqueries

'''
sigs=[];decls=[]
for n in range(len(items)+1):
    sig=common+''.join(t for _,t in items[n:])+ ' :\n'+conclusion+'\n'
    sigs.append(sig)
    decls.append(f'theorem model_stage{n}\n'+sig.rstrip()+proof)
for n,(name,_) in enumerate(items):
    d=''.join(difflib.unified_diff(sigs[n].splitlines(True),sigs[n+1].splitlines(True),fromfile='before',tofile='after'))
    assert not any(l.startswith('+') and not l.startswith('+++') for l in d.splitlines()),name
    (E/f'OraclePortC7-delete-{name}.diff').write_text(d)
    (E/f'OraclePortC7-{name}-verbatim.lean.txt').write_text(items[n][1])
# The source witness is also no longer used after all model premises are gone.
final=sigs[-1].replace('    (source : (Bytes → State) → SourceInputs)\n','')
decls.append('theorem model_without_source\n'+final.rstrip()+proof)
(E/'OraclePortC7-delete-source.diff').write_text(''.join(difflib.unified_diff(sigs[-1].splitlines(True),final.splitlines(True),fromfile='before',tofile='after')))
(BASE/'lean/OraclePortPremiseDeletionC7.lean').write_text(header+''.join(decls)+''.join(f'#print axioms model_stage{n}\n' for n in range(len(items)+1))+'#print axioms model_without_source\nend AspisR1.OraclePortPremiseDeletionC7\nend\n')
(E/'OraclePortC7-premise-audit.json').write_text(json.dumps({'scope':'Type-checked fixed-fibre model adapters; carrier normalization and the new Rust/runtime joins are separate from these deletion-only diffs.','deletions':[name for name,_ in items]+['source'],'module':'OraclePortPremiseDeletionC7'},indent=2)+'\n')
