from pathlib import Path
import sys
root=Path(__file__).resolve().parents[2]
base=(root/'lean/NBA_Materialize.lean').read_text()
defs=base[base.index('  have bw0 :='):base.index('  unfold NBA_QueryFactor.materialize')]
names=' '.join(f'{x}{i}' for x in ['b','a'] for i in range(8))
args=' '.join(f't.p{i}.{x}' for i in range(8) for x in ['block','advance'])
pairs='\n'.join(f'    (NBA_Transcript.readParts {"before" if i==0 else "t.p"+str(i-1)+".advance"} 1#u8,t.p{i}.block),\n    (NBA_Transcript.readParts {"before" if i==0 else "t.p"+str(i-1)+".advance"} 2#u8,t.p{i}.advance)' + (',' if i<7 else '') for i in range(8))
# only proof let abbreviations; no new theorem premise
letdefs='\n'.join(f'  let b{i} := t.p{i}.block\n  let a{i} := t.p{i}.advance' for i in range(8))
calls='\n'.join(f'  have hb{i} := t.p{i}.readCall\n  have ha{i} := t.p{i}.advanceCall' for i in range(8))
callsn=' '.join(f'h{j}{i}' for i in range(8) for j in ['b','a'])
stores=', '.join(f'{j}{i}' for j in ['bw','aw','ar'] for i in range(8))
s='''import NBL_RunStep
import NBL_QueryEffectFactor
import NBL_HashReplay
import NBL_MaterialTrace
set_option autoImplicit false
namespace AspisR1.NBL_MaterialHashReplay
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NBL_CodeRunLaws

def log {H : Type} {D : aspis_core.Digest32 H} {hash : H} {before : NBL_MaterialTrace.Bytes32}
    (t : NBL_MaterialTrace.Trace D hash before) : NBL_BlockTrace.Log :=
  [
'''+pairs+''']

theorem source {H : Type} (D : aspis_core.Digest32 H) (hash : H) (before : NBL_MaterialTrace.Bytes32)
    (t : NBL_MaterialTrace.Trace D hash before) :
    run (NBL_QueryEffectFactor.materialize D hash before)=
      (NBL_HashReplay.events D hash (log t),ok (t.blocks,t.advances)) := by
'''+letdefs+'\n'+calls+'\n'+defs+'''
  simp only [NBA_Transcript.readParts] at '''+callsn+'''
  unfold NBL_QueryEffectFactor.materialize
  simp only [NBL_HashReplay.events,log,List.map_cons,List.map_nil]
  repeat' first
    | (apply NBL_RunStep.lift_ok; first | assumption | rfl)
    | (apply NBL_RunStep.digest_ok; assumption)
    | (rw [aw0])
    | exact pure_run _

#print axioms source
end AspisR1.NBL_MaterialHashReplay
'''
# proof defs originally use 'state' not 'before'
s=s.replace('NBA_Transcript.readParts state','NBA_Transcript.readParts before')
p=root/'lean/NBL_MaterialHashReplay.lean'
if '--check' in sys.argv: assert p.read_text()==s
else: p.write_text(s)
