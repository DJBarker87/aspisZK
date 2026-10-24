#!/usr/bin/env python3
from pathlib import Path
import sys
S=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
rows=[('sampleBlock','','(self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8)','self row framed',[]),('semanticValidated','','(self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord)','self record1',['sampleBlock'])]
for n in [13,9,5]:rows.append(('begin'+str(n),'',f'''(prefix1 : r1_wire.Prefix) (transcript{n} : r1_wire.SemanticTranscript H)
    (val val1 val2 val{n-1} : aspis_core.field.QM31)
    (index_mut_back{n-4} : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize)''',f'prefix1 transcript{n} val val1 val2 val{n-1} index_mut_back{n-4}', ['semanticValidated']+(['begin'+str(n+4)] if n<13 else [])))
rows += [('begin','','(prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)','prefix1 transcript',['semanticValidated','begin5']),('newTranscript','','(hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize)','hash publicBytes root',[]),('publicTranscript','','(pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize)','pub hash root',['newTranscript']),('roundStep','(B : RoundModel.Boundaries)','(prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)\n    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize)','prefix1 transcript alpha running round',['semanticValidated']),('rounds','(B : RoundModel.Boundaries)','(prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)','prefix1 transcript',['roundStep']),('circleValidated','(B : FinishModel.Boundaries)','(self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord)','self record1',['sampleBlock']),('finish','(R : RoundModel.Boundaries) (B : FinishModel.Boundaries)','(pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)\n    (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)\n    (obs : Option (verifier.Phase → Result Unit))','pub prefix1 transcript challenges obs',['rounds','circleValidated']),('verify','(R : RoundModel.Boundaries) (B : FinishModel.Boundaries)','(pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)\n    (obs : Option (verifier.Phase → Result Unit))','pub bytes hash obs',['publicTranscript','begin','finish'])]
out='''import S1SemanticCodeVerifyExactV1
import S1PreparedP3ValidV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisV8R19.DuplexFrames S4SolanaDigestP3RegroupV1

'''
for name,extra,params,args,deps in rows:
 lead='B ' if name in ['roundStep','rounds','circleValidated'] else 'R B ' if name=='finish' else '(finish R B) ' if name=='verify' else ''
 out+=f'''theorem {name}_p3_valid {extra} {{H : Type}} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) {params} :
    OracleValid sha ({name} {lead}(solanaDigestP3Model copy sha) {args}) := by
  unfold {name}
  repeat' first
'''+''.join('    | (solve | with_reducible apply '+d+'_p3_valid)\n' for d in deps)+'''    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

'''
out+='\n'.join('#print axioms '+r[0]+'_p3_valid' for r in rows)+'\nend AspisR1PublicPreparation.S1SemanticCode\n'
p=S/'S1SemanticCodeP3ValidV1.lean'
if __name__=='__main__':
 if '--check' in sys.argv:assert p.read_text()==out
 else:p.write_text(out)
