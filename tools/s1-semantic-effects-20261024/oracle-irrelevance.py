#!/usr/bin/env python3
from pathlib import Path
import runpy,sys
S=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
rows=runpy.run_path(str(Path(__file__).with_name('oracle-valid.py')))['rows']
out='''import S1SemanticCodeVerifyExactV1
import S1PreparedOracleProgramLawsV1
import S1SemanticGhostDictionaryV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

'''
for name,extra,params,args,deps in rows:
 lead='B ' if name in ['roundStep','rounds','circleValidated'] else 'R B ' if name=='finish' else '(finish R B) ' if name=='verify' else ''
 out+=f'''theorem {name}_dictionary_irrelevant {extra} {{H : Type}}
    (first second : aspis_core.Digest32 H) {params} :
    oracleProgram ({name} {lead}first {args})=oracleProgram ({name} {lead}second {args}) := by
  unfold {name}
  repeat' first
'''+''.join('    | (solve | with_reducible apply '+d+'_dictionary_irrelevant)\n' for d in deps)+'''    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

'''
out+='\n'.join('#print axioms '+r[0]+'_dictionary_irrelevant' for r in rows)+'\nend AspisR1PublicPreparation.S1SemanticCode\n'
p=S/'S1SemanticCodeDictionaryV1.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
