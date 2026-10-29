"""Split the projected caller into a selector prefix and four named continuations.
No arithmetic is reduced; all generated text is copied from the pinned emission.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';raw=(D/'raw227-composition-resume5/Funs.lean').read_text()
name='reference_poseidon.evaluate_state_only_poseidon_oracle_projected'
decl=re.search(r'^def '+re.escape(name)+r'\s*\n[\s\S]*?(?=^/--|\Z)',raw,re.M)[0].strip()
head,body=decl.split(':= do',1);lines=body.splitlines();starts=[next(i for i,x in enumerate(lines)if re.match(r'  let start'+str(k if k else '')+r' ←',x))for k in range(4)]
outputs=['q32','q47','q62','q77'];shared='(openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier)'
args='openings leading full internal pqm pqm1 pqm2 prepared_block'
header='''import PV_B3P_P227_14
import PV_B3P_Operations12227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding12227 Result
set_option autoImplicit false
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub
  aspis_core.field.QM31.mul reference_field.qm31_pack_base4
  reference_field.qm31_sum_products3_prepared reference_field.PreparedQm31Multiplier.mul
  reference_field.PreparedQm31Multiplier.new reference_poseidon.interpolated_full_pair_packed
  reference_poseidon.interpolated_internal_pair reference_poseidon.leading_pair_packed
'''
records=[]
# suffixes preserve prior values and their order explicitly
for k in range(3,-1,-1):
 chunk='\n'.join(lines[starts[k]:starts[k+1]if k<3 else len(lines)])
 prev=' '.join(outputs[:k]);pars=shared+(f' ({prev} : aspis_core.field.QM31)'if prev else '')
 if k<3:chunk+='\n  projected_stage13_'+str(k+1)+' '+args+' '+' '.join(outputs[:k+1])
 mod='PV_B3P_ProjectedStage13'+str(k)+'227';s=header
 if k<3:s='import PV_B3P_ProjectedStage13'+str(k+1)+'227\n'+s
 s+='def projected_stage13_'+str(k)+' '+pars+' : Result (Array aspis_core.field.QM31 4#usize) := do\n'+chunk+'\n'
 s+='end PV_B3P_Binding13227\n';(L/(mod+'.lean')).write_text(s)
 records.append(dict(module=mod,stage=k,source_chunk_sha256=hashlib.sha256(chunk.encode()).hexdigest()))
prefix='\n'.join(lines[:starts[0]])
prefix=prefix.replace('reference_poseidon.leading_pair_packed openings','operation openings')
pars='(operation : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings → Result (Array aspis_core.field.QM31 4#usize)) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors)'
s='import PV_B3P_ProjectedStage130227\n'+header+'def projected_prefix13 '+pars+' : Result (Array aspis_core.field.QM31 4#usize) := do\n'+prefix+'\n  projected_stage13_0 '+args+'\n'
s+='''theorem projected_prefix_leading13
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    projected_prefix13 reference_poseidon.leading_pair_packed openings selectors =
      projected_prefix13 source_leading12 openings selectors :=
  congrArg (fun operation => projected_prefix13 operation openings selectors) leading_operation12
#print axioms projected_prefix_leading13
end PV_B3P_Binding13227
'''
(L/'PV_B3P_ProjectedPrefix13227.lean').write_text(s)
# Rejected whole-body Bridge route (66637) is never emitted.
# projected_raw227_resume13.py emits the accepted named-bind bridge.
(D/'resume13/projected-stages.json').write_text(json.dumps(dict(declaration_sha256=hashlib.sha256(decl.encode()).hexdigest(),stages=records,method='exact text segmentation; arithmetic locally irreducible; unchanged default recursion'),indent=2)+'\n')
