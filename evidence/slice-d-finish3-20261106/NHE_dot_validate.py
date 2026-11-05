from pathlib import Path
import json,runpy,re,subprocess
E=Path(__file__).resolve().parent
x=runpy.run_path(str(E/'NHE_round_validate.py'));gate=x['gate'];pin=x['pin'];inputs=x['inputs'];M=x['M'];P=x['P']
pairs=[]
for i in range(55,83,2):pairs.append([gate(M,f'NGM_K{i:03d}',True),gate(M,f'NGM_K{i+1:03d}',False)])
pairs.append([gate(P,'NGW_K099',True),gate(P,'NGW_K100',False)])
for base,ns in [(M,['NGM_DotABI.lean','NGM_DotInduction.lean','NGM_RawWords.lean','NGM_NATIVE_INPUTS.json']), (P,['NGW_DotCodec.lean','NGW_DotStep.lean','NGW_DotRef/Funs.lean','NGW_DotRef/Types.lean','NGW_E003/receipt.json'])]:
 for n in ns:pin(base/n)
source=json.loads((M/'NGM_NATIVE_INPUTS.json').read_text())['crates/aspis-r1-cost-probe/src/NGM_dot.rs']
norm=lambda s:re.sub(r'\s+','',s)
assert 'letvalue=recorded_field(final_message,*j,log);letscalar=recorded_weight(weights,*j,log);recorded_push(dot,value,scalar,log).map_err(|_|Error::Parse)?;*j+=1;Ok(())'in norm(source)
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
a=frozen.index('fn finish_query_dot(');b=frozen.index('{',a);depth=1;c=b+1
while depth:depth+=(frozen[c]=='{')-(frozen[c]=='}');c+=1
actual=frozen[a:c];assert 'dot.push(field(final_message,j),weights[j]).map_err(|_|Error::Parse)?;j+=1;'in norm(actual)
(E/'NHE_frozen_dot.rs.txt').write_text(actual+'\n');pin(E/'NHE_frozen_dot.rs.txt')
(E/'NHE_INPUT_INDEX.json').write_text(json.dumps(inputs,indent=2)+'\n')
(E/'NHE_DOT_VALIDATION.json').write_text(json.dumps(dict(status='PASS',native_pairs=pairs,lean_root='NHE_DotDeployed.cohort',domain='arbitrary byte slice; arbitrary weights with length<=64; includes scalar/count/error branches; caller has exactly64 canonical weights',parser='NHE_DotRead.field/weight on SAME bytes/index/nominal carrier',state='typed fields NHE_DotState.toPush; NGW_DotCodec and NHE_DotDomain.step ensure native nine-word/count ABI only on reached count<=64',new_packet='NHE_DotState.new; inherited Q constructor',finish_packet='NHE_DotFinish.native/cohort; inherited NFE_NEI_PublicDotFinishValues.source on SAME final sums/count',push_packet='NHE_PrivateDot.cohort; NHE_PublicDot.cohort; NHE_DotRaw.raw',induction='NHE_DotLoop.decreases/cohort; complete Result and error prefix',no_success_premise=True,new_kani_runs=0),indent=2)+'\n')
print('PASS dot pairs',len(pairs))
