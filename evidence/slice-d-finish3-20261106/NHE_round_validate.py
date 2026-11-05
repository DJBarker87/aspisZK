from pathlib import Path
import json,runpy,re,subprocess
E=Path(__file__).resolve().parent
x=runpy.run_path(str(E/'NHE_polynomial_validate.py'));gate=x['gate'];pin=x['pin'];inputs=x['inputs'];M=x['M'];P=x['P']
pairs=[[gate(M,'NGM_K098',True),gate(M,'NGM_K099',False)]]
for i in [95,97]:pairs.append([gate(P,f'NGW_K{i:03d}',True),gate(P,f'NGW_K{i+1:03d}',False)])
for base,ns in [(M,['NGM_RoundScale.lean','NGM_HELPER_ERASURE.json','NGM_DOMAIN.md']),(P,['NGW_HelperRef/Funs.lean','NGW_E001/receipt.json'])]:
 for n in ns:pin(base/n)
code=json.loads((M/'NGM_NATIVE_INPUTS.json').read_text())['crates/aspis-r1-cost-probe/src/NGM_helpers.rs']
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
def body(s,n):
 a=s.index('fn '+n+'(');b=s.index('{',a);d=1;c=b+1
 while d:d+=(s[c]=='{')-(s[c]=='}');c+=1
 return s[a:c]
norm=lambda s:re.sub(r'\s+','',s)
actual=body(frozen,'finish_relation_round');ref=body(code,'source_round')
erased=ref.replace('source_round','finish_relation_round').replace(',log:&mut RoundLog','').replace('scale(claim,QUARTER,log)','claim.mul_m31(QUARTER)').replace('polynomial_reply(poly,alpha,log)','polynomial(poly,alpha)')
assert norm(erased)==norm(actual)
(E/'NHE_frozen_round.rs.txt').write_text(actual+'\n');pin(E/'NHE_frozen_round.rs.txt')
(E/'NHE_INPUT_INDEX.json').write_text(json.dumps(inputs,indent=2)+'\n')
(E/'NHE_ROUND_VALIDATION.json').write_text(json.dumps(dict(status='PASS',native_pairs=pairs,source_erasure='exact whole source_round modulo only named opaque scale/polynomial calls',reference='NGW_HelperRef.round_ref; NHE_RoundRef.observed',deployed_dictionary='AspisR1.IDa_Deployed.finish reservation',lean_root='NHE_Round.cohort',domain='canonical alpha; arbitrary claim and byte slice; round<2; exact errors and runtime failures retained',next_claim_domain='NHE_PolynomialDomain.source',new_kani_runs=0,no_success_premise=True),indent=2)+'\n')
print('PASS round pairs',len(pairs))
