"""No semantic credit from proof counts. Check exact new extraction chains."""
from pathlib import Path
import json,hashlib,re,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume14';sha=lambda b:hashlib.sha256(b).hexdigest()
previous=json.loads((D/'resume13/coverage.json').read_text());audit=json.loads((D/'resume12/identity-audit.json').read_text());inv=json.loads((D/'resume9/body-inventory.json').read_text())
for f in inv['files']:
 for k in ['source','owned']:assert sha(Path(f[k]).read_bytes())==f[k+'_sha256']
old=next(r for r in audit['bodies']if r['key']=='frontier#0');assert old['post_macro_identity']
# The lifted declaration's body is byte-for-byte unchanged, visibility only is
# outside the body. It resolves the same Digest/M31/Error/Vec and fields callee.
lift=json.loads((O/'lift-inputs.json').read_text());source=Path(lift['owned_file']).read_text();lib=Path('tools/pv-b3p6-20261028/v244-missing14/lib.rs').read_text()
r=next(r for r in lift['lifts']if r['name']=='frontier');decl=source[r['start_byte']:r['end_byte']];body=decl[decl.index('{'):]
a=lib.index('pub fn frontier');b=lib.index('{',a);depth=1;i=b+1
while depth:depth+=(lib[i]=='{')-(lib[i]=='}');i+=1
assert lib[b:i]==body and sha(body.encode())==r['body_sha256']
translation=json.loads((O/'frontier-raw/translation.json').read_text());f=next(f for f in translation['functions']if f['rust_name'].endswith('::frontier'));assert not f['is_opaque']
port=json.loads((O/'frontier-port.json').read_text());assert port['body_byte_identical']and not port['external_template_compiled']
chain=dict(key='frontier#0',previous_post_macro_audit='../resume12/identity-audit.json',post_macro_source_sha256=old['source']['expanded_body_sha256'],post_macro_owned_sha256=old['owned']['expanded_body_sha256'],owned_file_sha256=lift['owned_sha256'],lifted_body_sha256=r['body_sha256'],lifted_source_file='tools/pv-b3p6-20261028/v244-missing14/lib.rs',emission=f,raw_model_sha256=sha((O/'frontier-raw/Funs.lean').read_bytes()),port=port,evidence_class='reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)',scope='Exact body extraction with fields port explicit; Vec and fields closure are not inferred. The old caller law is not yet discharged.')
(O/'frontier-binding-chain.json').write_text(json.dumps(chain,indent=2)+'\n')
# Do not grant coverage until compilation and generation receipts are collected.
(O/'coverage-draft.json').write_text(json.dumps(dict(previous_bound=39,candidates=79,proposed_exact_body_credit=[chain],proposed_own1_credit=['transition-native-association.json'],status='DRAFT; reconcile against final receipts and target links before awarding any count'),indent=2)+'\n')
path='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_OracleBridge38.lean';ref='origin/codex/pv-runjoin-20261026';b=subprocess.check_output(['git','show',ref+':'+path]).decode();hyp=re.search(r'\(op227 : (∀ claims,[\s\S]*?)\) :',b)[1]
checks={}
for mod in ['PV_B3P_SelectedCorrected14227','PV_B3P_AllGroups14227']:
 s=(D/'lean'/(mod+'.lean')).read_text();conclusion=re.search(r'    (∀ claims,[\s\S]*?) := by',s)[1];assert hyp==conclusion;checks[mod]=sha(conclusion.encode())
(O/'runjoin-byte-check.json').write_text(json.dumps(dict(reference=ref,path=path,reference_revision=subprocess.check_output(['git','rev-parse',ref],text=True).strip(),carrier='Install227.Types base',terminal='transported_reference base',conclusion_byte_identical=checks,op227_discharged=False),indent=2)+'\n')
print(json.dumps(dict(frontier_chain=True,byte_match=list(checks))))
