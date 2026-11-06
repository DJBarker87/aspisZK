from pathlib import Path
import json,lzma,base64,hashlib
B=Path.cwd();D=B/'NJX_audit_gate2/proof33';s=(D/'stdout.log').read_text();results=[json.loads(l[11:])for l in s.splitlines()if l.startswith('NEP_RESULT ')]
assert len(results)==224
bad=[x for x in results if not x['equal']];assert len(bad)==1 and bad[0]['root']=='NHC_DecodeModel.decoder_error' and bad[0]['collect_axioms']==[] and set(bad[0]['walked_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for x in results)
assert json.loads((B/'NJX_L140/receipt.json').read_text())['exit_status']==1
artifacts=[]
for q in B.glob('NEP_proof33_*'):
 if q.is_file()and q.suffix in ['.txt','.json']:
  raw=q.read_bytes();packed=lzma.compress(raw);assert lzma.decompress(packed)==raw;h=hashlib.sha256(raw).hexdigest();(D/(q.name+'.xz.b64.txt')).write_text(base64.b64encode(packed).decode());(D/(q.name+'.sha256')).write_text(h+'\n');artifacts.append(dict(name=q.name,bytes=len(raw),sha256=h,compressed_bytes=len(packed)));q.unlink()
x=dict(status='RAW_STANDARD_WITH_COLLECTOR_DISAGREEMENT',original_scope='NJX_L140',original_scope_exit_status=1,recovery_scope='NJX_L149',rerun=False,standard_only=True,results=results,collect_axioms_disagreements=bad,raw_artifacts=artifacts,ruling='C3 ax2 raw walk authoritative; exact known NJO disagreement retained; original wrapper failure not relabelled')
(D/'raw_recovery_receipt.json').write_text(json.dumps(x,indent=1));print('Recovered existing proof33 raw diagnostics; no theorem rerun; original L140 exit1 retained')
