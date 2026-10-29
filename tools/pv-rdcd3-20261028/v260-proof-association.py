"""Fail closed unless every concrete V260 proof source has a matching PASS.
The file records a source/Result evidence class only; it cannot grant endpoint,
binary or observer credit and does not relabel historical pin tools as checkers.
"""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd3-20261028'
required=['RangeFold','RangeLoop','Range194','OrderedFold','Index194','ReadHoist','Word194','WordAll194','Control194','V260Bounds','V260RowSource','V260RowRange','V260RowResult','V260Folds','V260Owned','V260Exact','V260','V260C_Rows','V260C_Folds','V260C_Owned','V260C_Exact','V260Callback','V260Complete']
receipts=[]
for p in E.glob('lean-*/receipt.json'):
 j=json.loads(p.read_text())
 if j['exit']==0:receipts.append((p,j))
matched={}
for short in required:
 m='R1Z/PV_RDCD3_'+short
 hits=[(p,j) for p,j in receipts if j['module']==m]
 assert hits,('missing PASS',m)
 p,j=hits[-1];s=R/j['source_path']
 assert hashlib.sha256(s.read_bytes()).hexdigest()==j['source_sha256'],m
 assert j['swap']=='0' and j['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),m
 assert j['axioms'] and all('sorryAx' not in a for a in j['axioms']),m
 assert all(x in j for x in ['target','exit','wall','peak_rss_kib','source_revision','dependencies_sha256']),m
 matched[m]=dict(receipt=str(p.relative_to(E)),receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_sha256=j['source_sha256'],axioms=j['axioms'])
for native in ['range-library-native','v260-source-static']:
 j=json.load(open(E/native/'receipt.json'));assert j['exit']==0 and j['swap']=='0',native
j=dict(row='V260',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),proofs=matched,class_scope='Complete Result source API and selected callback value carrier only',native_link_evidence_class='structural (K-1 substitute); reclassification within existing Rust/Aeneas/compiler trust',endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[],retained=['E1/E2','real native RunJoin/carrier/world','client proof-account route','L1/L2/L3','T exactly entropy_law, entropy_kernel, observation'],requires_final_dag='v260-fingerprint-result.json and current source/static gate hashes; the final combined axioms audit and focused row replay remain mandatory')
(E/'v260-proof-association.json').write_text(json.dumps(j,indent=2)+'\n')
print('Every required V260 proof source has a capped matching PASS and standard-axiom receipt')
