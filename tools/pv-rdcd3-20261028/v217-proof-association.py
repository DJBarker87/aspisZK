"""Associate complete source model/Result proof with capped successful receipts.
This never grants binary, observer, native RunJoin or endpoint premise credit.
"""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd3-20261028'
pins=json.load(open(E/'v217-source-resolution.json'));passed=[]
for p in E.glob('lean-*/receipt.json'):
 j=json.loads(p.read_text())
 if j['exit']==0:passed.append((p,j))
matched={}
for module,pin in pins['modules'].items():
 hits=[(p,j) for p,j in passed if j['module']==module.replace('.','/') and j['source_sha256']==pin['sha256']]
 assert hits,('no matching successful source',module)
 p,j=hits[-1];source=R/j['source_path'];assert hashlib.sha256(source.read_bytes()).hexdigest()==pin['sha256']
 assert j['swap']=='0' and j['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
 assert all(x in j for x in ['target','exit','wall','peak_rss_kib','source_revision','dependencies_sha256'])
 for line in j['axioms']:assert 'sorryAx' not in line
 matched[module]=dict(receipt=str(p.relative_to(E)),receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_sha256=j['source_sha256'],axioms=j['axioms'])
for name in ['v217-source-check','v217-final-source']:
 j=json.load(open(E/name/'receipt.json'));assert j['exit']==0 and j['swap']=='0',name
j=dict(row='V217',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),proofs=matched,native_link_evidence_class='structural (K-1 substitute)',scope='Complete deployed source-value/Result association, all typed inputs, no success/canonicality hypotheses added',composition='Aeneas/Rust semantic agreement is reclassification within existing tool trust, never premise removal',before='The complete deployed selected-mask source-to-owned-reference Result equality and concrete library-body transport were unestablished.',after='For all c1:Array QM31 16, mask:Array QM31 10, g:QM31, point:Array QM31 10, the structurally bound source model returns exactly the owned reference Result (including fail/div). This is PV_RDCD3_V217.complete, using MaskRootEq.reference.',unchanged=['input quantifiers','Result carrier, failure/divergence and conclusion','T exactly entropy_law, entropy_kernel, observation'],retained=['V370 compiler preservation and D381/D386 compiler-cohort boundary','E1/E2','real native RunJoin/carrier/world','client proof-account route','L1/L2/L3 and binary/physical observer','panic diagnostics and runtime effects outside source-value projection'],endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[],final_requirement='Combined statement/axioms audit and focused replay under the final frozen closure remain mandatory')
(E/'v217-proof-association.json').write_text(json.dumps(j,indent=2)+'\n');print(len(matched),'required source models/proofs have coherent successful capped receipts')
