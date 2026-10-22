#!/usr/bin/env python3
import hashlib, json, pathlib, re
ROOT=pathlib.Path(__file__).resolve().parent
REPO=ROOT.parents[4]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok: raise SystemExit('FAIL: '+msg)
m=json.loads((ROOT/'manifest.json').read_text())
require(m.get('schema')=='focused-extractor-proof-packet-v1','schema')
require(len(m.get('modules',[]))==1,'one module expected')
mod=m['modules'][0]
src=ROOT/mod['source']; obj=ROOT/mod['object']
require(src.is_file() and sha(src)==mod['source_sha256'],'module source hash')
require(obj.is_file() and sha(obj)==mod['object_sha256'],'module object hash')
for k in ('receipt','preflight','command'):
    require((ROOT/mod[k]).is_file(),f'missing module {k}')
r=json.loads((ROOT/mod['receipt']).read_text())
pre=json.loads((ROOT/mod['preflight']).read_text())
require(r['exit_status']==0 and r['object_sha256']==mod['object_sha256'],'successful object receipt')
require(r['source_sha256_before']==r['source_sha256_after']==mod['source_sha256'],'source unchanged through compile')
require(r['source_revision_at_launch']==mod['source_revision'],'launch revision')
require(r['swap_bytes']==0 and r['peak_rss_bytes']==mod['peak_rss_bytes'],'resource receipt')
require(pre['source_sha256']==mod['source_sha256'] and pre['source_revision_at_launch']==mod['source_revision'],'preflight pins')
for name,pin in m['direct_import_source_map'].items():
    sp=pathlib.Path(pin['source_path']); sp=sp if sp.is_absolute() else REPO/sp
    op=pathlib.Path(pin['selected_object_path'])
    rp=REPO/pin['producer_record']
    require(sp.is_file() and sha(sp)==pin['source_sha256'],f'{name} source')
    require(op.is_file() and sha(op)==pin['object_sha256'],f'{name} selected object')
    require(rp.is_file() and sha(rp)==pin['producer_record_sha256'],f'{name} producer record')
text=src.read_text()
for theorem in m['theorems']:
    require(re.search(r'\btheorem\s+'+re.escape(theorem)+r'\b',text),f'missing theorem {theorem}')
require('candidate_query_success_field_evidence' in text,'candidate call field evidence constructor')
require('CandidateQueryFieldEvidence rest proof p a0 g claimPowers' in text,'same-call evidence conclusion')
require('sorry' not in text and 'admit' not in text,'sorry/admit')
log=(ROOT/'evidence/lean.log').read_text()
for ax in mod['axioms']:
    require(ax in log,f'axiom audit missing {ax}')
require('sorryAx' not in log,'sorryAx')
for name in m['evidence_files']:
    require((ROOT/name).is_file(),f'missing evidence {name}')
for line in (ROOT/'SHA256SUMS').read_text().splitlines():
    digest,rel=line.split('  ',1); require(sha(ROOT/rel)==digest,f'checksum {rel}')
print('PASS: tx2 candidate same-call field-evidence packet hashes, producer pins, receipts, theorem inventory, and axioms')
