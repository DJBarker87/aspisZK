#!/usr/bin/env python3
import hashlib, json, pathlib, re, sys
ROOT=pathlib.Path(__file__).resolve().parent
REPO=ROOT.parents[4]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok: raise SystemExit('FAIL: '+msg)
m=json.loads((ROOT/'manifest.json').read_text())
require(m.get('schema')=='focused-extractor-proof-packet-v1','schema')
require(len(m.get('modules',[]))==1,'expected one module')
mod=m['modules'][0]
src=ROOT/mod['source']; obj=ROOT/mod['object']
require(src.is_file() and sha(src)==mod['source_sha256'],'module source hash')
require(obj.is_file() and sha(obj)==mod['object_sha256'],'module object hash')
for key in ['receipt','preflight','command']:
    require((ROOT/mod[key]).is_file(),f'missing {key}')
for name in m['evidence_files']:
    require((ROOT/name).is_file(),f'missing evidence {name}')
for name,pin in m['direct_import_source_map'].items():
    sp=pathlib.Path(pin['source_path'])
    if not sp.is_absolute(): sp=REPO/sp
    op=pathlib.Path(pin['selected_object_path'])
    require(sp.is_file() and sha(sp)==pin['source_sha256'],f'{name} source hash')
    require(op.is_file() and sha(op)==pin['object_sha256'],f'{name} object hash')
    rp=REPO/pin['producer_record']
    require(rp.is_file() and sha(rp)==pin['producer_record_sha256'],f'{name} producer record hash')
text=src.read_text()
for theorem in m['theorems']:
    require(re.search(r'\btheorem\s+'+re.escape(theorem)+r'\b',text) is not None,f'missing theorem {theorem}')
require(not re.search(r'\bsorry\b|\badmit\b',text),'sorry/admit in source')
log=(ROOT/'evidence/lean.log').read_text()
for ax in m['modules'][0]['axioms']:
    require(ax in log,f'axiom audit missing {ax}')
require('sorryAx' not in log,'sorryAx in axiom audit')
require(m['modules'][0]['exit_status']==0,'nonzero exit')
print('PASS: S4 tx2 resume-to-twelve actual-call packet hashes, producer pins, theorem inventory, and axiom logs verified')
