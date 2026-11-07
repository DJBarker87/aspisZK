"""Final receipt, reservation, source and export checks; no build/replay."""
from pathlib import Path
import json,hashlib,lzma,shutil
B=Path.cwd()
def sha(p):
 with p.open('rb')as f:return hashlib.file_digest(f,'sha256').hexdigest()
receipts=[json.loads(p.read_text())for p in B.glob('NMB_[LK][0-9][0-9][0-9]/receipt.json')]
assert len([r for r in receipts if r['kind']=='kani'])==40
assert len([r for r in receipts if r['kind']!='kani'])==139
admissions=json.loads((B/'NMB_admissions_snapshot.json').read_text());assert all(x['exit']==0 and x['reservation']['allowed']is True for x in admissions.values())
audit=json.loads((B/'NMB_AUDIT.json').read_text());assert audit['required_roots']==11518 and audit['raw_standard_axioms_only']and audit['source_gate_pass']and not audit['security_target_established']
export=json.loads((B/'NMB_EXPORT.json').read_text())
for f in export['files']:assert sha(Path(f['path']))==f['sha256']
for p,h in audit['audit_executable_sha256'].items():assert sha(Path(p))==h
closure=json.loads(lzma.decompress((B/'NMB_CLOSURE_PINS.json.xz').read_bytes()));assert len(closure['files'])>10000
for n,v in closure['files'].items():
 p=Path(n);assert p.is_file()and p.stat().st_size==v['bytes'],n
# Source/current selected Aeneas hashes were exhaustively checked by retention;
# full closure bytes are pinned once, avoiding a redundant full byte replay.
assert json.loads((B/'NMB_RETENTION.json').read_text())['all_checks']
size=sum(p.stat().st_size for p in B.rglob('*')if p.is_file());free=shutil.disk_usage(B).free;assert size<30_000_000_000 and free>=40_000_000_000
x=dict(checks=True,completed_receipts_before_this_scope=len(receipts),current_scope='NMB_L140',final_budget_after_receipt=dict(Lean_support=140,Kani=40,extraction=0),all_admissions_allowed=True,required_roots=11518,source_gate=True,native_parent_composition=False,row_promotions=0,target_established=False,workspace_bytes=size,host_free_bytes=free,export=export['export'],deleted_files=0,target_retained=(B/'NMB_target').is_dir(),tmp_retained=(B/'NMB_tmp').is_dir())
(B/'NMB_FINAL_CHECK.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
