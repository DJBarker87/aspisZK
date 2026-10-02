#!/usr/bin/env python3
"""Offline saved-evidence integrity checker for R378."""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
FOUNDATIONS={"propext","Classical.choice","Quot.sound"}
def sha(p:Path)->str: return hashlib.sha256(p.read_bytes()).hexdigest()
def req(ok:bool,msg:str):
    if not ok: raise SystemExit("FAIL: "+msg)
def j(p:Path): return json.loads(p.read_text())
inv=j(HERE/'inventory.json')
tgt=REPO/inv['target']['repository_path']; copy=HERE/inv['target']['evidence_copy']
req(tgt.is_file() and sha(tgt)==inv['target']['sha256'], 'promoted target hash')
req(tgt.read_bytes()==copy.read_bytes(), 'promoted target is not byte-identical to saved source')
run=inv['successful_run']; source=HERE/run['source']; log=HERE/run['log']; receipt=HERE/run['receipt']
r=j(receipt)
req(sha(source)==run['source_sha256']==r['source_sha256'], 'run source hash')
req(sha(log)==run['log_sha256'], 'run log hash')
req(sha(receipt)==run['receipt_sha256'], 'receipt hash')
for k in ('exit_status','wall_time','peak_rss_kib','swaps','source_revision','resources','measurement_boundary','complete_print_axioms'):
    req(run[k]==r[k], f'receipt/inventory {k}')
req(run['exit_status']==0 and run['swaps']==0, 'successful status and swap')
txt=log.read_text(errors='replace')
req(f"Elapsed (wall clock) time (h:mm:ss or m:ss): {run['wall_time']}" in txt, 'GNU time wall')
req(f"Maximum resident set size (kbytes): {run['peak_rss_kib']}" in txt, 'GNU time RSS')
req(f"Swaps: {run['swaps']}" in txt and f"Exit status: {run['exit_status']}" in txt, 'GNU time swap/status')
printed=re.findall(r"^'([^']+)' depends on axioms: \[(.*?)\]$",txt,re.M)
req(len(printed)==5==len(run['complete_print_axioms']), 'five complete axiom reports')
actual=[f"'{name}' depends on axioms: [{axioms}]" for name,axioms in printed]
req(actual==run['complete_print_axioms'], 'axiom report text')
req(all(set(a.strip() for a in ax.split(','))==FOUNDATIONS for _,ax in printed), 'green axioms exceed standard foundations')
req([n.rsplit('.',1)[-1] for n,_ in printed]==inv['theorems'], 'reported theorem names')
runner=HERE/inv['runner']['path']; req(sha(runner)==inv['runner']['sha256']==r['runner_sha256'], 'runner hash')
for key in ('direct_local_import','transitive_local_import'):
    dep=inv[key]; depfile=HERE/dep['evidence_copy']; repo_file=REPO/dep['repository_path']
    req(sha(depfile)==dep['sha256'] and sha(repo_file)==dep['sha256'], key+' hash')
# Confirm dependency chain is exactly the recorded R376 -> R374 path.
req('import AspisV8R19.R376SimplePointDegree' in copy.read_text(), 'R378 direct import declaration')
req('import AspisV8R19.R374SingleCoordinateDegree' in (HERE/inv['direct_local_import']['evidence_copy']).read_text(), 'R376 transitive import declaration')
manifest=j(HERE/inv['source_provenance']['manifest'])
excerpt=HERE/inv['source_provenance']['excerpt']
req(sha(excerpt)==manifest['excerpt_sha256']==inv['source_provenance']['excerpt_sha256'], 'source excerpt hash')
req(manifest['status']=='source excerpt for provenance only; not a refinement theorem', 'source provenance scope')
req(manifest['source_git_metadata'] is False, 'frozen source Git metadata caveat')
note=HERE.parents[1]/inv['publication_note']
req(note.is_file() and sha(note)==inv['publication_note_sha256'], 'publication note hash')
req(inv['no_rebuild'] is True and len(inv['boundary'])>=3, 'scope/no-rebuild record')
# Outer file inventory is exact except for its own checksum index.
cs=HERE/'SHA256SUMS'; lines=[x for x in cs.read_text().splitlines() if x.strip()]
listed=set()
for line in lines:
    h,rel=line.split(None,1); rel=rel.lstrip('* '); f=HERE/rel
    req(f.is_file() and sha(f)==h, 'bundle checksum '+rel); listed.add(rel)
actual_files={str(f.relative_to(HERE)) for f in HERE.rglob('*') if f.is_file() and f!=cs}
req(listed==actual_files, 'outer checksum file list differs from bundle files')
print(f"PASS: R378 evidence ({len(actual_files)} files); exact target/dependency copies, run receipt/log, five foundational axiom reports, source excerpt provenance, and checksums verified")
