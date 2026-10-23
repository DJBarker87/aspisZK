#!/usr/bin/env python3
"""Focused standard-library-only Lean coverage theorem; no dependency rebuild.
The local unknown lock is retained. This separate Linux target uses the pinned
Lean4.32.0 bundled Omega/List objects, one job, and an explicit no-swap scope.
"""
from pathlib import Path
import json,hashlib,subprocess,os,re,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');project=H/'lean-native-prefix-frame-v1'
attempt=sys.argv[1];tag='sdk-native-frame-coverage-'+attempt
T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(project/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage native_frame_coverage\n')
(project/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
source=project/'S2SdkNativeFrameCoverageV1.lean'
assert all(x not in source.read_text() for x in ['sorry','native_decide','axiom '])
cmd=[str(T/'bin/lake'),'env',str(T/'bin/lean'),'-j1','-M4400','-o',str(project/'S2SdkNativeFrameCoverageV1.olean'),str(source)]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
pins=dict(schema='focused-extractor-proof-packet-v1',source_context_revision='de1e75322',source_sha256=sha(source),command=cmd,tool_pins={str(p):sha(p) for p in [T/'bin/lake',T/'bin/lean']},direct_import_pins={str(p.relative_to(T/'lib/lean')):sha(p) for p in [T/'lib/lean/Init.olean',T/'lib/lean/Lean/Elab/Tactic/Omega.olean']},project_source_pins={p.name:sha(p) for p in [project/'lakefile.lean',project/'lean-toolchain']},runner_sha256=sha(Path(__file__)),qualification=__doc__+' Source SHA is authoritative for this uncommitted candidate. No native SDK theorem or complete source refinement follows from the pure index/list coverage theorem alone.')
(H/(tag+'-input.json')).write_text(json.dumps(pins,indent=2)+'\n')
os.chdir(project)
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Focused generic index coverage/list-extensionality proof, bundled Lean libraries only; no cold dependencies or dense numeral evaluation','--',*cmd])
rp=H/'receipts'/tag/'receipt.json';receipt=json.loads(rp.read_text());log=(rp.parent/'stdout.log').read_text()
audits=re.findall(r"'[^\n]+' (?:depends on axioms:\s*\[[\s\S]*?\]|does not depend on any axioms)",log)
(rp.parent/'source.lean').write_bytes(source.read_bytes())
overlay=dict(pins)
overlay.update(raw_receipt_sha256=sha(rp),exit_status=receipt['exit_status'],wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'],print_axioms=audits,qualification=__doc__+' Overlay records actual source/import pins and Lean axioms. Raw capped receipt source_revision is inherited host bookkeeping; its print_axioms default is inapplicable and superseded by this log-derived audit.')
if status==0:
 assert len(audits)==4,audits
 assert not any(x in str(audits) for x in ['sorryAx','Lean.ofReduceBool','native_decide'])
 overlay['object_sha256']=sha(project/'S2SdkNativeFrameCoverageV1.olean')
(rp.parent/'lean-audit.json').write_text(json.dumps(overlay,indent=2)+'\n')
print(log);print(json.dumps(dict(exit_status=status,print_axioms=audits)))
raise SystemExit(status)
