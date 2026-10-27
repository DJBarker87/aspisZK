from pathlib import Path
import json,hashlib,subprocess
B=Path(__file__).resolve().parent
O=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
S=Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/src')
def artifact(p):
 return dict(path=str(p),sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),bytes=p.stat().st_size)
pins=json.loads((O/'XRa_release_sourcepins.json').read_text());errors=[]
for row in pins['files']:
 p=S/row['path']
 if not p.is_file() or artifact(p)['sha256']!=row['sha256']:errors.append(row['path'])
tools=[O/'XRa_bin/charon',O/'XRa_bin/charon-driver',O/'XRa_bin/aeneas-b59d5188-extended',Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')]
artifacts=[Path('/home/dombarker/project-offloads/codex-cx-extraction-repro4-20261027/XRd_release_candidate_tx1.llbc')]+list(B.glob('XRg_*tx1.llbc'))+[B/'XRg_crate/Cargo.lock']+list(B.glob('XRg_Association.olean*'))
receipts=[]
for p in sorted(B.glob('XRg_*/receipt.json')):
 r=json.loads(p.read_text());out=p.parent/'stdout.log';log=out.read_text();timed='CBMC timed out' in log
 receipts.append(dict(attempt=r['attempt'],receipt=artifact(p),stdout=artifact(out),exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],cgroup_peak_bytes=r['cgroup_memory_peak_bytes'],swaps=r['swaps'],timeout=timed,limits=r['limits']))
out=dict(release_revision=pins['source_revision'],files_checked=len(pins['files']),changed_source_files=errors,tools=[artifact(p) for p in tools],artifacts=[artifact(p) for p in artifacts],receipts=receipts,generated_outputs=[artifact(p) for p in B.glob('XRg_generated*/**/*') if p.is_file()],runner_matches_coherent=(B/'XRg_run_host.py').read_bytes()==Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S2W_run_host.py').read_bytes())
(B/'XRg_HostAudit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(source_errors=errors,files_checked=len(pins['files']),attempts=len(receipts),outputs=len(out['generated_outputs']))))
