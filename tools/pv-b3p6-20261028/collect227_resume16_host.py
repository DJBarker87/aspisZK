from pathlib import Path
import json,tarfile,hashlib
from run import H
R=H/'resume16';rows=[]
for p in sorted(R.glob('K*/receipt/receipt.json')):
 x=json.loads(p.read_text());d=p.parent.parent;out=(p.parent/'stdout.log').read_text();reservation=json.loads((d/'reservation.json').read_text());barrier=json.loads((d/'barrier.json').read_text());assert reservation['allowed'] is True and barrier['allowed'] is True
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},x['limits']
 inputs=json.loads((R/(d.name+'-inputs.json')).read_text())
 rows.append(dict(run=d.name,harness=inputs['harness'],status='PASS' if 'VERIFICATION:- SUCCESSFUL'in out else 'EXPECTED/UNEXPECTED FAIL' if 'VERIFICATION:- FAILED'in out else 'TIMEOUT' if x['exit_status']==124 else 'COMPILE/ENV FAILURE',receipt=str(p.relative_to(R)),exit=x['exit_status'],wall=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],cgroup_peak_bytes=x['cgroup_memory_peak_bytes'],swaps=x['swaps'],source_revision=x['source_revision'],source_hashes=inputs.get('source_hashes',{}),print_axioms=x['print_axioms']))
assert len(rows)<=40
(R/'run-index.json').write_text(json.dumps(rows,indent=2)+'\n')
# Preserve exact Lean source snapshots and accepted/rejected receipts too.
import shutil, subprocess
for p in H.glob('lean-72*/receipt/receipt.json'):
 d=p.parent.parent
 if not __import__('re').fullmatch(r'lean-720\d\d(?:-r\d+)?',d.name):continue
 target=R/'lean-receipts'/d.name
 if target.exists():shutil.rmtree(target)
 target.mkdir(parents=True)
 for q in d.rglob('*'):
  if q.is_file() and (q.suffix in ['.json','.log','.lean']):
   dst=target/q.relative_to(d);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(q,dst)
for name in ['TALLY-resume16.json','external-verification-resume16.json','cache-verification-resume16.json']:
 shutil.copy2(H/name,R/name)
bundle=Path('/home/dombarker/.kani/kani-0.67.0')
backend=dict(bundle=str(bundle),rustc_version_file=(bundle/'rustc-version').read_text().strip(),rust_toolchain_version=(bundle/'rust-toolchain-version').read_text().strip(),actual_compiler_query=subprocess.check_output([str(bundle/'bin/kani-compiler'),'--version'],text=True).strip(),deployed_configuration_query=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-vV'],text=True),pinned_kani_unchanged=True,pinned_cbmc_unchanged=True,deployed_configuration_credit=False,blocker='Bundled Kani backend is 1.93.0-nightly; rustc +1.94.1 metadata query does not select it. Required reached-body/stdlib parity with deployed 1.94.1 remains OPEN; std belongs to pv-b3q.',receipt_correction='All K*-inputs.json rustc fields are configuration queries, not the actual Kani backend. Original receipts retained, no verdict changed.')
(R/'KANI-BACKEND.json').write_text(json.dumps(backend,indent=2)+'\n')
with tarfile.open(H/'resume16-receipts.tar.gz','w:gz') as t:
 for p in R.rglob('*'):
  if p.is_file() and (p.suffix in ['.json','.log','.lean'] or p.name=='revision'):t.add(p,arcname=str(p.relative_to(R)))
print(json.dumps(dict(charged=len(rows),statuses={s:sum(r['status']==s for r in rows)for s in set(r['status']for r in rows)})))
