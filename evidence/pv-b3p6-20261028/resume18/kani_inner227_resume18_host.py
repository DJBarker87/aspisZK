"""Run one timed Kani gate, then save its reached symbols in the same scope."""
from pathlib import Path
import subprocess,json,lzma,hashlib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028');ident=sys.argv[1];assert sys.argv[2]=='--';cmd=sys.argv[3:]
harness=cmd[cmd.index('--harness')+1];status=subprocess.run(cmd).returncode
R=H/'resume18'/('K'+ident+'-symbols');R.mkdir(exist_ok=True);rows=[]
for p in (H/'target/kani/x86_64-unknown-linux-gnu/debug/deps').glob('*.kani-metadata.json'):
 for h in json.loads(p.read_text()).get('proof_harnesses',[]):
  if h['pretty_name']!=harness:continue
  q=Path(h['goto_file'])
  if not q.exists():continue
  raw=subprocess.check_output(['/home/dombarker/.kani/kani-0.67.0/bin/cbmc',str(q),'--show-symbol-table','--json-ui'],stderr=subprocess.STDOUT)
  out=R/f'symbols-{len(rows)}.json.xz'
  with lzma.open(out,'wb')as f:f.write(raw)
  sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
  rows.append(dict(metadata=str(p),metadata_sha256=sha(p),harness=h,goto_file=str(q),goto_sha256=sha(q),symbol_dump=str(out),symbol_dump_sha256=sha(out)))
(R/'index.json').write_text(json.dumps(dict(harness=harness,kani_exit=status,records=rows,symbol_listing_inside_same_capped_Kani_scope=True),indent=2)+'\n')
raise SystemExit(status)
