"""Kani plus read-only reached-symbol capture within the same resource scope."""
from pathlib import Path
import sys,json,subprocess,lzma,hashlib,os
out=Path(sys.argv[1]);cmd=json.loads(sys.argv[2]);code=subprocess.run(cmd).returncode
harness=cmd[cmd.index('--harness')+1];records=[]
for p in Path(os.environ['CARGO_TARGET_DIR']).rglob('*.kani-metadata.json'):
 for h in json.loads(p.read_text()).get('proof_harnesses',[]):
  if h.get('pretty_name')!=harness:continue
  q=Path(h['goto_file'])
  if not q.exists():continue
  if q.stat().st_mtime < json.loads((out/'STARTED.json').read_text())['epoch']:continue
  raw=subprocess.check_output(['/home/dombarker/.kani/kani-0.67.0/bin/cbmc',str(q),'--show-symbol-table','--json-ui'],stderr=subprocess.STDOUT)
  f=out/f'symbols-{len(records)}.json.xz';f.write_bytes(lzma.compress(raw,preset=1))
  records.append({'metadata':str(p),'metadata_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'harness':h,'goto_sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'symbols':f.name,'symbols_raw_sha256':hashlib.sha256(raw).hexdigest()})
(out/'symbols-index.json').write_text(json.dumps({'harness':harness,'kani_exit':code,'records':records,'inside_same_scope':True},indent=2)+'\n')
raise SystemExit(code)
