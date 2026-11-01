"""Runs the matched control, then read-only symbol inspection within its same cap."""
from pathlib import Path
import subprocess,json,sys,hashlib,lzma
out=Path(sys.argv[1]);cmd=json.loads(sys.argv[2]);code=subprocess.run(cmd).returncode
# Preserve control exit independently of read-only inspection success.
(out/'control-exit.json').write_text(json.dumps({'exit_status':code,'command':cmd})+'\n')
root=out.parent
p=root/'target/kani/x86_64-unknown-linux-gnu/debug/deps/pv_k3scan_pathbuf-ee4c6c50b6475ade.kani-metadata.json'
try:
 d=json.loads(p.read_text());hs=[h for h in d['proof_harnesses'] if h['pretty_name']=='path_checks::pathbuf_borrows'];assert len(hs)==1,hs
 h=hs[0];q=Path(h['goto_file']);raw=subprocess.check_output(['/home/dombarker/.kani/kani-0.67.0/bin/cbmc',str(q),'--show-symbol-table','--json-ui'],stderr=subprocess.STDOUT)
 (out/'positive-symbols.json.xz').write_bytes(lzma.compress(raw,preset=1));(out/'positive-metadata.json').write_bytes(p.read_bytes());(out/'symbol-inspection.json').write_text(json.dumps({'metadata_path':str(p),'metadata_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'goto_path':str(q),'goto_sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'symbol_dump_sha256':hashlib.sha256(raw).hexdigest(),'exit_status':0,'note':'Read-only inspection of earlier positive goto; no solver or positive re-run'},indent=2)+'\n')
except Exception as e:(out/'symbol-inspection.json').write_text(json.dumps({'error':str(e),'exit_status':1})+'\n')
raise SystemExit(code)
