"""Read exact reached Kani symbol tables; no Kani/toolchain installation."""
from run import H,run
from pathlib import Path
import json,hashlib,subprocess,sys,lzma
kind,ident=sys.argv[1:3];assert kind in ('host-mask','statement-mask','reconstruct','transition','external','internal')
assert 73960<=int(ident)<=73965
R=H/'resume17';O=R/('std-'+kind);O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if '--inside' not in sys.argv:
 label='S'+ident;retry=0
 while (R/label).exists():
  assert not (R/label/'receipt/receipt.json').exists();retry+=1;label='S'+ident+'-r'+str(retry)
 raise SystemExit(run('resume17/'+label,['timeout','180','python3',str(Path(__file__)),kind,ident,'--inside'],'read-only Kani reached-symbol listing for '+kind+'; no solver or compilation'))
patterns={'host-mask':'selector_mask_host_','statement-mask':'selector_mask_statement_','reconstruct':'reconstruct_10','transition':'validate_transition','external':'external_local_packed_raw','internal':'internal_linear_lazy'}
metadata=[]
for p in (H/'target/kani/x86_64-unknown-linux-gnu/debug/deps').glob('*.kani-metadata.json'):
 for h in json.loads(p.read_text()).get('proof_harnesses',[]):
  name=h['pretty_name'].split('::')[-1]
  if (name.startswith(patterns[kind]) if 'mask' in kind else name==patterns[kind]):metadata.append((p,h))
assert metadata,kind
records=[]
for i,(p,h) in enumerate(metadata):
 q=Path(h['goto_file']);assert q.exists(),q
 raw=subprocess.check_output(['/home/dombarker/.kani/kani-0.67.0/bin/cbmc',str(q),'--show-symbol-table','--json-ui'],stderr=subprocess.STDOUT)
 out=O/f'symbols-{i}.json.xz'
 with lzma.open(out,'wb') as f:f.write(raw)
 records.append(dict(metadata=str(p),metadata_sha256=sha(p),harness=h,goto_file=str(q),goto_sha256=sha(q),symbol_dump=str(out),symbol_dump_sha256=sha(out)))
(O/'index.json').write_text(json.dumps(dict(kind=kind,records=records,bundled_rustc=(Path('/home/dombarker/.kani/kani-0.67.0/rustc-version')).read_text(),deployed_rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-vV'],text=True),note='Symbol sets are retained exactly; token parity and intrinsic classification are separate checks, no inferred PASS.'),indent=2)+'\n')
print(json.dumps(dict(group=kind,symbol_listings=len(records))))
