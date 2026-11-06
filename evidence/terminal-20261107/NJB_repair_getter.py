from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;p=E/'NJB_terminal.rs.txt';s=p.read_text()
s=s.replace('fn common()', 'fn digest()->aspis_core::r0::merkle::Digest { let w:[u32;8]=kani::any();['+','.join(f'M31(w[{i}])'for i in range(8))+']}\nfn frontier()->[aspis_core::r0::merkle::Digest;20] {core::array::from_fn(|_|digest())}\nfn common()')
for key in ['historical_global_anchor','current_root','next_root','anchor_root','nullifier','recipient_commitment','change_commitment']:s=s.replace(key+':kani::any()',key+':digest()')
for key in ['frontier','next_frontier']:s=s.replace(key+':kani::any()',key+':frontier()')
s=s.replace('#[kani::unwind(2)]','#[kani::unwind(33)]');p.write_text(s)
# Retain final patch from original frozen sources, no original body edit.
files=json.loads((E/'NJB_PATCH_FILES.json').read_text());prefix='#![cfg_attr(kani,feature(allocator_api))]\n';patch=''
for q,r in files.items():
 old=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+q]).decode();new=(prefix if q.endswith('/lib.rs') else '')+old+r['append'];r['prepend']=prefix if q.endswith('/lib.rs')else'';r['after_sha256']=hashlib.sha256(new.encode()).hexdigest();patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+q,tofile='b/'+q))
patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NJB_terminal.rs'))
(E/'NJB_native.patch').write_text(patch);(E/'NJB_PATCH_FILES.json').write_text(json.dumps(files,indent=1))
(E/'NJB_update_getter.py').write_text('''from pathlib import Path
import json,hashlib,lzma,base64
b=Path(__file__).resolve().parent;s=b/'NJB_src';x=json.loads((b/'NJB_PATCH_FILES.json').read_text());data=json.loads(lzma.decompress((b/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()));pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text())
for q,r in x.items():
 raw=r.get('prepend','').encode()+base64.b64decode(data[q])+r['append'].encode();assert hashlib.sha256(raw).hexdigest()==r['after_sha256'];(s/q).write_bytes(raw);pins[q]=r['after_sha256']
q='crates/aspis-statement/src/pool_v1/NJB_terminal.rs';raw=(b/'NJB_terminal.rs.txt').read_bytes();(s/q).write_bytes(raw);pins[q]=hashlib.sha256(raw).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('all-bit-valid M31 generators and cfg-only allocator feature repaired')
''')
x=dict(attempt='NJB_L007',kind='setup',module='NJB_getter_inputs_repair',sources=['NJB_update_getter.py','NJB_terminal.rs.txt','NJB_PATCH_FILES.json','NJB_native.patch'],command=['python3','NJB_update_getter.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},collect=['NJB_SOURCE_PINS.json'],expected_time='Repair own cfg-only harness input constructors; actual frozen function unchanged')
(E/'NJB_L007.json').write_text(json.dumps(x));print('getter generators cover every raw M31 word; cfg-only allocator feature configured')
