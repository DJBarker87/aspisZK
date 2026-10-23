#!/usr/bin/env python3
"""Backend names only: preserve all bodies, IDs, Rust names and types."""
from pathlib import Path
import copy,hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-full-forest-codec-five-unrolled-v1'
p=P/'Codec.llbc';original=json.loads(p.read_text());d=copy.deepcopy(original);changed=[]
for f in d['translated']['fun_decls']:
 if not f:continue
 name=f['item_meta']['name'];first=name[0].get('Ident',[''])[0];last=name[-1].get('Ident',[''])[0]
 if first in ['aspis_statement','aspis_core'] and last and last[0].isupper():
  assert f['item_meta']['attr_info']['rename'] is None
  f['item_meta']['attr_info']['rename']='constructor_'+last
  changed.append(dict(id=f['def_id'],rust_name=name,backend_name='constructor_'+last))
assert changed
q=P/'Codec-renamed.llbc';q.write_text(json.dumps(d)+'\n')
check=copy.deepcopy(d)
for f in check['translated']['fun_decls']:
 if f and any(x['id']==f['def_id'] for x in changed):f['item_meta']['attr_info']['rename']=None
assert check==original
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
(P/'backend-renaming.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',original_sha256=sha(p),renamed_sha256=sha(q),changes=changed,only_backend_rename_fields_changed=True,qualification=__doc__),indent=2)+'\n')
A=H/'s1-collapse-tool-recover-v2/source/src/_build/default/main.exe'
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS6FiveUnrolledCodec','-dest',str(P/'renamed-generated'),'-subdir','AspisS6FiveUnrolledCodec','-split-files','-emit-json',str(q)]
tag='s6-full-forest-codec-five-unrolled-aeneas-renamed-v1'
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,llbc_sha256=sha(q),tool_sha256=sha(A),renaming_sha256=sha(P/'backend-renaming.json'),qualification=__doc__,expected_time='Focused same-LLBC Aeneas translation with metadata-only collision resolution; no rebuild or arithmetic evaluation.'),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Exact native outer codec: backend enum constructor naming only','--','timeout','180',*cmd]))
