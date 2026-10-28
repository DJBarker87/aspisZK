from pathlib import Path
import json,hashlib,difflib,subprocess
import NCX_transport as t
E=t.E
attempts=[p.parent.parent.name for p in sorted(E.glob('NCX_K*/sources/NCX_harness.patch')) if p.stat().st_size==0]
assert attempts,'nothing to recover'
r=t.py(f'''from pathlib import Path
import json
b=Path({t.B!r})
print(json.dumps({{a:{{str(p.relative_to(b/a/'sources'/'NCX_src')):p.read_text() for p in (b/a/'sources'/'NCX_src').rglob('*.rs')}} for a in {attempts!r}}}))
''');assert r.returncode==0,r.stderr
sources=json.loads(r.stdout);report={}
for a,files in sources.items():
 receipt=json.loads((E/a/'receipt.json').read_text());patch='';verified={}
 for name,body in files.items():
  expected=receipt['source_hashes']['NCX_src/'+name];h=hashlib.sha256(body.encode()).hexdigest();assert h==expected,(a,name)
  original=subprocess.run(['git','show',t.REV+':'+name],capture_output=True,text=True);before=original.stdout if original.returncode==0 else ''
  patch+=''.join(difflib.unified_diff(before.splitlines(True),body.splitlines(True),fromfile='a/'+name if before else '/dev/null',tofile='b/'+name))
  verified[name]=h
 required=[n for n in receipt['source_hashes'] if n.startswith('NCX_src/') and n.endswith('.rs')]
 assert len(verified)==len(required),(a,'incomplete host snapshot')
 assert patch,(a,'empty recovered patch')
 (E/a/'sources/NCX_harness.patch').write_text(patch)
 report[a]=dict(source='immutable host attempt/sources/NCX_src',verified_source_hashes=verified,patch_sha256=hashlib.sha256(patch.encode()).hexdigest())
(E/'NCX_PATCH_RECOVERY.json').write_text(json.dumps(report,indent=2)+'\n')
print('Recovered and source-hash-verified',len(report),'patches')
