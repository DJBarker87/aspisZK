from NJN_formal import *
r=run('NJN_L030','inspect','NJN_actual_SDK',['python3','NJN_source_audit.py'],{'NJN_source_audit.py':(E/'NJN_source_audit.py').read_text(),'NJN_SDK_PINS.json':(E/'NJN_SDK_PINS.json').read_text()});assert r['exit_status']==0
r=ssh('cat '+B+'/NJN_ACTUAL_SDK.json');assert r.returncode==0,r.stderr
x=json.loads(r.stdout);sources=x.pop('sources')
for n,t in sources.items():
 h=sha(t.encode());p=E/'NJN_SDK_INPUTS'/(h+'.xz')
 if not p.exists():p.write_bytes(lzma.compress(t.encode()))
x['source_archive_directory']='NJN_SDK_INPUTS/<sha256>.xz';(E/'NJN_ACTUAL_SDK.json').write_text(json.dumps(x,indent=1)+'\n')
