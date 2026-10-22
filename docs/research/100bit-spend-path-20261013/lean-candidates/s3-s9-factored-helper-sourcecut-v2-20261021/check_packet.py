from pathlib import Path
import hashlib,json,subprocess,sys
w=Path(__file__).resolve().parent
m=json.loads((w/'manifest.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
def eq(path,expected,label):
 p=w/path
 ok=p.is_file() and sha(p)==expected
 checks.append((label,ok,sha(p) if p.is_file() else None))
 return ok
p=m['input'];eq(p['path'],p['sha256'],'input')
eq('input/source-pins.json',p['source_pins_sha256'],'source-pins')
sourcepins=json.loads((w/'input/source-pins.json').read_text())
eq('source-snapshot/weights.rs',sourcepins['source_snapshot']['sha256'],'frozen-source-snapshot')
for phase in ['charon','aeneas']:
 section=m[phase]
 for key in ['receipt_path','admission_path','reservation_path']:
  path=section.get(key)
  if path: eq(path,section[key.replace('_path','_sha256')],phase+'-'+key)
for key in ['llbc_path','receipt_path','admission_path','reservation_path']:
 path=m['charon'].get(key)
 if path and key.endswith('_path'):
  h=m['charon'].get(key.replace('_path','_sha256'))
  if h:eq(path,h,'charon-'+key)
for name,x in m['aeneas']['outputs'].items():eq(x['path'],x['sha256'],'aeneas-'+name)
cr=json.loads((w/m['charon']['receipt_path']).read_text())
ar=json.loads((w/m['aeneas']['receipt_path']).read_text())
checks += [('charon-subprocess-green',cr.get('exit_status')==0 and cr.get('wrapper_exit_status')==1,None),('charon-llbc-valid',cr.get('llbc_has_errors') is False and cr.get('llbc_function_declaration_count')==164,None),('aeneas-success-and-declarations',ar.get('exit_status')==0 and ar.get('declaration_check_ok') is True,None),('no-olean-objects',not list(w.rglob('*.olean')),None),('no-executable-binaries',not [p for p in w.rglob('*') if p.is_file() and p.suffix in {'.exe','.so','.dylib'}],None)]
subprocess.run([sys.executable,str(w/'check_source_cut.py')],check=True,stdout=subprocess.PIPE,text=True)
for label,ok,value in checks: print(('PASS' if ok else 'FAIL'),label,value or '')
if not all(ok for _,ok,_ in checks):sys.exit(1)
print('PASS packet checks')
