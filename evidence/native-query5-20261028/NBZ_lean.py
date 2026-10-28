from NBZ_host import *
import sys,hashlib,fcntl
_serial=(E/'NBZ_SERIAL.lock').open('a');fcntl.flock(_serial,fcntl.LOCK_EX)
a,module=sys.argv[1:];assert a.startswith('NBZ_L') and int(a[5:])<=50
src=Path('docs/research/100bit-spend-path-20261013/lean')/(module+'.lean');assert module.startswith('NBZ_')
admit(a+'_UPLOAD')
r=py(f"from pathlib import Path; p=Path({(B+'/NBZ_generated')!r});p.mkdir(exist_ok=True);(p/{(module+'.lean')!r}).write_text({src.read_text()!r})")
assert r.returncode==0,r.stderr
base=json.loads((E.parent/'native-query4-20261028/NBW_L012.json').read_text())
base.update(attempt=a,module=module,sources=['NBZ_generated/'+module+'.lean'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True)
base['command']=[x.replace('NBW_generated','NBZ_generated').replace('NBW_Audit',module) for x in base['command']]
base['deps_fingerprint']={'scope':'NBW/NBO/NBF/NBB imported unchanged; coherent SInt2; Aeneas NBZ_LIBRARY_PIN.json'}
# Pin actual Aeneas resolution and all cache dependencies before proof.
pin=json.loads((E.parent/'native-query4-20261028/NBW_LIBRARY_PIN.json').read_text())
r=py(f'''from pathlib import Path
import hashlib,json
pins=json.loads({json.dumps(pin)!r})
for n,v in pins.items():assert hashlib.sha256(Path(n).read_bytes()).hexdigest()==v['sha256'],n
print(json.dumps(pins,indent=2))
''');assert r.returncode==0,r.stderr
(E/'NBZ_LIBRARY_PIN.json').write_text(r.stdout)
# The unchanged inherited Lean launcher inventories actual direct object resolution.
# launch() uses S2W_run_host; select its existing Lean front-end through own hook.
import NBZ_host
oldssh=NBZ_host.ssh
def lean_ssh(code,submitted=False):
 if submitted and 'S2W_run_host.py '+a+'.json' in code:code=code.replace('S2W_run_host.py','S2W_lean_host.py')
 return oldssh(code,submitted)
NBZ_host.ssh=lean_ssh
launch(base)
