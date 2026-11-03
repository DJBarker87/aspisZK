"""Read-only call-site windows of the adopted entropy function; no execution."""
from pathlib import Path
import hashlib,json,shlex,subprocess,sys
E=Path('evidence/pv-evh10-20261102')
adopted=json.loads((E/'adopted-backend-confirmation.json').read_text())
binary=adopted['adopted_build_receipt']['receipt']['path']
code=r'''
from pathlib import Path
import subprocess,re,hashlib,json,sys
p=Path(sys.argv[1]);raw=p.read_bytes()
rel=subprocess.check_output(['readelf','-rW',str(p)],text=True)
relocations=[l for l in rel.splitlines() if re.search(r'\b1457a0\s*$',l)]
got={int(l.split()[0],16) for l in relocations}
asm=subprocess.check_output(['objdump','-d','-C',str(p)],text=True).splitlines()
header='';hits=[]
for i,line in enumerate(asm):
 if re.match(r'^[0-9a-f]+ <.*>:$',line):header=line
 direct=bool(re.search(r'\b(?:call|jmp)\s+1457a0\b',line))
 ref=re.search(r'#\s+([0-9a-f]+)\b',line)
 indirect=ref is not None and int(ref[1],16) in got
 if direct or indirect:
  hits.append(dict(function=header,instruction=line,kind='direct branch' if direct else 'GOT reference',
   window='\n'.join(asm[max(0,i-35):i+12])))
print(json.dumps(dict(binary=dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)),
 command=['objdump','-d','-C',str(p)],relocations=relocations,windows=hits,executed=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)+' '+shlex.quote(binary)],text=True,capture_output=True)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
assert out['binary']['sha256']==adopted['adopted_build_receipt']['receipt']['sha256']
assert out['windows'],'no statically identified callers; inspect function-address escapes before claiming closure'
out.update(evidence_class='read-only adopted-artifact call-site support; compiler/runtime invocation interpretation not proved',
 retained=['all callers/address escapes and complete stack interpretation require source association and V370; these windows are not a full control-flow proof',
 'kernel full memory footprint, heap coherence, actual allocator and advancing native-family obligations retained'],
 native_runs=0,kani_runs=0,rows_removed=[],trust_fields_added=[])
p=E/'entropy-callers-da36d6aa.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS adopted entropy call-site windows:',len(out['windows']))
for row in out['windows']:print(row['function'],row['instruction'].strip())
