from pathlib import Path
import json,subprocess,hashlib,lzma,re,struct
H=Path('/home/dombarker/project-offloads/codex-cx-native-sbfstack-20261028');O=H.parent
nm='/usr/bin/nm';w=json.loads((H/'NDC_WARNINGS.json').read_text());out={}
for p in sorted((H/'NDC_target_native/release/deps').glob('libaspis*.rlib')):
 q=subprocess.run([nm,'--defined-only',str(p)],capture_output=True,text=True);(H/('NDC_native_'+p.stem+'_nm.txt')).write_text(q.stdout+q.stderr)
 out[p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'nm_exit':q.returncode,'matches':{row['identity']:[s for s in re.findall(r'_ZN\S+',q.stdout) if re.sub(r'17h[0-9a-f]{16}E$','',s)==row['identity']] for row in w}}
(H/'NDC_NATIVE_SYMBOLS.json').write_text(json.dumps(out,indent=2)+'\n')
print('NATIVE',json.dumps({p:{k:len(v) for k,v in j['matches'].items() if v} for p,j in out.items()}))
# Read original compiler IR to identify warned instances and their immediate IR callers.
r={}
for label in ['NCY_B001','NCY_B002']:
 d=O/'codex-cx-native-elfpins-20261028'/label/'diagnostics/compiler-output'
 for p in d.glob('*.ll'):
  t=p.read_text();current=None;defs={};uses={}
  for ln in t.splitlines():
   if ln.startswith('define '):
    m=re.search(r'@("[^"]+"|[^ (]+)',ln);current=m.group(1).strip('"') if m else None
    if current:defs[current]=ln
   if ln=='}':current=None
   if current:
    for sym in re.findall(r'@("[^"]+"|[^ (,)]+)',ln):uses.setdefault(sym.strip('"'),set()).add(current)
  hits={}
  for row in w:
   for dd in row['diagnostics'].values():
    sym=dd['symbol']
    if sym in defs:hits[sym]={'definition':defs[sym],'callers':sorted(uses.get(sym,set())-{sym})}
  if hits:r[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':hits}
(H/'NDC_DIAGNOSTIC_IR.json').write_text(json.dumps(r,indent=2)+'\n');print('IR_COUNTS',{p:len(v['hits']) for p,v in r.items()})
# Compress previously generated text; no binary artifacts committed.
pins={}
for pat in ['NDC_*_disassembly.txt','NDC_*_readelf.txt','NDC_*_symbols.txt']:
 for p in H.glob(pat):
  data=p.read_bytes();xz=Path(str(p)+'.xz');xz.write_bytes(lzma.compress(data,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(data).hexdigest()+'  '+p.name+'\n')
  pins[p.name]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'xz_bytes':xz.stat().st_size}
(H/'NDC_TEXT_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
# Inspect only retained no-warning try_from_fn instances' syntactic r10 accesses.
t=(H/'NDC_verifier_disassembly.txt').read_text();samples=[]
for name,body in re.findall(r'^([0-9a-f]+ <[^\n]+>):\n(.*?)(?=^[0-9a-f]+ <|\Z)',t,re.M|re.S):
 if 'try_from_fn' in name:
  refs=re.findall(r'[^\n]*\br10\b[^\n]*',body);samples.append({'function':name,'r10_lines':refs})
(H/'NDC_GENERIC_DISASSEMBLY.json').write_text(json.dumps(samples,indent=2)+'\n');print('TRY_FN',json.dumps(samples))
print('PINS',json.dumps(pins))
