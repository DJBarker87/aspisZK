"""Replace two unbound MIR inputs with the matching deployed LLVM units.
This establishes representation coverage of those compilation units, not
interprocedural reachability or public provenance of their diagnostics.
"""
from pathlib import Path
import hashlib,json,re,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');P=D.parent/'codex-pv-rdea-20261028';T=P/'client-target/release/deps'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((P/'ir-mir-pins.json').read_text());rows=[]
for ident in ['5923482f8c707be4','75c27e421895d7c1']:
 p=T/f'libsecp256k1-{ident}.ll';pin=next(r for r in pins['llvm'] if r['path']==str(p));assert sha(p)==pin['sha256']
 defs=[];aliases=[];calls=[];indirect=[];asm=[];current=None;module=None;compiler=[]
 with p.open() as f:
  for n,line in enumerate(f,1):
   if line.startswith('; ModuleID'):module=line.strip()
   if 'rustc version' in line:compiler.append(line.strip())
   if line.startswith('define '):
    m=re.search(r'@([^ (]+)\(',line);assert m,(n,line[:200]);current=m[1];defs.append(dict(symbol=current,line=n))
   if line.startswith('@') and ' alias ' in line:aliases.append(dict(symbol=line.split(' =')[0][1:],line=n))
   if re.search(r'\b(?:call|invoke|callbr)\b',line) and not line.lstrip().startswith(';'):
    direct=re.search(r'@([^ (]+)\(',line)
    item=dict(function=current,line=n,instruction=line.strip()[:3000])
    if direct:item['callee']=direct[1];calls.append(item)
    else:indirect.append(item)
   if ' asm ' in line:asm.append(dict(function=current,line=n,instruction=line.strip()[:3000]))
 rlib=T/f'liblibsecp256k1-{ident}.rlib';nm=subprocess.check_output(['nm','--defined-only','--format=posix',str(rlib)],text=True,stderr=subprocess.DEVNULL)
 syms=[];members=[]
 for line in nm.splitlines():
  if line.endswith(']:'):members.append(line)
  z=line.split()
  if len(z)>=2 and z[1] in ['T','t','W','w']:syms.append(z[0])
 represented={r['symbol'] for r in defs+aliases};missing=sorted(set(syms)-represented);assert not missing,missing
 # Pin source/build inputs and Cargo's exact per-unit feature/profile record.
 fp=T.parent/'.fingerprint'/f'libsecp256k1-{ident}'/'lib-libsecp256k1.json'
 deps=(T/f'libsecp256k1-{ident}.d').read_text().splitlines()[0].split(': ',1)[1].split()
 source_pins=[dict(path=q,sha256=sha(Path(q))) for q in deps]
 rows.append(dict(ident=ident,llvm=dict(**pin,actual_sha256=sha(p)),archive=dict(path=str(rlib),sha256=sha(rlib),members=members,text_symbols=syms),module=module,compiler=compiler,defined_functions=defs,aliases=aliases,unrepresented_text_symbols=missing,calls=calls,indirect=indirect,asm=asm,source_pins=source_pins,fingerprint=dict(path=str(fp),sha256=sha(fp),record=json.loads(fp.read_text()))))
wrapper=P/'emit-wrapper.py';assert "=='libsecp256k1' else ',mir'" in wrapper.read_text()
result=dict(classification='compiler-structure artifact coverage, not a complete linked diagnostic effect closure',replaced_mir=['libsecp256k1-5923482f8c707be4.mir','libsecp256k1-75c27e421895d7c1.mir'],mir_credited=False,wrapper_sha256=sha(wrapper),build_command=json.loads((P/'build-command.json').read_text()),rows=rows)
(D/'llvm-replacement.json').write_text(json.dumps(result,indent=2)+'\n')
print([(r['ident'],len(r['defined_functions']),len(r['archive']['text_symbols']),len(r['unrepresented_text_symbols']),len(r['indirect'])) for r in rows])
