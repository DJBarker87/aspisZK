#!/usr/bin/env python3
"""Locate exact reached declarations in retained Lean sources (static, no compile)."""
import json,re,subprocess,hashlib
from pathlib import Path
OUT=Path(__file__).parent
constants=set(json.loads(Path('evidence/replay-deployed2-20261027/RPx_reachable-constants.json').read_text()))
tops=set(json.loads(Path('evidence/replay-tops3-20261027/RPv_FJv_Top-reachable-constants.json').read_text()))
pins=json.loads(Path('evidence/replay-deployed2-20261027/RPx_retained-object-pins.json').read_text())
pin_basenames={Path(x).stem for x in pins if x.endswith('.olean')}
pin_by_file={}
for q,v in pins.items():
 if q.endswith('.olean') and isinstance(v,dict):pin_by_file.setdefault(Path(q).name,[]).append({'path':q,**v})
paths=subprocess.check_output(['git','ls-files','*.lean']).decode().splitlines()
found={};decls={}
for fn in paths:
 p=Path(fn)
 if not p.is_file():continue
 if p.stem not in pin_basenames and '/evidence/' in fn:continue
 # Don't scan irrelevant enormous generated certificates.
 if any(x in fn for x in ['R17Table','R17Narrow','Certificate','WideMaskingRankChunk']):continue
 try:s=p.read_text()
 except UnicodeDecodeError:continue
 stack=[];block=0;last_rust=None
 rust_sources={i:(m[1],int(m[2]),int(m[3])) for i,line in enumerate(s.splitlines(),1) if (m:=re.search(r"Source: '([^']+)', lines (\d+):\d+-(\d+):\d+",line))}
 for i,line in enumerate(s.splitlines(),1):
  if i in rust_sources:last_rust=rust_sources[i]
  # Strip nested Lean block comments so examples are never counted as definitions.
  clean='';j=0
  while j<len(line):
   if line[j:j+2]=='/-':block+=1;j+=2
   elif block and line[j:j+2]=='-/':block-=1;j+=2
   elif block:j+=1
   elif line[j:j+2]=='--':break
   else:clean+=line[j];j+=1
  line=clean.strip()
  ns=re.match(r'namespace\s+([\w.]+)',line)
  if ns:stack.append(('ns',ns[1]));continue
  if re.match(r'(?:noncomputable\s+)?section\b',line):stack.append(('section',''));continue
  if re.match(r'end(?:\s|$)',line):
   if stack:stack.pop()
   continue
  m=re.match(r'(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|unsafe|partial)\s+)*(def|abbrev|theorem|structure|inductive|opaque)\s+([^\s(:{]+)',line)
  if not m:continue
  name=m[2];full='.'.join([v for k,v in stack if k=='ns']+[name])
  if full.startswith('_root_.'):full=full[7:]
  if full not in constants:continue
  row={'name':full,'kind':m[1],'source':fn,'line':i,'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'in_deployed_closure':True,'in_tops3_closure':full in tops}
  # Aeneas modules use directory-qualified Funs/Types; others use their basename.
  module=(p.parent.name+'.'+p.stem) if p.stem in ('Funs','Types','FunsExternal','TypesExternal','TypesExternal_Template') else p.stem
  row['module']=module
  row['rust_source_comment']=last_rust
  suffix='/'+module.replace('.','/')+'.olean'
  row['retained_objects']=[v for v in pin_by_file.get(module.split('.')[-1]+'.olean',[]) if v['path'].endswith(suffix)]
  found.setdefault(full,[]).append(row)
(OUT/'NBI1_COHORT_INDEX.json').write_text(json.dumps(found,indent=2)+'\n')
print(len(constants),'reached constants;',len(found),'located declarations in',len(paths),'Lean sources')
