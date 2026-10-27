#!/usr/bin/env python3
"""Locate declarations that occur in the retained kernel reachable-constant set.
No type checking and no inferred native correspondence: records are name/source evidence.
"""
import json,pathlib,re,subprocess,hashlib,collections
ROOT=pathlib.Path(__file__).resolve().parents[2]; OUT=pathlib.Path(__file__).resolve().parent
reachable=set(json.load(open(ROOT/'evidence/replay-deployed2-20261027/RPx_reachable-constants.json')))
files=subprocess.check_output(['git','ls-files','*.lean'],cwd=ROOT,text=True).splitlines()
# Include original candidates read-only, never live worktrees; all paths are in this checkout.
found=collections.defaultdict(list)
for f in files:
 if not f.startswith(('lean/','lean-candidates/','evidence/','docs/research/100bit-spend-path-20261013/','docs/research/v8-full-view-zk-20260912/lean/')): continue
 p=ROOT/f
 try: text=p.read_text()
 except FileNotFoundError:continue
 stack=[]
 for lineno,line in enumerate(text.splitlines(),1):
  line=line.strip()
  m=re.match(r'namespace\s+([\w.]+)',line)
  if m: stack.append(('ns',m[1]));continue
  if re.match(r'(noncomputable\s+)?section(\s|$)',line):stack.append(('section',''));continue
  if re.match(r'end(\s|$)',line):
   if stack: stack.pop()
   continue
  m=re.search(r'\b(?:def|abbrev|theorem|opaque|structure|inductive)\s+([\w.]+)',line)
  if not m or line.startswith(('--','/--','/-','*')):continue
  ns='.'.join(x[1] for x in stack if x[0]=='ns'); name=m[1][7:] if m[1].startswith('_root_.') else (ns+'.' if ns else '')+m[1]
  if name in reachable:
   found[name].append({'file':f,'line':lineno,'module_hint':p.stem,'source_sha256':hashlib.sha256(text.encode()).hexdigest()})
(OUT/'NBI2_cohort_index.json').write_text(json.dumps(found,indent=2)+'\n')
print('located reachable declarations',len(found))
