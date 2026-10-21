#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[2]
P=ROOT/'docs/research/100bit-spend-path-20261013'; E=P/'evidence/port-integrate-20261021'; S=P/'lean'
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT,text=True).strip()
# Prefer the last successful checkpoint freeze's explicit environment, which
# includes the focused Stage2 reader cache, then retain the published base path.
c=json.loads((P/'evidence/ckpt-abi-draft-20261021/OraclePortCkptAbiFreeze-2/command.json').read_text())
paths=list(dict.fromkeys(x for x in c['lean_path'].split(':') if x))
paths.insert(0,'/tmp/codex-cx-ckpt-abi-draft-20261021-objects')
(E/'lean-path.txt').write_text(':'.join(dict.fromkeys(paths))+'\n')
seen=set(); order=[]; external=[]
def visit(m):
 if m in seen:return
 seen.add(m); f=S/(m.replace('.','/')+'.lean')
 if not f.exists():external.append(m);return
 for x in re.findall(r'^import\s+(\S+)',f.read_text(),re.M):visit(x)
 order.append(m)
targets=['OraclePortFrozenOrderHeadline']+sorted(f.stem for f in S.glob('OraclePortCkptAbi*.lean'))
for m in targets:visit(m)
cache=[]
for m in order+external:
 if m.startswith('OraclePort'):continue
 obj=next((Path(p)/(m.replace('.','/')+'.olean') for p in paths if (Path(p)/(m.replace('.','/')+'.olean')).exists()),None)
 f=S/(m.replace('.','/')+'.lean')
 cache.append(dict(module=m,path=str(obj) if obj else None,sha256=hashlib.sha256(obj.read_bytes()).hexdigest() if obj else None,source_sha256=hashlib.sha256(f.read_bytes()).hexdigest() if f.exists() else None))
plan=dict(source_revision=git('rev-parse','HEAD'),research_revision=git('rev-parse','research'),targets=targets,compile_order=[m for m in order if m.startswith('OraclePort')],cached_dependencies=cache)
(E/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
# Lexical scan with nested Lean comments and string literals blanked, keeping lines.
def code_only(s):
 out=[]; i=0; depth=0; string=False
 while i<len(s):
  if depth:
   if s[i:i+2]=='/-':depth+=1;out.extend('  ');i+=2
   elif s[i:i+2]=='-/':depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
   if s[i]=='\\':out.extend('  ');i+=2
   elif s[i]=='"':string=False;out.append(' ');i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='/-':depth=1;out.extend('  ');i+=2
  elif s[i:i+2]=='--':
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  elif s[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
added=git('diff','--name-only','--diff-filter=A','research','HEAD','--','*.lean').splitlines()
pattern=r'\b(?:sorry|axiom|admit|native_decide|implemented_by)\b|@\[\s*extern\b'
findings=[]; raw=[]
for name in added:
 t=(ROOT/name).read_text()
 for category,txt,items in [('code',code_only(t),findings),('raw',t,raw)]:
  for m in re.finditer(pattern,txt):items.append(dict(file=name,line=txt.count('\n',0,m.start())+1,token=m.group()))
# All lexical admit hits were reviewed: these are the Decision wrapper
# OraclePortAdmission.admit and its term occurrences, never the tactic.
reviewed=[]; rejected=[]
for x in findings:
 line=(ROOT/x['file']).read_text().splitlines()[x['line']-1]
 if x['token']=='admit' and not re.search(r'(?:^|[;·])\s*admit\s*(?:$|;)',line):
  reviewed.append({**x,'classification':'OraclePortAdmission.admit definition or term reference','source_line':line})
 else:rejected.append(x)
findings=rejected
changes=git('diff','--name-status','--diff-filter=MDRT','research','HEAD').splitlines()
(E/'audit.json').write_text(json.dumps(dict(research_revision=plan['research_revision'],source_revision=plan['source_revision'],new_lean_files=added,forbidden_code_findings=findings,raw_text_findings=raw,reviewed_identifier_occurrences=reviewed,all_preexisting_file_changes=changes,pass_scan=not findings,pass_preexisting_unchanged=not changes),indent=2)+'\n')
print(json.dumps(dict(port_compiles=len(plan['compile_order']),cached_dependencies=len(cache),missing_cache=[x['module'] for x in cache if not x['path']],scan_findings=findings,reviewed_identifiers=len(reviewed),preexisting_changes=changes),indent=2))
