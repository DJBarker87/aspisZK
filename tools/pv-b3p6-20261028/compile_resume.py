"""Compile one new module through pinned run2.py in a private env-J overlay.
Never writes shared env-J sources or objects. IDs and budget remain job-owned.
"""
from run import H,run
from pathlib import Path
import os,sys,json,hashlib,re,time
ORIGINAL_JENV=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')
JENV=H/'env-J-private.json'
assert json.loads((H/'external-verification.json').read_text())['mismatches']==[]
# Project closure resolved separately before project imports.
module=sys.argv[1];assert not module.startswith('XR');assert module.startswith('PV_B3P_') or module in json.loads((H/'project-resolution.json').read_text())['modules'],module
shared_env=json.loads(ORIGINAL_JENV.read_text())
shared_env['LEAN_PATH']='/home/dombarker/project-offloads/aspis-joint-20261019/objects:'+shared_env['LEAN_PATH']
JENV.write_text(json.dumps(shared_env,indent=2)+'\n')
DRIVER=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py')
module=sys.argv[1];assert module.startswith('PV_B3P_') or module in json.loads((H/'project-resolution.json').read_text())['modules'],module
S=H/'lean';O=H/'lean-objects';S.mkdir(exist_ok=True);O.mkdir(exist_ok=True)
p=S/(module.replace('.','/')+'.lean');assert p.exists(),p
outfile=O/(module.replace('.','/')+'.olean')
outfile.parent.mkdir(parents=True,exist_ok=True)
state=H/'TALLY-resume.json';t=json.loads(state.read_text())
t['next_unused_id']=next((i for i in range(36400,36497) if i not in t['used_ids']),36497)
assert t['lean_attempts']<100,t
is_audit=len(sys.argv)>2 and sys.argv[2]=='audit'
a=(36497+len(t.get('audit_ids_used',[]))) if is_audit else t['next_unused_id']
assert 36400<=a<=36499 and a not in t['used_ids']
if not is_audit:assert a<36497
# Check other jobs' receipt directory names as well as shared sent ledgers.
root=H.parent
collision=[]
for base,dirs,files in os.walk(root):
 if Path(base)==H:
  dirs[:]=[]
  continue # Own charged IDs are checked by TALLY; retained refusals do not consume IDs (m').
 depth=len(Path(base).relative_to(root).parts)
 if depth>=5: dirs[:]=[]
 dirs[:]=[d for d in dirs if d not in {'target','sbf-target','charon-target','node_modules','.git','source','sources','.lake','objects','lean-objects','lean','generated','src','rebuild-objects'}]
 for name in dirs+files:
  if re.search(r'(?<![A-Za-z0-9])'+str(a)+r'(?![A-Za-z0-9])',name): collision.append(str(Path(base)/name))
 for name in files:
  if name=='sent.txt':
   for line in (Path(base)/name).read_text().splitlines():
    fields=line.split()
    if len(fields)>2 and fields[2]==str(a):collision.append(str(Path(base)/name)+':'+line)
assert not collision,collision
# Reject IDs already used by the existing shared launcher, including refusals.
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
assert not (T/f'out-{a}.log').exists(),a
srcsha=hashlib.sha256(p.read_bytes()).hexdigest();env=json.loads(JENV.read_text());search=[str(O)]+env['LEAN_PATH'].split(':')
imports=re.findall(r'^import (\S+)',p.read_text(),re.M);assert not any(x.startswith('XR') for x in imports);deps={}
for imp in imports:
 q=next((Path(x)/(imp.replace('.','/')+'.olean') for x in search if (Path(x)/(imp.replace('.','/')+'.olean')).exists()),None)
 deps[imp]=dict(path=str(q) if q else None,sha256=hashlib.sha256(q.read_bytes()).hexdigest() if q else 'missing')
context=dict(deps)
if '.' in module: context['private_output_parent']={'path':str(outfile.parent),'exists':outfile.parent.is_dir(),'reason':'created nested private output directory after charged 37968 write failure'}
fp=hashlib.sha256(json.dumps(context,sort_keys=True).encode()).hexdigest();key=srcsha+':'+fp
assert key not in t.get('sent_inputs',[]),'unchanged source/dependencies refused'
t['used_ids'].append(a)
if is_audit:t.setdefault('audit_ids_used',[]).append(a)
else:t['next_unused_id']=next((i for i in range(36400,36497) if i not in t['used_ids']),36497)
state.write_text(json.dumps(t,indent=2)+'\n')
label=f'lean-{a}'
retry=0
while (H/label).exists():
 assert not (H/label/'receipt/receipt.json').exists(), 'charged ID cannot be retried'
 retry+=1;label=f'lean-{a}-r{retry}'
sub=dict(attempt=a,module=module,source_sha256=srcsha,dependency_objects=deps,deps_fingerprint=fp,source_revision=(H/'revision').read_text().strip(),source_revision_kind='Rust source freeze; Lean source is exact SHA snapshot in source.lean',environment='J',environment_sha256=hashlib.sha256(JENV.read_bytes()).hexdigest(),original_environment_sha256=hashlib.sha256(ORIGINAL_JENV.read_bytes()).hexdigest(),private_sources=str(S),private_objects=str(O),shared_sources_written=False)
if '.' in module:
 authority=json.loads((H/'project-resolution.json').read_text())['modules'][module]
 assert srcsha==authority['sha256'],(module,srcsha,authority)
 sub['project_source_authority']=authority
 sub['compile_environment_change']=context['private_output_parent']
authority=json.loads((H/'project-resolution.json').read_text())['modules'][module]
assert srcsha==authority['sha256'],(module,srcsha,authority)
sub['project_source_authority']=authority
cmd=['timeout','900','python3',str(DRIVER),str(JENV),str(O),str(S),str(O/(module.replace('.','/')+'.olean')),str(p),'7000']
status=run(label,cmd,'one focused Lean module via pinned run2.py, env J, -M7000; private source/object overlay')
sub['lean_source_revision']=(H/'proof-revision').read_text().strip() if (H/'proof-revision').exists() else 'see SHA-matched source snapshot and own source authority record'
sub['source_authority_record']='project-resolution.json / d324-private-source-authority.json, h5 own HEAD; external h4 verified'
R=H/label;(R/'source.lean').write_bytes(p.read_bytes());(R/'submission.json').write_text(json.dumps(sub,indent=2)+'\n')
charged=(R/'receipt/receipt.json').exists()
if charged:
 t['lean_attempts']+=1;t.setdefault('sent_inputs',[]).append(key)
 log=(R/'receipt/stdout.log').read_text()+(R/'receipt/stderr.log').read_text()
 rec=json.loads((R/'receipt/receipt.json').read_text());rec.update(sub);rec['print_axioms']=re.findall(r"^.*(?:depends on axioms|does not depend on any axioms).*(?:\n\s+.*)?",log,re.M);rec['charged_lean_attempt']=True;(R/'receipt/receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 t.setdefault('receipts',[]).append(dict(attempt=a,module=module,exit=status,receipt=str(R/'receipt/receipt.json')))
else:
 t.setdefault('refusals',[]).append(dict(attempt=a,module=module,exit=status,charged_lean_attempts=0,label=label,ruling='m\u2032'))
 t['used_ids'].remove(a)
 if is_audit:t['audit_ids_used'].remove(a)
 else:t['next_unused_id']=a
state.write_text(json.dumps(t,indent=2)+'\n');print(json.dumps(dict(attempt=a,module=module,exit=status,charged=charged,lean_attempts=t['lean_attempts'],next_unused_id=t['next_unused_id'])),flush=True)
sys.exit(status)
