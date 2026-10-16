#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess
b=Path(__file__).resolve().parent;root=b.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=b/'runs/completed-decode-a';r=json.loads((a/'receipt.json').read_text());m=json.loads((b/'input-manifest-completed-decode-a.json').read_text())
assert r['target']=='ExtractedPrefixCompletedDecode' and r['exit_status']==0
assert r['source_sha256']==sha(a/'source.lean')==sha(root/'docs/research/100bit-spend-path-20261013/lean/ExtractedPrefixCompletedDecode.lean')
assert r['runner_sha256']==sha(a/'runner.py') and r['input_manifest_sha256']==sha(b/'input-manifest-completed-decode-a.json')
assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
assert r['process_swaps']==0 and r['cgroup_swap_current']=='0' and r['memory_events_before']==r['memory_events_after']
assert '4.32.0' in r['lean_version'] and len(r['runtime_sha256'])==4
prior=b.parent/'r18-prefix-typed-semantic-20261016'
pr=json.loads((prior/'runs/typed-full-b/receipt.json').read_text());pm=json.loads((prior/'input-manifest-typed-full-b.json').read_text())
assert m['new_import_objects']['ExtractedPrefixTypedFull.olean']==pr['olean_sha256']
assert m['new_sources']['ExtractedPrefixTypedFull.lean']==pr['source_sha256']
for n,h in pm['new_import_objects'].items():assert m['new_import_objects'][n]==h
log=(a/'lean.log').read_text();reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
assert len(reports)==1 and reports[0][0]=='AspisR1.ExtractedPrefixCompletedDecode.completed_decode'
assert {s.strip() for s in reports[0][1].split(',')}<={'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in log and 'error:' not in log
assert json.loads((b/'output-object-pins.json').read_text())=={r['target']:r['olean_sha256']}
# The large closure is inventoried only. No object from it is imported here.
f=json.loads((b/'current-source-frontier.json').read_text());cat=f['catalog']
assert not f['unmapped_project_imports']
assert f['receipt_sets']['r17_inventory_sha256']==sha(b/'r17-producing-inventory.json')
def imports(text):
 clean=[];i=0;depth=0
 while i<len(text):
  if text.startswith('/-',i):depth+=1;i+=2;continue
  if depth and text.startswith('-/',i):depth-=1;i+=2;continue
  if depth:
   if text[i]=='\n':clean.append('\n')
   i+=1;continue
  if text.startswith('--',i):
   while i<len(text) and text[i]!='\n':i+=1
   continue
  clean.append(text[i]);i+=1
 result=[]
 for line in ''.join(clean).splitlines():
  s=line.strip()
  if not s or s=='prelude':continue
  if s.startswith('public import '):result+=s[14:].split()
  elif s.startswith('import '):result+=s[7:].split()
  else:break
 return result
for n,x in cat.items():
 data=subprocess.check_output(['git','show',f['source_revision']+':'+x['source']],cwd=root)
 assert hashlib.sha256(data).hexdigest()==x['source_sha256'] and imports(data.decode())==x['imports']
for target,c in f['closures'].items():
 seen=set()
 def walk(n):
  if n not in cat or n in seen:return
  seen.add(n)
  for dep in cat[n]['imports']:walk(dep)
 walk(target)
 assert sorted(seen)==c['modules'] and len(seen)==c['project_module_count']
 assert sorted(n for n in seen if not cat[n]['source_matching_receipt_sets'])==c['without_source_matching_receipt_in_audited_sets']
for line in (b/'SHA256SUMS').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(b/p)==h,p
print('PASS:one new generic bridge; standard-only audit; exact current dependency/source/runtime/resource pins;337/341/377 source-only import inventories; no Selected closure replay')
