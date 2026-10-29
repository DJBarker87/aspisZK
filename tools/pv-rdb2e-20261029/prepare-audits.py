from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2e-20261029';P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
# Record exact current source closure. No source locator fallback is used.
external={r['module'].replace('/','.')for r in json.loads(subprocess.check_output(['git','show','HEAD:evidence/pv-replay-20261027/receipts/external-object-manifest.json']))}
modules={}
def visit(m):
 if m in external or m in modules:return
 assert m.startswith(('R1Z.PV_RDB2E_','R1Z.PV_RDB2D_')),m
 p=P/(m.split('.')[-1]+'.lean');raw=p.read_bytes();rel=str(p.relative_to(R));committed=subprocess.check_output(['git','show','HEAD:'+rel]);assert committed==raw,m
 deps=re.findall(r'^import (\S+)',raw.decode(),re.M)
 modules[m]=dict(source_path=rel,source_sha256=hashlib.sha256(raw).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip(),imports=deps)
 for d in deps:visit(d)
roots=['R1Z.'+p.stem for p in sorted(P.glob('PV_RDB2E_*.lean')) if not any(x in p.stem for x in ['Audit','Replay'])]
for root in roots:visit(root)
# Collect full declaration names printed by admitted independent focused compiles.
printed=set()
for p in E.glob('lean-*/receipt.json'):
 j=json.loads(p.read_text());m=j['module'].replace('/','.')
 if j['exit']!=0 or m not in modules:continue
 if j['source_sha256']!=modules[m]['source_sha256']:continue
 for line in j['print_axioms']:
  name=re.match(r"'([^']+)'",line)[1];printed.add(name)
# Every live new-module theorem must have a print in its own source. Namespace
# qualification is independently checked by the final named-command elaboration.
def strip(s):
 s=re.sub(r'/--.*?-/|/-.*?-/',lambda m:'\n'*m[0].count('\n'),s,flags=re.S);return re.sub(r'--[^\n]*','',s)
declared=[]
for m,r in modules.items():
 if not m.startswith('R1Z.PV_RDB2E_'):continue
 s=strip((R/r['source_path']).read_text());stack=[]
 for line in s.splitlines():
  x=line.strip()
  ns=re.match(r'namespace\s+(\S+)',x)
  if ns:stack.append(('namespace',ns[1]));continue
  if re.match(r'(?:noncomputable\s+)?section\b',x):stack.append(('section',''));continue
  if re.match(r'end(?:\s|$)',x):
   assert stack,(m,x);stack.pop();continue
  th=re.match(r'(?:private\s+)?theorem\s+([^\s({:]+)',x)
  if th:
   name='.'.join([v for k,v in stack if k=='namespace']+[th[1]])
   declared.append(dict(name=name,module=m))
   assert '#print axioms '+th[1] in s or '#print axioms '+name in s,(m,name)
assert all(x['name']in printed for x in declared),[x for x in declared if x['name']not in printed]
plan=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),roots=roots,modules=modules,excluded='sampler-cohort-stop.json',named_declarations=sorted(printed),theorems=declared,scope='independent SHA/pointer/from_fn models; no original sampler or native row restoration')
(E/'frozen-proof-manifest.json').write_text(json.dumps(plan,indent=2))
(E/'audit-declarations.json').write_text(json.dumps(dict(theorems=declared,printed=sorted(printed)),indent=2))
base=''.join('import '+m+'\n'for m in roots)
statements=['R1Z.PV_RDB2E_ShaHandles.complete_typed','R1Z.PV_RDB2E_ShaHandles.callback_run','R1Z.PV_RDB2E_Dispatch.full_dispatch','R1Z.PV_RDB2E_ConcreteSoft.all_fields','R1Z.PV_RDB2E_ConcreteSoft.both_backends','R1Z.PV_CBL_FallbackBlockTotal.total','R1Z.PV_RDB2E_PointerOffsets.nonempty','R1Z.PV_RDB2E_FromFn.length']
(P/'PV_RDB2E_StatementAudit.lean').write_text(base+'\n'.join('#print '+n+'\n#print axioms '+n for n in statements)+'\n')
(P/'PV_RDB2E_AxiomsAudit.lean').write_text(base+'\n'.join('#print axioms '+n for n in sorted(printed))+'\n')
(P/'PV_RDB2E_FocusedReplay.lean').write_text(base+'\n'.join('#check '+n+'\n#print axioms '+n for n in statements)+'\n')
print(json.dumps(dict(modules=len(modules),theorems=len(declared),named_declarations=len(printed),sampler_excluded=True)))
