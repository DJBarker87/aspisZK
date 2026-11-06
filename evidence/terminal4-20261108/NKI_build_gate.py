from pathlib import Path
import json,re,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent
entries=[json.loads(l)for l in(E/'NKI_ATTEMPTS.jsonl').read_text().splitlines()];passed={}
for x in entries:
 m=x.get('module','');p=E/(m+'.lean')
 if x.get('kind')!='lean' or x['exit_status']!=0 or not m.startswith('NKI_') or not p.is_file():continue
 if m in ['NKI_Driver','NKI_ProofDriver','NKI_COMBINED_IMPORT']:continue
 if x['source_hashes'].get(m+'.lean')!=hashlib.sha256(p.read_bytes()).hexdigest():continue
 passed[m]=x['attempt']
roots=[]
for m in sorted(passed):
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace ([\w.]+)',s,re.M)
 if ns:roots +=[ns[1]+'.'+n for n in re.findall(r'^(?:@\[step\] )?theorem ([\w.]+)',s,re.M)]
required=['AspisR1.NKI_AppendRoot.source','AspisR1.NKI_LevelsComplete.source','AspisR1.NKI_InitialRoot.source','AspisR1.NKI_ValueRoot.source'];assert set(required)<=set(roots)
modules=['NKC_COMBINED_IMPORT','NJX_COMBINED_IMPORT']+sorted(passed)
s=''.join('import '+m+'\n'for m in modules)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n'
for r in sorted(set(roots)):s+='#check '+r+'\n#print axioms '+r+'\n'
(E/'NKI_COMBINED_IMPORT.lean').write_text(s)
expected={};baselines=[]
for p in [E.parent/'ledger17-20261108/NKC_EXPECTED_IMPORTS.jsonl',E.parent/'terminal3-20261108/NJX_EXPECTED_IMPORTS.jsonl']:
 baselines.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 for row in map(json.loads,p.read_text().splitlines()):
  assert row['module']not in expected or expected[row['module']]==row['imports'],row['module']
  expected[row['module']]=row['imports']
sourcepins=[]
for p in [E/(m+'.lean')for m in passed]+[E/'NKI_COMBINED_IMPORT.lean']:
 imports=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)));expected[p.stem]=imports
 sourcepins.append(dict(module=p.stem,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=imports))
(E/'NKI_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n'for m,im in sorted(expected.items())))
(E/'NKI_GATE_SOURCES.json').write_text(json.dumps(dict(baselines=baselines,source_extensions=sourcepins,passed=passed),indent=1))
allroots=sorted(set(roots+json.load(open(E.parent/'ledger17-20261108/NKC_AUDIT_ROOTS.json'))['roots']+json.load(open(E.parent/'terminal3-20261108/NJX_AUDIT_ROOTS.json'))['roots']))
# Allocation may be split further BEFORE any raw root is submitted. Never rewalk
# an unchanged completed group; one unique complete-root partition only.
count=28;groups=[allroots[i*len(allroots)//count:(i+1)*len(allroots)//count]for i in range(count)]
assert len(set(sum(groups,[])))==len(allroots)==sum(map(len,groups))
(E/'NKI_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=groups,new_roots=sorted(set(roots)),reason='FIRST NKC+NJX+NKI selected-cohort proof-body audit, same canonical JFw owners as NJX; disjoint complete partition'),indent=1))
(E/'NKI_AUDIT_MODULES.json').write_text(json.dumps([['NKI_COMBINED_IMPORT']]*count))
basepath=E.parent/'ledger17-20261108/NKC_LEDGER.json.xz';raw=lzma.decompress(basepath.read_bytes());base=json.loads(raw)
rows={x['row']:x for x in base['rows']};new=[]
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
text=subprocess.check_output(['git','show',rev+':crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs']).decode()
def body(name):
 p=text.index('fn '+name+'(');p=text.index('{',p);q=p+1;depth=1
 while depth:depth+=(text[q]=='{')-(text[q]=='}');q+=1
 return text[p+1:q-1]
for row,name,owner,domain,pairs in [
 ('TX1:234','append_level_packed_selector_tensor','NKI_AppendRoot','SAME index:anyU64; level<20; canonical frontier8/opened16/high', [['NKI_K001','NKI_K002']]),
 ('TX1:235','append_levels_packed_selector_tensor','NKI_LevelsComplete','SAME index:anyU64; canonical frontier20x8/opened16/high64;234at EACH actual argument', [['NKI_K001','NKI_K002'],['NJL_K059','NJL_K060']]),
 ('TX1:260','semantic_initial_and_absorption','NKI_InitialRoot','arbitrary SAME public; canonical opened.z16/selectors.high64/low16;227 SAME5scalars/opened', [['NKI_K009','NKI_K010']]),
 ('TX1:233','add_value_lanes','NKI_ValueRoot','SAME packed24 and all3opened16views/selectors.high64/low16 canonical; shared49/conservation82 complete', [['NKI_K003','NKI_K004'],['NKI_K005','NKI_K006']])]:
 assert rows[row]['status']=='OPEN'
 new.append(dict(rows=[row],function=rows[row]['function'],frozen_body_sha256=hashlib.sha256(body(name).encode()).hexdigest(),route='(y)/(ai)(5)/(ad)/(aq)/(aq)(5)/(au) direct P6 hybrid',root_domain=domain,native_pairs=pairs,lean_roots=['AspisR1.'+owner+'.source'],owner_module=owner,complete_carrier=True,premise_policy='Only actual typed root inputs/canonicality/bounds; all child Results/domains/frames internally derived; no endpoint/success/Run/Ops hypothesis',trust='P6/D188 option A RECLASSIFICATION; inherited ABI/std/allocator/compiler/source-to-ELF retained; none added or removed',status='CANDIDATE',local_gate='PENDING',credit_waits_next_ledger_gate=True))
(E/'NKI_CLOSED.json').write_text(json.dumps(dict(frozen_revision=rev,headline='AspisR1.RPx_Deployed.deployed',functions=new,target_established=False),indent=2))
(E/'NKI_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline='evidence/ledger17-20261108/NKC_LEDGER.json.xz',baseline_uncompressed_sha256=hashlib.sha256(raw).hexdigest(),authoritative_delta=0,requested_rows=[r['rows'][0]for r in new],source_only=['TX1:232'],support_only=['TX1:251'],next_ledger_required=True,target_established=False),indent=2))
print(json.dumps(dict(passed_modules=len(passed),new_roots=len(set(roots)),total_raw_roots=len(allroots),raw_groups=count,import_conflicts=0,candidate_rows=4)))
