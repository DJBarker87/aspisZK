from pathlib import Path
from collections import deque
import subprocess,json,re,hashlib
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean';e=r/'evidence/pv-join-20261026/wire';rows=json.loads((e/'rows-before.json').read_text());items=json.loads((e/'operations.json').read_text());root='R1Z.PV_Join_Wire_Caller';root_module='R1Z.PV_Join_Wire_FinalAuditA'
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
def file(m):
 f=p/(m.replace('.','/')+'.lean')
 if not f.exists() and m.startswith('R1Z.ProverRwFull'):f=r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/(m.split('.')[-1]+'.lean')
 return f
def path(start,dest):
 q=deque([(start,[start])]);seen=set()
 while q:
  m,chain=q.popleft()
  if m==dest:return chain
  if m in seen:continue
  seen.add(m);f=file(m)
  if f.exists():
   for line in f.read_text().splitlines():
    if line.startswith('import '):
     for child in line[7:].split():q.append((child,chain+[child]))
 return None
# Extract independently checked declaration closure, as distinct from imports.
closures={}
for f in sorted(e.glob('*-out.log')):
 receipt=e/(f.name.replace('-out.log','-receipt.json'))
 if not receipt.exists() or json.loads(receipt.read_text())['validation_exit']!=0:continue
 for m,names in re.findall(r'JOIN_CLOSURE (\S+):\s*\[([\s\S]*?)\]',f.read_text()):closures[m]=re.findall(r'R1Z\.[A-Za-z0-9_.]+',names)
proof=closures.get(root+'.refinement_of_data',[]);before=closures.get('R1Z.PV_Join_AggregateCaller.refinement_of_data',[])
results=[]
for row in rows:
 law=row['theorems'][0] if row['theorems'] else None
 chain=path(root_module,law.rsplit('.',1)[0]) if law else None
 reason=None if chain else 'V270 is a scoped Formatter inadmissible-axiom diagnostic; Recount 3 names no closing theorem or operation. Native Formatter adequacy remains V269.'
 results.append(dict(**row,after_import='candidate' if chain else 'neither',import_path=chain,reason=reason,proof_consumed=law in proof if law else False,before_proof_consumed=law in before if law else False,path_sources=[dict(module=m,path=str(file(m).relative_to(r)),sha256=hashlib.sha256(file(m).read_bytes()).hexdigest()) for m in chain] if chain else []))
x=dict(source_revision=rev,consumer=root+'.refinement_of_data',consumer_module=root_module,old_consumer='R1Z.PV_Join_AggregateCaller.refinement_of_data',recount3_baseline=dict(candidate=17,neither=10,research=0),rows=results,consumed_laws=proof,before_consumed_laws=before,extra_op51=next(x for x in items if x['op']==51))
(e/'import-chain.json').write_text(json.dumps(x,indent=2)+'\n')
s='# Candidate consumer import and application chains\n\nOrganisation of proved facts, not premise discharge. **Target not yet established.**\n\n'
s+=f'Consumer: `{root}.refinement_of_data`, defined in `{root_module}`. Source revision: `{rev}`. The historical `PV_Join_AggregateCaller.refinement_of_data` remains unchanged. This new caller is the source-wired extension of its P6 aggregate baseline; the final combined audit covers both.\n\n'
s+='Recount 3 baseline: research/candidate/neither **0/17/10**. After wiring: **0/26/1**, for the same 27 rows. All 26 source-law rows are imported and checked as declaration dependencies; V270 has no closing operation theorem. Extra arbitrary-carrier op51 is consumed but remains OPEN under Recount 3; this work does not reclassify its P6/native obligations.\n\n'
s+='The new source selection installs the cb4/cb5 exact laws for 84, 105, 107, 109 and 118, the arbitrary-carrier 51 law, and the native carrier needed for 229. It does not prove equality of every new selection to the historical one. No new proposition hypothesis is added: reservation and the full proof/audit data equality remain. Native source/effect/model/release obligations are retained. The research headline imports none of this work; no headline credit is claimed.\n\n'
s+='Every path below lists **module imports**, followed by its closing declaration. `proof consumed` is separately derived from the compiled declaration graph. Machine-readable source hashes and paths are in `import-chain.json`.\n\n| Row | Recount 3 import | Closing theorem | Consumer import path | Proof consumed |\n|---|---|---|---|---|\n'
for row in results:
 law=row['theorems'][0] if row['theorems'] else 'none named'
 chain=' → '.join('`'+m+'`' for m in row['import_path']) if row['import_path'] else 'not reachable: '+row['reason']
 s+=f"| {row['row']} | {row['before']} | `{law}` | {chain} | {row['proof_consumed']} |\n"
s+='\n## Previously unconsumed source laws\n\nThe old consumer declaration graph is distinct from the Recount 3 import column. The following closing declarations are absent from its proof dependencies:\n\n'
for row in results:
 if row['theorems'] and not row['before_proof_consumed']:s+='- '+row['row']+': `'+row['theorems'][0]+'`\n'
s+='\n## Extra op51\n\n`'+root+'` → `R1Z.PV_Join_Wire_Dictionary` → `R1Z.PV_Join_Wire_Entry51` → `R1Z.PV_Join_Wire_Op51` → `R1Z.PV_CB3_Op51Arbitrary.op51_source`. All raw carriers and complete Result are preserved. No native gate was rerun (no Kani).\n'
(e/'IMPORT-CHAIN.md').write_text(s)
print('import candidate/neither',sum(bool(x['import_path']) for x in results),sum(not x['import_path'] for x in results),'proof laws',len(proof),'before',len(before))
