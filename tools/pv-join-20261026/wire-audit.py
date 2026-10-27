# Retained initial-stage generator. Final sources include reviewed proof corrections.
raise SystemExit('Retired draft generator; use the pinned final source files and combined-audit-manifest.json')
# Historical partition generator; retired after attempt 39357.
# The final exact coverage is pinned by wire/combined-audit-manifest.json and
# the two committed final audit sources. Do not regenerate them from this draft.
from pathlib import Path
import re,json,hashlib
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'evidence/pv-join-20261026/wire'
items=json.loads((e/'operations.json').read_text())
# Cover all historical modules, retaining inherited statement/axiom inventory.
old=json.loads((e.parent/'resume5/combined-audit-manifest.json').read_text())
names=set(old['theorems_or_functions'])
names.update(x['theorem'] for x in items)
names.update(f"R1Z.PV_Join_Wire_Entry{x['op']}.equation" for x in items)
names.update(['R1Z.PV_Join_Wire_Dictionary.dictionary','R1Z.PV_Join_Wire_Caller.refinement_of_data'])
# Include every lexical theorem not already in the inherited audit manifest.
files=sorted(f for f in p.glob('PV_Join_*.lean') if f.stem not in {'PV_Join_Wire_FinalAuditA','PV_Join_Wire_FinalAuditB','PV_Join_Wire_CombinedAudit'})
for f in files:
 s=f.read_text();ns=re.search(r'^namespace (\S+)',s,re.M)
 if ns and f.stem!='PV_Join_Wire_ConstantEntries':
  names.update(ns[1]+'.'+n for n in re.findall(r'^theorem (\S+)\s',s,re.M))
names=sorted(names);head='R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed'
# Both portions have disjoint statement/axiom inventories and import coverage.
for k,suffix in enumerate(['A','B']):
 group=files[len(files)*k//2:len(files)*(k+1)//2]
 part=names[len(names)*k//2:len(names)*(k+1)//2]
 # All names may be declared in either group. Import the prior combined audit
 # and current caller plus all entries to expose the complete symbol inventory.
 imports=sorted(set(['R1Z.PV_Join_CombinedAudit5','R1Z.PV_Join_Wire_FinalAuditA']+['R1Z.'+f.stem for f in group]+[f"R1Z.PV_Join_Wire_Op{x['op']}" for x in items]))
 
 if k==0:
  imports=[m for m in imports if m!='R1Z.PV_Join_Wire_FinalAuditA']
 body=(r/'tools/pv-join-20261026/wire-caller.lean.txt').read_text() if k==0 else ''
 body='\n'.join(l for l in body.splitlines() if not l.startswith('import '))+'\n' if body else ''
 text=''.join('import '+m+'\n' for m in imports)+'\n'+body+''.join('#print '+n+'\n#print axioms '+n+'\n' for n in part)
 (p/f'PV_Join_Wire_FinalAudit{suffix}.lean').write_text(text)
text='import R1Z.PV_Join_Wire_FinalAuditA\nimport R1Z.PV_Join_Wire_FinalAuditB\nimport R1Z.PrivacyR1HeadlineDeployedReal\n\n'
text+=''.join('#print axioms '+n+'\n' for n in names+[head]+[x['source_law'] for x in items])
text+='#join_closure R1Z.PV_Join_Wire_Caller.refinement_of_data\n'
(p/'PV_Join_Wire_CombinedAudit.lean').write_text(text)
(e/'combined-audit-manifest.json').write_text(json.dumps(dict(modules=[dict(module='R1Z.'+f.stem,sha256=hashlib.sha256(f.read_bytes()).hexdigest()) for f in files],theorems_or_functions=names,consumed_laws=[x['source_law'] for x in items],headline=head,targets=['R1Z.PV_Join_Wire_FinalAuditA','R1Z.PV_Join_Wire_FinalAuditB','R1Z.PV_Join_Wire_CombinedAudit'],kind='one final combined dependency/axiom audit against retained host objects, not a clean release replay'),indent=2)+'\n')
print(len(files),'PV_Join modules;',len(names),'inherited/new declarations;',len(items),'consumed laws')
