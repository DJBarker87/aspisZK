"""Full type/axiom receipts for every explicitly declared Pool theorem."""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent;x=json.loads((E/'NGK_PROVENANCE.json').read_text())
records=[]
for r in x['files']:
 for m in re.finditer(r'(?m)^(?:private )?theorem\s+([^\s({:]+)',r['after_body']):
  records.append(dict(name=r['target_module']+'.'+m[1],source_module=r['source_module'],source_path=r['source_path'],source_sha256=r['source_sha256']))
assert len({r['name'] for r in records})==len(records)
# Thirty-three disjoint groups cover every declared statement exactly once.
# These are statement review receipts, not a repeated full manifest.
groups=[records[i::33] for i in range(33)]
for i,rs in enumerate(groups):
 assert rs
 text='import Lean\nimport NGK_COMBINED_IMPORT\nopen Lean\nset_option pp.universes true\nset_option pp.explicit true\n'+''.join('#check @'+r['name']+'\n#print axioms '+r['name']+'\n' for r in rs)
 text+='\nrun_cmd do\n let env ← Lean.getEnv\n'
 for r in rs:
  name=r['name'];mod='NGK_'+r['source_module']
  text+=' let n := `'+name+'\n let some idx := env.getModuleIdxFor? n | throwError \"missing selected theorem owner\"\n unless env.header.moduleNames[idx.toNat]! == `'+mod+' do throwError \"wrong selected theorem owner\"\n let some ci := env.find? n | throwError \"missing theorem constant\"\n unless ci.isTheorem do throwError \"selected constant is not a theorem\"\n let entry := Json.mkObj [(\"name\",toJson n.toString),(\"owner\",toJson env.header.moduleNames[idx.toNat]!.toString),(\"type\",toJson (reprStr ci.type))]\n logInfo m!\"NGK_CERT_ENTRY {entry.compress}\"\n'
 if i==0:text+='#check @NFY_OwnerTransport.map_err_transport\n#print axioms NFY_OwnerTransport.map_err_transport\n'
 (E/f'NGK_Statements{i:02}.lean').write_text(text)
(E/'NGK_STATEMENT_MANIFEST.json').write_text(json.dumps(dict(records=records,groups=groups,all_statements_once=True,classification='complete kernel-elaborated statement and printed axiom review; not native/source implementation closure'),indent=1)+'\n')
print(len(records),'explicit theorems in',len(groups),'disjoint statement groups')
