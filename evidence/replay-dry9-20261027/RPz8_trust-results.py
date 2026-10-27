"""Classify historical formatter names using fresh checked kernel declarations."""
from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;R=E.parents[1]
read=lambda p:json.loads(p.read_text());parse=lambda text,tag:[json.loads(l.split(tag,1)[1]) for l in text.splitlines() if tag in l]
log=(E/'RPz8_666/stdout.log').read_text();kind=parse(log,'RPZ8_FORMATTER_KIND ')[0];roots=parse(log,'RPZ8_FORMATTER_TRUST ');inventory=parse((E/'RPz8_667/stdout.log').read_text(),'RPZ8_FORMATTER_INVENTORY ');byname={r['name']:r for r in inventory};standard={'propext','Classical.choice','Quot.sound'}
assert len(inventory)==85 and sum(r['isAxiom'] for r in inventory)==84
assert kind['kind']=='definition' and not kind['isAxiom']
for x in roots:
 assert set(x['uncached_axiom_info_names'])==standard
 root=x['root'].split('.')[-2];attempt='360' if root=='Rc10_Top' else '657';headers={r['module']:r['imports'] for r in parse((E/f'RPz8_{attempt}/stdout.log').read_text(),'RPZ8_IMPORTS ')}
 target='Aeneas.Std.Core.Fmt';queue=[['RPz8_'+root]];seen=set();import_path=[]
 for path in queue:
  n=path[-1]
  if n==target:import_path=path;break
  if n in seen:continue
  seen.add(n);queue.extend(path+[k] for k in headers.get(n,[]) if k not in seen)
 assert import_path
 x['exact_import_path']=import_path
 closure=set(read(E/('RPz8_'+root+'-reachable-constants.json')))
 x['historical_name_records']=[{**i,'reachable':i['name'] in closure} for i in inventory]
 x['reachable_actual_formatter_axioms']=sum(r['isAxiom'] and r['reachable'] for r in x['historical_name_records'])
 assert x['reachable_actual_formatter_axioms']==0
out={'historical_nonstandard_names':85,'actual_axiom_declarations':84,'actual_definitions':1,'formatter_kind':kind,'library_pin':read(E/'RPz8_Formatter-library-pin.json'),'roots':roots,'qualification':'The historical cached nonstandard-name list is not an actual declaration-kind inventory. Formatter is reachable but definitionally Unit on the pinned coherent library. No library/source change was made. All 84 actual formatter axioms and all 180 named implementation records are unreachable from either fresh root. Uncached complete kernel traversal finds exactly the three standard axioms.'}
(E/'RPz8_formatter-axiom-reachability.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# Fresh formatter classification','','The historical audit lists 85 nonstandard names. Fresh checked-kernel inventory RPz8_667 classifies **84 as axioms and one as a definition**. The latter is `Aeneas.Std.core.fmt.Formatter := Unit`; it is not an axiom. The pinned coherent library object is SHA256 `'+out['library_pin']['sha256']+'` ('+str(out['library_pin']['bytes'])+' bytes), resolved exactly as RPz8_Formatter-library-pin.json records. It was already in the retained trusted base; no object or source was replaced.','','All 180 named formatter implementation records remain unreachable. All 84 actual formatter axioms are also unreachable. The pure Formatter type definition is reachable. RPz8_666 records exact proof paths and uncached axiom inventories; both roots have exactly propext, Classical.choice and Quot.sound. This matches their raw #print axioms results. The full per-name classification is RPz8_formatter-axiom-reachability.json.','','No historical raw audit output is edited. The earlier label “85 nonstandard axioms” is corrected here to “85 historical nonstandard names”. This is an audit classification correction, not a discharged premise or a library/model repair. The all-declaration standard-only gate remains false because the 84 native formatter axioms still exist.']
for x in roots:
 lines+=['','## '+x['root'],'','Proof dependency path (the final edge is a type reference):','',' → '.join('`'+n+'`' for n in x['path']),'','Exact import path:','',' → '.join('`'+n+'`' for n in x['exact_import_path'])]
(E/'RPz8_FORMATTER-CLASSIFICATION.md').write_text('\n'.join(lines)+'\n')
p=E/'RPz8_FORMATTERS.md';s=p.read_text();s=s.replace('The existing 180 formatter-family declarations and 85 nonstandard axioms remain\nin the imported source/library corpus. The all-declaration standard-only gate\ntherefore remains false for that retained corpus.', 'The retained corpus contains the 180 historical formatter records. Its list of 85 historical nonstandard names classifies freshly as 84 actual native formatter axioms plus the definition Formatter := Unit. The pure definition is reachable; all 84 actual axioms are unreachable. RPz8_FORMATTER-CLASSIFICATION.md records both exact paths and uncached standard-only root audits. The all-declaration standard-only gate remains false for the retained corpus.')
p.write_text(s)
print('Classified',len(inventory),'historical names; both uncached axiom inventories standard-only')
