"""Independently check Lean receipts, import DAGs and exhaustive visited sets."""
import collections,hashlib,json,lzma,re,sys
from pathlib import Path
E=Path(__file__).resolve().parent; R=E.parents[1]
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def parse(path):
 result={};rows=[];mods={}
 for line in path.read_text().splitlines():
  if line.startswith('NDP_RESULT '):result=json.loads(line[11:])
  if line.startswith('NDP_AXIOM '):rows.append(json.loads(line[10:]))
  if line.startswith('NDP_MODULE '):
   m=json.loads(line[11:]);assert m['module'] not in mods;mods[m['module']]=m
 assert result and 'NDP_AUDIT_COMPLETE' in path.read_text()
 return result,rows,mods
summaries={};inventories={};files={};closures={}
for label,attempt,previous,count,nreach in [('Headline','NDP_R005','NDJ_R002',12712,115256),('Joint','NDP_R007','NDJ_R004',15068,885779)]:
 stem='NDP_'+label;p=E/attempt
 receipt=json.loads((p/'receipt.json').read_text());assert receipt['exit_status']==0 and str(receipt['swaps'])=='0'
 assert receipt['limits']['memory.swap.max']=='0' and receipt['limits']['pids.max']=='64'
 expected_limits=('6442450944','8589934592','-M7000') if label=='Headline' else ('15032385536','17179869184','-M15000')
 assert (receipt['limits']['memory.high'],receipt['limits']['memory.max'])==expected_limits[:2]
 assert expected_limits[2] in receipt['command']
 for name,digest in receipt['source_hashes'].items():
  assert sha((p/'sources'/name).read_bytes())==digest
  assert sha((E/name).read_bytes())==digest
 result,rows,mods=parse(p/'stdout.log')
 seen_raw=lzma.decompress((E/(stem+'_REACHABLE.txt.xz')).read_bytes())
 assert sha(seen_raw)==(E/(stem+'_REACHABLE.txt.sha256')).read_text().split()[0]
 names=seen_raw.decode().splitlines();seen=set(names);assert len(names)==len(seen)==result['reachable_constants']==nreach
 closure=set();pending=[result['root_module']]
 while pending:
  m=pending.pop()
  if m in closure:continue
  closure.add(m);pending+=mods[m]['imports']
 assert len(closure)==count==result['closure_modules']
 closures[label]=closure
 assert all(x['in_root_import_closure']==(m in closure) for m,x in mods.items())
 assert len(rows)==len({x['name'] for x in rows})==result['all_loaded_axioms']==result['serialized_axioms']
 assert all(x['reachable']==(x['name'] in seen) for x in rows)
 assert all(x['in_root_import_closure']==(x['module'] in closure) for x in rows)
 assert all(x['module'] in mods and x['type'] and x['type_expr'] for x in rows)
 reached={x['name'] for x in rows if x['reachable']}
 assert reached==set(result['walked_axioms'])==set(result['collect_axioms'])
 assert len(receipt['print_axioms'])==1
 line=receipt['print_axioms'][0]
 printed=set(re.sub(r'\.\{[^}]*\}','',line.split('depends on axioms: [')[1].removesuffix(']')).split(', '))
 assert reached==printed==STANDARD,(label,reached,printed)
 old=(R/'evidence/native-l188-20261028'/previous/'stdout.log').read_text()
 old_rows=[json.loads(l[len('NDJ_IMPORT_AXIOMS '):]) for l in old.splitlines() if l.startswith('NDJ_IMPORT_AXIOMS ')]
 assert len(old_rows)==1 and set(old_rows[0])=={x['name'] for x in rows}
 # Every root-import object is selected and hash-checked by the normal runner;
 # the agg16 shim replaces that table, so the full copied-artifact check is also required.
 if label=='Headline':assert closure<=set(receipt['deps_fingerprint']['selected_objects'])
 summaries[label]={**result,'attempt':attempt,'exit_status':receipt['exit_status'],'wall_seconds':receipt['wall_seconds'],'peak_rss_kib':receipt['peak_rss_kib'],'cgroup_memory_peak_bytes':receipt['cgroup_memory_peak_bytes'],'swaps':receipt['swaps'],'source_revision':receipt['source_revision'],'command':receipt['command'],'limits':receipt['limits'],'print_axioms':receipt['print_axioms'],'reachable_file':stem+'_REACHABLE.txt.xz','reachable_uncompressed_sha256':sha(seen_raw),'root_import_axioms':sum(x['in_root_import_closure'] for x in rows),'tool_only_axioms':sum(not x['in_root_import_closure'] for x in rows)}
 summaries[label]['FunsExternal_modules']={m:sum(x['module']==m for x in rows) for m in sorted(closure) if 'FunsExternal' in m}
 inventories[label]={x['name']:x for x in rows}
 for rel in [attempt+'/receipt.json',attempt+'/stdout.log',attempt+'/time.log',stem+'_REACHABLE.txt.xz',stem+'_REACHABLE.txt.sha256']:
  b=(E/rel).read_bytes();files[rel]={'sha256':sha(b),'bytes':len(b)}
all_names=sorted(set().union(*(set(x) for x in inventories.values())))
axioms=[];tool_only=[]
differing_shared=[]
for name in all_names:
 groups={}
 for label,inv in inventories.items():
  if name not in inv:continue
  v=inv[name];key=(v['module'],v['type_expr'],tuple(v['level_params']))
  groups.setdefault(key,[]).append(label)
 if len(groups)>1:differing_shared.append(name)
 for key,labels in groups.items():
  v=inventories[labels[0]][name]
  imported={k:k in labels and bool(inv[name]['in_root_import_closure']) for k,inv in inventories.items()}
  reachable={k:k in labels and bool(inv[name]['reachable']) for k,inv in inventories.items()}
  category='a' if name in STANDARD else 'c' if any(reachable.values()) else 'b'
  row={k:v[k] for k in ['name','module','level_params','type','type_expr']}
  row.update(classification=category,declared_in_forests=labels,imported_by=imported,reachable_from=reachable,evidence={k:{'attempt':summaries[k]['attempt'],'complete_raw_kernel_walk':True,'visited_file':summaries[k]['reachable_file'],'visited_uncompressed_sha256':summaries[k]['reachable_uncompressed_sha256'],'name_present':bool(inventories[k].get(name,{}).get('reachable')),'same_name_different_declaration':k not in labels and name in inventories[k]} for k in summaries})
  (axioms if any(imported.values()) else tool_only).append(row)
for label,inv in inventories.items():
 reconstructed={x['name']:x for x in axioms if x['imported_by'][label]}
 expected={n:v for n,v in inv.items() if v['in_root_import_closure']}
 assert set(reconstructed)==set(expected)
 assert all(reconstructed[n]['type_expr']==v['type_expr'] and reconstructed[n]['module']==v['module'] for n,v in expected.items())
nonstandard_reached=[x['name'] for x in axioms if x['classification']=='c']
assert not nonstandard_reached,nonstandard_reached
seed=json.loads((E/'NDP_SEED_VERIFICATION.json').read_text())
manifest=lzma.decompress((R/'evidence/native-l188-20261028/NDJ_CACHE_PINS.json.xz').read_bytes())
assert seed['seed_manifest_sha256']==sha(manifest)
pins=json.loads(manifest)
assert seed['artifacts_verified']==sum(len(r['artifacts']) for r in pins['objects'])
counts=dict(collections.Counter(x['classification'] for x in axioms))
out={'schema':'NDP_AXIOMS/v1','finding_first':'No reachable nonstandard axiom; raw constant dependency graphs agree with both #print axioms results.','scope':'Every axiom declaration in the actual transitive import closures; audit-tool-only imports explicitly separated','classification_key':{'a':'Lean core standard: propext, Classical.choice, Quot.sound','b':'Imported declaration unreachable from both roots, established by exhaustive raw kernel graph traversal','c':'Reachable nonstandard: investigate contradiction with printed axiom results'},'roots':summaries,'closure_union_modules':len(set.union(*closures.values())),'unique_axiom_names':len({x['name'] for x in axioms}),'shared_names_with_distinct_declarations':differing_shared,'counts':counts,'axioms':axioms,'tool_only_axioms':tool_only,'seed_verification':seed,'evidence_files':files,'limitations':['Cached objects, not a fresh coherent closure rebuild','Imported objects and Lean kernel/toolchain remain trusted','Explicit theorem hypotheses and runtime/native/artifact boundaries are not discharged by an axiom audit','Separate predecessor forests; no compatible combined environment claimed']}
encoded=json.dumps(out,indent=2,ensure_ascii=False)+'\n'
if '--check' in sys.argv:assert (E/'NDP_AXIOMS.json').read_text()==encoded
else:(E/'NDP_AXIOMS.json').write_text(encoded)
print(json.dumps({'valid':True,'counts':counts,'total_axioms':len(axioms),'tool_only_axioms':len(tool_only),'roots':{k:{p:v[p] for p in ['closure_modules','reachable_constants','root_import_axioms','walked_axioms']} for k,v in summaries.items()}},indent=2))
