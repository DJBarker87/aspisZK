"""Archive the one retained strict walk. Does not invoke Lean or alter results."""
from pathlib import Path
import hashlib,json,lzma
P=Path('/home/dombarker/project-offloads/codex-pv-lib-spec-20261107/evidence')
rec=json.loads((P/'receipt-55190.json').read_text())
results=[]
for c in ['w3']:
 for line in (P/f'out-55190-{c}.log').read_text().splitlines():
  if line.startswith('NEP62_RESULT '):
   v=json.loads(line.split('NEP62_RESULT ',1)[1]);v['cohort']=c;results.append(v)
files=[P/'raw-audit'/('NEP_pv-thread_'+v['root']+'_REACHABLE.txt') for v in results]
assert all(f.exists() for f in files)
data=json.dumps({f.name:f.read_text() for f in files},sort_keys=True).encode()
(P/'SESSION12_RAW_GRAPH_ARCHIVE.json.xz').write_bytes(lzma.compress(data))
(P/'SESSION12_RAW_GRAPH_ARCHIVE.json.sha256').write_text(hashlib.sha256(data).hexdigest()+'\n')
manifest={'roots':results,'files':[{'name':f.name,'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size} for f in files]}
(P/'SESSION12_RAW_GRAPH_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
standard={'propext','Classical.choice','Quot.sound'}
logs='\n'.join((P/f'out-55190-{c}.log').read_text() for c in ['w3'])
summary={k:rec[k] for k in ['attempt','exit','source_revision','wall','peak_rss_kbytes','swaps']}
summary.update(roots=len(results),partitions={c:sum(v['cohort']==c for v in results) for c in ['w3']},
 all_equal=all(v['equal'] for v in results),unresolved=logs.count('unresolved or ambiguous retained constant')+logs.count('unresolved retained constant'),
 standard_axioms_only=all(set(v['walked_axioms'])<=standard for v in results),
 new_roots_only=True,rerun=False,walker_changes=False,collector_changes=False,
 constructor_summary_union='every reached kernel ctorInfo; walker and collectAxioms unchanged',
 full_source_joint_witness_inhabited=False,successful_original_history=False,callback_byte_suffix_installed=True,canonical_thread_word_repaired=True,scope_u8_repaired=True,physical_stack_pairing_proved=False,full_joint_contradiction_proved=False)
(P/'SESSION12_RAW_AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
