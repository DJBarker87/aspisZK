#!/usr/bin/env python3
"""Current emitted-body ownership census. Source candidates are not execution."""
import collections,hashlib,importlib.util,json,re
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023')
spec=importlib.util.spec_from_file_location('policy',H/'ownership-policy.py')
policy=importlib.util.module_from_spec(spec);spec.loader.exec_module(policy)
x=json.loads((H/'mir-declarations.json').read_text())
overlay=json.loads((H/'ownership.json').read_text())
index=collections.defaultdict(set)
for p in sorted((H/'src').glob('crates/*/src/**/*.rs'))+sorted((H/'src').glob('programs/*/src/**/*.rs')):
 for name in re.findall(r'\bfn\s+(\w+)',p.read_text()):index[name].add(str(p.relative_to(H/'src')))
rows=[];counts=collections.Counter();unassigned=[]
for r in x['records']:
 header=r['header'];name=header[3:].split('(',1)[0];leaf=name.rsplit('::',1)[-1]
 # Closure inherits its actual enclosing source function's ownership.
 if '{closure#' in name:leaf=name.split('::{closure#',1)[0].rsplit('::',1)[-1]
 explicit=re.search(r'<impl at ([^:]+\.rs):',header)
 candidates=sorted(index[leaf])
 crate_prefix={'aspis_core':'crates/aspis-core/','aspis_statement':'crates/aspis-statement/',
  'aspis_r1_cost_probe':'crates/aspis-r1-cost-probe/','aspis_r1_cost_probe_program':'programs/r1-cost-probe/','aspis_pool':'programs/aspis-pool/'}[r['crate']]
 candidates=[p for p in candidates if p.startswith(crate_prefix)]
 file=explicit[1] if explicit else candidates[0] if len(candidates)==1 else ''
 canonical=r['crate']+'::'+name
 owners,boundary=policy.proposal(canonical,file)
 # The lead overlay takes precedence for the changed declarations.
 basis='retained disjoint source/file ownership policy'
 if 'four_dots' in name:owners,boundary=['S4'],None;basis='lead re-pin S4 ownership overlay'
 elif ('from_limbs' in name and ('canonical' in name or file.endswith('/fast_pairing.rs'))):owners,boundary=['S5'],None;basis='lead re-pin canonical constructor ownership overlay'
 elif 'EbyKDot' in header and file.endswith('/fast_pairing.rs'):owners,boundary=['S8'],None;basis='lead re-pin EbyKDot ownership overlay'
 elif name.startswith('weights::powers'):owners,boundary=['S3'],None;basis='lead re-pin generic powers ownership overlay'
 elif explicit and file.endswith('/verifier.rs'):
  for ty,owner in [('BatchedWeights','S8'),('QueryGeometry','S7'),('Reader','checkpoint ABI')]:
   if re.search(r'\b'+ty+r'\b',header):owners,boundary=[owner],None;break
 elif explicit and 'SemanticTranscript' in header:owners,boundary=['S1'],None
 if not owners and not boundary:owners=['ordered caller join'];basis='owned compiler/source glue or unresolved source placement; caller must lower, not a trust admission'
 assert len(owners)+int(boundary is not None)==1
 owner=owners[0] if owners else None
 counts[(r['mode'],owner or 'boundary:'+boundary['kind'])]+=1
 ident='mir:'+r['mode']+':'+r['crate']+':'+str(r['line'])+':'+r['sha256'][:16]
 rows.append(dict(id=ident,mode=r['mode'],header=header,body_sha256=r['sha256'],owner=owner,
  boundary=boundary['kind'] if boundary else None,source_file=file or None,
  candidate_source_files=candidates if not file else [],ownership_basis=basis,
  compiler_output=Path(r['path']).name,line=r['line'],calls=len(r['calls']),inline_scopes=len(r['inline_scopes'])))
assert len({r['id'] for r in rows})==len(rows)
# Compact JSONL preserves every compiler occurrence without a giant inline map.
p=H/'declaration-owners.jsonl'
p.write_text(''.join(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n' for r in rows))
summary=dict(schema='s10-adopted-frozen-body-ownership-v1',records=len(rows),
 counts=[dict(mode=m,owner=o,count=n) for (m,o),n in sorted(counts.items())],
 declaration_owners=dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()),
 overlay_sha256=hashlib.sha256((H/'ownership.json').read_bytes()).hexdigest(),
 policy_sha256=hashlib.sha256((H/'ownership-policy.py').read_bytes()).hexdigest(),
 overlay_records=len(overlay['records']),unassigned=unassigned,
 limitations='One proposed owner per emitted generic body. Includes source supersets and compiler glue, not complete deployed reachability; caller-lowering placement, final inline correspondence, source semantics and owner acceptance stay open. Historical native closure/constant IDs are not reused.',complete=False)
(H/'declaration-ownership.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
print(json.dumps(summary),flush=True)
