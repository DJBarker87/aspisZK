#!/usr/bin/env python3
"""Exact source chain ledger; no semantic equivalence claim is inferred from Git."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];ev=area/'evidence/cu-equivalence-20261019'
def git(*args):return subprocess.check_output(['git',*args])
def full(rev):return git('rev-parse',rev).decode().strip()
sha=lambda b:hashlib.sha256(b).hexdigest()
reference=full('f458169f7');production=full('39c2971dd');roots=['crates/aspis-r1-cost-probe','programs/r1-cost-probe']
keep={full(rev):i for i,rev in [(1,'3ab4faf7f'),(2,'190e1779c'),(3,'d631a90ec'),(4,'d11f9b2fc'),(5,'e58b87665'),(6,'e5a93db5c'),(7,'2aa1b879c'),(10,'225a3736d'),(12,'16a39d2a8'),(14,'39c2971dd')]}
drops={full(rev):full(revert) for rev,revert in [('f40c80702','ad8c22750'),('481df1dec','8cdeaf716'),('b0005af33','a29133e25'),('029206324','16724ebd0')]};reverts={v:k for k,v in drops.items()}
def files(rev):
 out={}
 for line in git('ls-tree','-r',rev,'--',*roots).decode().splitlines():
  mode,typ,digest,path=line.split(None,3)
  if typ=='blob':out[path]={'git_blob':digest,'sha256':sha(git('cat-file','blob',digest))}
 return out
def state(rev):return sha(json.dumps(files(rev),sort_keys=True,separators=(',',':')).encode())
history=git('rev-list','--reverse',reference+'..'+production).decode().splitlines();rows=[];prev_keep=reference;source_neutral=[]
for rev in history:
 parent=full(rev+'^');changed=git('diff','--name-only',parent,rev,'--',*roots).decode().splitlines();entry=dict(revision=rev,parent=parent,subject=git('show','-s','--format=%s',rev).decode().strip(),runtime_paths_changed=changed)
 if rev in keep:
  assert state(parent)==state(prev_keep),(keep[rev],'retained_predecessor_source_gap')
  before,after=files(parent),files(rev)
  entry.update(kind='KEEP',candidate=keep[rev],source_predecessor=prev_keep,parent_source_map_sha256=state(parent),source_predecessor_map_sha256=state(prev_keep),candidate_source_map_sha256=state(rev),files={p:dict(before=before.get(p),after=after.get(p)) for p in changed})
  prev_keep=rev
 elif rev in drops:
  assert state(full(rev+'^'))==state(drops[rev]),('revert_not_exact',rev)
  entry.update(kind='DROP',revert=drops[rev],restored_parent_source_map_sha256=state(parent))
 elif rev in reverts:
  entry.update(kind='REVERT',dropped_candidate=reverts[rev],restores_source_revision=full(reverts[rev]+'^'),restored_source_map_sha256=state(rev))
 else:
  assert not changed,('unclassified_runtime_delta',entry)
  entry['kind']='RUNTIME_SOURCE_NEUTRAL';source_neutral.append(rev)
 rows.append(entry)
assert prev_keep==production
before,after=files(reference),files(production);changed={p:dict(reference=before.get(p),production=after.get(p)) for p in sorted(set(before)|set(after)) if before.get(p)!=after.get(p)}
result=dict(reference=reference,production=production,source_roots=roots,selected_features=['pool-adapter','private-leaf-salts'],excluded_feature='cu-profiling',source_chain_complete=True,retained_candidates=[keep[r['revision']] for r in rows if r['kind']=='KEEP'],source_neutral_revisions=source_neutral,dropped_pairs_fully_restored=True,reference_source_map_sha256=state(reference),production_source_map_sha256=state(production),net_changed_files=changed,history=rows,semantic_scope='This audit establishes exact source-delta coverage and source snapshot adjacency, not whole-verifier equivalence. Semantic/source-bound context equations and invariants must separately instantiate each KEEP edge under one compatible observation/runtime interpretation. Reverted candidates need no equivalence theorem because complete runtime source maps are restored.')
p=ev/'RETAINED-COMPOSITION-SOURCE-LEDGER.json';data=(json.dumps(result,indent=2)+'\n').encode()
if args.check:assert p.read_bytes()==data
else:p.write_bytes(data)
print(json.dumps(dict(check=args.check,keep=len(keep),drop_pairs=len(drops),runtime_source_neutral=len(source_neutral),net_changed_files=list(changed),source_chain_complete=True,semantic_equivalence_asserted=False)))
