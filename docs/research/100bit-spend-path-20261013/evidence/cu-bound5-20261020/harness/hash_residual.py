"""New-format SHA syscall residual, separately from SBF instruction residual.
Usage: hash_residual.py host-root analysis-dir out.json
"""
import json,sys,collections
from pathlib import Path
H,A,OUT=map(Path,sys.argv[1:]);res=json.loads((A/'residuals.json').read_text());rows=[];baselines=collections.defaultdict(set)
for role in ['stage1','stage2']:
 d=json.loads((A/f'{role}.json').read_text());meta=json.loads((A/'runs.json').read_text());per=[]
 for t in d['traces']:
  label=t['label'];paths=list((H/'sweep').glob(f'*/runs/{label}/stderr.log'));assert len(paths)==1,paths
  logs=paths[0].read_text().splitlines();native=json.loads(next(l.split('=',1)[1] for l in logs if l.startswith('FORMAT_ADOPT_NATIVE=')))
  lo,hi=(0,10) if role=='stage1' else (10,22);q=native['queries'][lo:hi];D=2*len(q)+len(set(u//4 for u in q));offset=0 if role=='stage1' else 3
  S=sum(native['slot_nodes'][offset:offset+3]);P=S+D-3;Pmax=447 if role=='stage1' else 527
  assert P<=Pmax
  sha=sum(n for _,n in t['syscalls']['sol_sha256']);baseline=sha-P;baselines[(role,meta[label]['kind'])].add(baseline)
  per.append(dict(label=label,parent_hashes=P,max_parent_hashes=Pmax,extra_parent_hashes=Pmax-P,sha_calls=sha,fixed_nonparent_sha_calls=baseline))
 for V,r in res['result'][role].items():
  w=next(t for t in per if t['label']==r['worst']);rows.append(dict(role=role,variant=json.loads(V),worst=r['worst'],**{k:v for k,v in w.items() if k!='label'},parent_syscall_cu=127,cost_in_worst_input=127*w['parent_hashes'],max_cost=127*w['max_parent_hashes'],residual=127*w['extra_parent_hashes']))
 (A/f'hash-counts-{role}.json').write_text(json.dumps(per,indent=1))
assert all(len(v)==1 for v in baselines.values()),baselines
out=dict(id='S-BINARY-PARENT-SHA',citation='multiproof.rs:149-186: one digest per distinct parent; candidate.rs:135-141 checks exact node consumption. Per tree parents = supplied nodes + distinct leaves - 1. evidence/proof-size-20261019/REPORT.md section 1 bounds six slots at 914 nodes, A=420/B=494. Thus parent maxima=420+30-3=447 /494+36-3=527. Agave 4.2.1 solana-syscalls/src/lib.rs:2545-2605 charges base85 plus max(10,len/2) for each of [1,32,32] bytes; execution_budget.rs:205-206,225 =>127 CU.',rows=rows,nonparent_sha_calls={f'{r}/{k}':list(v)[0] for (r,k),v in baselines.items()},unexplained_hash_count_variations=0)
OUT.write_text(json.dumps(out,indent=1));print(out['nonparent_sha_calls'])
