#!/usr/bin/env python3
"""Noncompiler preparation for exactly355. No import of compiler launch code."""
import json,pathlib,subprocess,time,resource,hashlib
from Port31DATA_run import T,E,SYS,pin,safe,state
start=time.monotonic();old=json.loads((E/'Port31DATA_preflight-354.json').read_text());plan=json.loads((E/'Port31DATA_next-inputs.json').read_text())
out=pathlib.Path('/private/tmp/Port31DATA-355-20261025');out.mkdir(mode=0o700,exist_ok=True)
assert not (E/'Port31DATA_attempt-355.json').exists()
# Historical safe/stat continuity is checked for the exact1815 admitted containers.
prior=next(r for r in old['fresh_pins'] if r['path'].endswith('/Port31DATA_inputs.tsv'))
assert pin(safe(prior['path']))==prior
rows=[l.split('\t') for l in pathlib.Path(prior['path']).read_text().splitlines()];assert len(rows)==1815
states={r['path']:r for r in old['states']}
for _,p in rows:assert state(safe(p))==states[p]['stat'],p
fresh={r['path']:r for r in old['fresh_pins']}
for r in fresh.values():assert pin(safe(r['path']))==r,r['path']
groups=[dict(label=l,kind='OWN' if l.startswith(('S8:','BOOL:')) else 'RAW',paths=[p]) for l,p in rows]
admitted={p for _,p in rows}
def reuse(r):
 p=str(safe(r['path']));assert state(p)==r['stat'] and state(p)[2]==r['bytes'],p
 assert p not in admitted;pstate=dict(path=p,stat=r['stat'],byte_pin=r['sha256'],assessment='REUSED historical SHA; safe/stat continuity, not a new identity gate')
 states[p]=pstate;admitted.add(p);return p
for i,r in enumerate(plan['original_packet']['fragments_data']):
 assert not r['already_admitted'];p=reuse(r);groups.append(dict(label=f"ROOT87:{i}:{r['module']}",kind='RAW',paths=[p]))
assert len(plan['original_packet']['fragments_data'])==87 and plan['original_packet']['bytes']==22668248
bases={'s126-sdk-current-9acc-proof-refresh-20261024-v1':'BASE','s126-sdk-current-incremental-release-20261024-v1':'INCREMENTAL','s126-sdk-selected-cut-release-20261025-v1':'SELECTED'}
for r in plan['additional_current_duplicate_containers']:
 p=reuse(r);pp=pathlib.Path(p);root=next(a for a in pp.parents if a.name in bases);mod=pp.relative_to(root/'transport').as_posix()[:-6].replace('/','.')
 groups.append(dict(label='CURRENT:'+bases[root.name]+':'+mod,kind='RAW',paths=[p]))
core=[reuse(r) for r in plan['core_supplement']['parts']];assert len(core)==3
assert core==[str(SYS/'lib/lean'/('Init/Core.olean'+s)) for s in ['', '.server','.private']]
groups.append(dict(label='CORE:Init.Core',kind='CORE',paths=core))
paths=[p for g in groups for p in g['paths']];assert len(paths)==len(set(paths))
size=sum(state(p)[2] for p in paths);assert size==283468040 and size<512*1024**2
wl=out/'Port31DATA_inputs355.tsv';wl.write_text(''.join('\t'.join([g['label'],g['kind'],*g['paths']])+'\n' for g in groups))
wp=out/'Port31DATA_duplicates355.tsv';wp.write_text(''.join('\t'.join(str(i) if k=='id' else r['presentation_row'][k] for k in ['id','name','first','second'])+'\n' for i,r in enumerate(plan['owner43']['data'])))
assert len(wp.read_text().splitlines())==43
roots=json.loads(subprocess.check_output(['git','show','3bc1639:evidence/port30join-20261025/focused-graph.json']))['roots']
assert roots==['AspisR1.S2W_D189Consolidation.accepted_run','AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace','AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts']
for p in [wl,wp,T/'Port31DATA_Raw355.lean',T/'Port31DATA_run355.py',T/'Port31DATA_prepare355.py',T/'Port31DATA_bound355.py',T/'Port31DATA_audit355.py',SYS/'src/lean/Init/Core.lean',SYS/'src/lean/Lean/Environment.lean',E/'Port31DATA_criteria355.md',E/'Port31DATA_next-inputs.json',E/'Port31DATA_reused-variant-obligations.json',pathlib.Path('/private/tmp/lead-port31-review-20261025-v1/receipt.json')]:
 q=pin(safe(p));fresh[str(p)]=q;states[str(p)]=dict(path=str(p),stat=state(p),byte_pin=q['sha256'],assessment='fresh hash')
nextplan=dict(status='AUTHORIZED355 INPUT PLAN; original next-inputs.json retained unchanged',original_plan=pin(E/'Port31DATA_next-inputs.json'),old_inputs_retained=1815,original_root_transports=87,original_root_bytes=22668248,additional_current_endpoints=len(plan['additional_current_duplicate_containers']),grouped_core_parts=3,group_count=len(groups),part_count=len(paths),bytes=size,groups=groups,roots=dict(source_revision='3bc1639',path='evidence/port30join-20261025/focused-graph.json',presentation_labels=roots,reader='explicit Lean Name quotation; never printed-label reconstruction'),reuse='Historical hashes plus safe/stat continuity, not8917 scan or2.8GB rehash',strict_readback_required=True)
(E/'Port31DATA_next-inputs355.json').write_text(json.dumps(nextplan,indent=2)+'\n')
r=dict(old,directory=str(out),fresh_pins=list(fresh.values()),states=list(states.values()),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),raw_inputs=len(paths),raw_groups=len(groups),raw_bytes=size,original_core_fragments=old['original_core_fragments'],roots=nextplan['roots'],authority='EXACTLY ONE raw data CLI355; no theorem/compiler probes',axioms='N/A: raw IO; Bool353 original audit REUSED',budget_before=dict(actual=354,unassigned=1,pending355=1,reserved_kernel_consumers=5,carry=7),budget_after=dict(actual=355,remaining=13,unassigned=1,reserved_kernel_consumers=5,carry=7),source_api='Environment.lean109-130,1740-1770; Core.lean1220/1226; immutable Port29 multiline update layout inspected',command=['python3','-B',str(pathlib.Path(__file__))],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap)
# Pin complete new plan after writing it; no self-referential hash.
p=E/'Port31DATA_next-inputs355.json';r['fresh_pins'].append(pin(p));r['states'].append(dict(path=str(p.resolve()),stat=state(p)))
(E/'Port31DATA_preflight-355.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(dict(groups=len(groups),parts=len(paths),bytes=size,original_roots=87,owner_pairs=43,wall_seconds=r['wall_seconds'],exit=0,lean_calls=0)))
