#!/usr/bin/env python3
"""Deterministic S10 reconciliation. --require-complete fails closed.

Ownership is a proposal derived from the frozen-order delivery table, not a
proof of cone refinement nor acceptance by another cone's owner. An emitted
Charon file with has_errors=true is never a successful extraction gate.
"""
import argparse,collections,hashlib,json,re,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory-20261021'
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(name):return json.loads((E/name).read_text())
def encoded(x):return (json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
OWNERS=['S1','S2','S3','S4','S5','S6','S7','S8','S9','S10','parser','multiproof','checkpoint ABI','Pool caller','ordered caller join']
SPECS={
 'core':'Rust core operations preserve the documented typed value, bounds/overflow checks, iterator order, reference aliasing and panic behavior; all source safety preconditions must be established. No UB or unchecked-index precondition is assumed proved.',
 'alloc':'Allocation may fail or abort exactly as the frozen runtime; successful Vec/Box operations preserve length/capacity, initialization, aliasing and drop effects. Allocation success is not assumed on all storage.',
 'std':'Native diagnostic std implementation only; NOT a deployed-SBF boundary. Runtime configuration/cfg correspondence remains open.',
 'sol_sha256':'For valid input slice descriptors, return the SHA-256 digest of concatenated slices in order; account for each invocation in the shared oracle log, including rejected executions; failure and memory effects follow the frozen runtime ABI.',
 'runtime':'The frozen Solana syscall ABI, account borrow/ownership/CPI/return-data and memory effects must match the caller model, with ordinary failure and transaction rollback; runtime carrier binding remains independent.',
 'panic':'Panic/abort never returns a successful verifier output; prove any omitted path unreachable on accepted executions, preserving prior oracle reads.'}

def proposal(name,file=''):
 # Disjoint policy branches: one proposal only. Unknown third-party code is NOT trusted.
 n=name.replace('$LT$','<').replace('$GT$','>').replace('$u20$',' ').replace('..','::')
 if n.startswith(('core::','alloc::','std::')):
  k=n.split('::')[0];return [],dict(kind=k,spec=SPECS[k],status='proposed trust specification; not discharged')
 if n in ('abort','custom_panic','rust_begin_unwind','__rust_start_panic'):
  return [],dict(kind='panic',spec=SPECS['panic'],status='residual')
 if n.startswith('sol_'):
  k='sol_sha256' if n=='sol_sha256' else 'runtime';return [],dict(kind=k,spec=SPECS[k],status='residual')
 if n=='entrypoint' or n.startswith(('__rust','__rg_','rust_eh_')):
  return [],dict(kind='runtime',spec=SPECS['runtime'],status='residual')
 if 'aspis_pool' in n or 'programs/aspis-pool/' in file:return ['Pool caller'],None
 if 'aspis_r1_cost_probe_program' in n or 'programs/r1-cost-probe/' in file:
  return ['S6' if 'first_decoded' in n or re.search(r'::first(?:$|::)',n) else 'S2'],None
 if n.startswith(('solana_','spl_')) or n.startswith('<solana_') or 'solana_' in n:
  return ['Pool caller'],None
 if 'aspis_r1_cost_probe' in n or 'crates/aspis-r1-cost-probe/' in file:
  if '/weights.rs' in file or '::weights::' in n:
   return ['S9' if 'libra' in n.lower() else 'S3'],None
  if '/fast_dots.rs' in file or '::fast_dots::' in n:return ['S4'],None
  if '/fast_pairing.rs' in file or '::fast_pairing::' in n:return ['S8' if any(x in n for x in ['EbyKDot','finish','value','push']) else 'S5'],None
  if '/fast_domain.rs' in file or '::fast_domain::' in n:return ['S7'],None
  if '/multiproof.rs' in file or '::multiproof::' in n or any(x in n for x in ['::batch_tree','::batch_merkle']):return ['multiproof'],None
  if '/compact.rs' in file or '::compact::' in n:return ['S8' if 'check_values' in n else 'parser'],None
  if any(x in n for x in ['::parse_shape','::wide_view','::opening','::slot::','::slot$']):return ['parser'],None
  if any(x in n for x in ['QueryGeometry','::accumulate','::query_values','::circle_fold','::line_fold']):return ['S7'],None
  if 'BatchedWeights' in n:return ['S8'],None
  if any(x in n for x in ['Reader','::resume','checkpoint','::save']):return ['checkpoint ABI'],None
  if any(x in n for x in ['::prepare','::powers','::claim','::r1_semantic::','::sampler::','Transcript','::r1_wire::begin']):return ['S1'],None
  if '::r1_wire::' in n or '/r1_wire.rs' in file:return ['parser'],None
  if any(x in n for x in ['::polynomial','::finish_relation']):return ['S5'],None
  if '/candidate.rs' in file or '::candidate::' in n or '::verifier::' in n:return ['ordered caller join'],None
  if '/trace.rs' in file or '::trace::' in n:return ['S7'],None
 if 'aspis_core' in n or 'crates/aspis-core/' in file:
  if '/field' in file or '::field::' in n:return ['S5'],None
  if any(x in n for x in ['merkle','Digest','digest']):return ['multiproof'],None
  if any(x in n for x in ['circle','domain']):return ['S7'],None
  return ['ordered caller join'],None
 if 'aspis_statement' in n or 'crates/aspis-statement/' in file:return ['Pool caller'],None
 return [],None

def build():
 elf=load('elf-graphs.json')['artifacts'];stage=load('stage2-llbc.json');sources=load('source-hashes.json');rows=[];gaps=[]
 for mode,g in elf.items():
  ids={s['address'] for s in g['symbols']};seen=set(g['roots']);todo=list(seen);adj=collections.defaultdict(list)
  for c in g['calls']:
   assert c['caller'] in ids
   if c['kind']=='direct':assert c['resolved'] and c['target'] in ids;adj[c['caller']].append(c['target'])
  while todo:
   for target in adj[todo.pop()]:
    if target not in seen:seen.add(target);todo.append(target)
  assert sorted(seen)==g['direct_reachable']
  assert g['text_equal']
  for s in g['symbols']:
   owners,boundary=proposal(s['name'])
   rows.append(dict(id=f'elf:{mode}:{s["address"]:x}:{sha(s["name"].encode())[:16]}',name=s['name'],artifact=mode,address=s['address'],size=s['size'],evidence='linked symbol',reachability='direct entrypoint lower bound' if s['address'] in seen else 'linked candidate; indirect reachability unresolved',owners=owners,trusted_boundary=boundary,source_instance_resolution='unresolved: LLVM inline/instance source map absent'))
  syscalls=sorted({c['target'] for c in g['calls'] if c['kind']=='syscall'})
  for name in syscalls:
   owners,boundary=proposal(name);assert boundary
   rows.append(dict(id=f'syscall:{mode}:{name}',name=name,artifact=mode,evidence='SBF dynamic call relocation',reachability='referenced in linked text',owners=owners,trusted_boundary=boundary))
  gaps.append(dict(kind='indirect_targets',artifact=mode,count=g['indirect_calls'],call_sites=[c['address'] for c in g['calls'] if c['kind']=='indirect']))
 for graph in ['stage2-llbc.json']+[p.name for p in sorted(E.glob('*-v[23].json')) if p.name not in ['inventory.json']]:
  x=load(graph)
  if 'declarations' not in x:continue
  if x.get('has_errors',x.get('input',{}).get('has_errors',False)):
   gaps.append(dict(kind='charon_has_errors',graph=graph))
  byid={f['id']:f for f in x['declarations']}
  for f in x['declarations']:
   file=f.get('source_pin',{});file=file.get('path','') if file else f.get('file',{}).get('Local','')
   owners,boundary=proposal(f['name'],file)
   for c in f['calls']:
    if c['target'] is not None:assert c['target'] in byid,(graph,c['target'])
   rows.append(dict(id=f'llbc:{graph}:{f["id"]}',name=f['name'],source_path=file,source_text_sha256=f['source_text_sha256'],source_pin=f.get('source_pin'),body_kind=f['body_kind'],evidence=graph,reachability='emitted declaration; calls may include unwind/code pointers',owners=owners,trusted_boundary=boundary,source_instance_resolution='compiler instance within this extraction only; SBF matching unproved'))
   if f['body_kind']!='Structured':gaps.append(dict(kind='missing_or_opaque_body',id=rows[-1]['id'],body_kind=f['body_kind']))
  unknown=[dict(caller=f['id'],call_index=i) for f in byid.values() for i,c in enumerate(f['calls']) if c['kind']=='indirect_or_trait']
  if unknown:gaps.append(dict(kind='indirect_or_trait_LLBC',graph=graph,count=len(unknown),sites=unknown))
 gaps += [dict(kind='source_cfg_and_toolchain',detail='Native/forced-cfg Charon runs use nightly rustc, not the frozen SBF Rust/LLVM target. Full inline/monomorphized source-to-SBF correspondence remains open.'),dict(kind='owner_acceptance',detail='Ownership proposals derived from delivery table; owner acceptance of each compiler instance remains open.'),dict(kind='source_driver_tree',detail='No complete frozen Rust Calls tree or source_order/model_order identities supplied. The checked model stage tree is distinct.'),dict(kind='import_collision_adoption',detail='IMPORT-UNION-20261021.md copied-world fix is proposed, not adopted into canonical generated modules.'),dict(kind='pool_and_devnet',detail='No clean full deployed-target entrypoint LLBC for all three modes. Shared .text establishes verifier executable equality only, not declaration completeness.')]
 unassigned=[r['id'] for r in rows if len(r['owners'])==0 and r['trusted_boundary'] is None]
 duplicate=[r['id'] for r in rows if len(r['owners'])+int(r['trusted_boundary'] is not None)>1]
 assert len({r['id'] for r in rows})==len(rows)
 counts=dict(records=len(rows),owners=dict(collections.Counter(o for r in rows for o in r['owners'])),trusted_boundary_records=sum(r['trusted_boundary'] is not None for r in rows),unassigned=len(unassigned),assigned_twice=len(duplicate),gaps=len(gaps))
 files=['elf-graphs.json','stage2-llbc.json','source-hashes.json']+[p.name for p in sorted(E.glob('*-v[23].json'))]
 inputs={name:sha((E/name).read_bytes()) for name in files}
 inputs['design/CONE-AUDIT-20261021.md']=sha((B/'design/CONE-AUDIT-20261021.md').read_bytes())
 result=dict(schema='s10-frozen-declaration-reconciliation-v1',source_revision=sources['source_revision'],status='INCOMPLETE',claim='Machine-checked reconciliation of recorded compiler/ELF evidence; not a complete frozen reachable-declaration set',owner_policy_status='PROPOSED; needs cone-owner reconciliation',owners=OWNERS,input_hashes=inputs,counts=counts,declarations=rows,unassigned=unassigned,assigned_twice=duplicate,gaps=gaps)
 residual=dict(schema='s10-explicit-trusted-boundary-residuals-v1',items=[dict(id=r['id'],name=r['name'],**r['trusted_boundary']) for r in rows if r['trusted_boundary']],status='Explicit proposed trust specifications; no new Lean axioms and no proof of backend/caller safety')
 return {'inventory.json':result,'trusted-boundary.json':residual}
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');p.add_argument('--require-complete',action='store_true');a=p.parse_args();outputs=build()
 for name,x in outputs.items():
  b=encoded(x)
  if a.check:assert (E/name).read_bytes()==b,'stale '+name
  else:(E/name).write_bytes(b)
 x=outputs['inventory.json'];print(json.dumps(dict(status=x['status'],counts=x['counts'],check=a.check,source_revision=x['source_revision']),sort_keys=True))
 if a.require_complete and (x['status']!='COMPLETE' or x['unassigned'] or x['assigned_twice'] or x['gaps']):raise SystemExit(2)
if __name__=='__main__':main()
