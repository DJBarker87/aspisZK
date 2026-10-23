#!/usr/bin/env python3
"""Deterministic S10 reconciliation. --require-complete fails closed.

Ownership is a proposal derived from the frozen-order delivery table, not a
proof of cone refinement nor acceptance by another cone's owner. An emitted
Charon file with has_errors=true is never a successful extraction gate.
"""
import argparse,collections,hashlib,io,json,posixpath,re,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory-20261021'
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(name):return json.loads((E/name).read_text())
def encoded(x):return (json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
OWNERS=['S1','S2','S3','S4','S5','S6','S7','S8','S9','S10','parser','multiproof','checkpoint ABI','Pool caller','ordered caller join']
SPECS={
 'core':'Rust core operations preserve the documented typed value, bounds/overflow checks, iterator order, reference aliasing, callback/trait-call order and panic behavior; all source safety preconditions must be established. No UB or unchecked-index precondition is assumed proved.',
 'alloc':'Allocation may fail or abort exactly as the frozen runtime; successful Vec/Box operations preserve length/capacity, initialization, aliasing and drop effects. Allocation success is not assumed on all storage.',
 'std':'Native diagnostic std implementation only; NOT a deployed-SBF boundary. Runtime configuration/cfg correspondence remains open.',
 'sol_sha256':'For valid input slice descriptors, return the SHA-256 digest of concatenated slices in order; account for each invocation in the shared oracle log, including rejected executions; failure and memory effects follow the frozen runtime ABI.',
 'runtime':'The frozen Solana syscall ABI, account borrow/ownership/CPI/return-data and memory effects must match the caller model, with ordinary failure and transaction rollback; runtime carrier binding remains independent.',
 'compiler_builtins':'memcpy/memmove/memset/memcmp implement the frozen byte ranges and overlap rules; __multi3 implements the low 128 bits of integer multiplication. The named soft-float helpers implement binary64 multiplication, integer conversions and comparisons with exact IEEE-754 rounding and ABI return conventions, including exceptional values; no unrestricted floating-point algebra law is assumed. Source pointer validity, non-overlap where required, and failure behavior remain obligations.',
 'panic':'Panic/abort never returns a successful verifier output; prove any omitted path unreachable on accepted executions, preserving prior oracle reads.'}

def proposal(name,file=''):
 # Disjoint policy branches: one proposal only. Unknown third-party code is NOT trusted.
 n=name.replace('$LT$','<').replace('$GT$','>').replace('$u20$',' ').replace('..','::')
 for a,b in [('$RF$','&'),('$u5b$','['),('$u5d$',']'),('$LP$','('),('$RP$',')')]:n=n.replace(a,b)
 if n.startswith('_<'):n=n[1:]
 if n.startswith(('<core::','<alloc::','<std::')) or re.match(r'^<(?:&?T|u(?:8|16|32|64|128)|str|char|usize|isize|i(?:8|16|32|64|128)|\[A\]|\(\)) as core::',n):
  k='alloc' if n.startswith('<alloc::') else 'std' if n.startswith('<std::') else 'core'
  return [],dict(kind=k,spec=SPECS[k],status='proposed trust specification; callbacks/trait calls remain independently inventoried')
 if n.startswith('compiler_builtins::') or n in ('memcpy','memmove','memset','memcmp','__multi3','__floatundidf','__gedf2','__muldf3','__fixunsdfdi','__gtdf2'):
  return [],dict(kind='compiler_builtins',spec=SPECS['compiler_builtins'],status='residual')
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
 if n.startswith(('five8_const::','five8_core::')):return ['Pool caller'],None
 if 'aspis_r1_cost_probe' in n or 'crates/aspis-r1-cost-probe/' in file:
  if '::transcript::' in n or '/transcript.rs' in file:return ['S1'],None
  if '::transport::' in n or '/transport.rs' in file:return ['S2'],None
  if '/weights.rs' in file or '::weights::' in n:
   return ['S9' if 'libra' in n.lower() else 'S3'],None
  if '/fast_dots.rs' in file or '::fast_dots::' in n:return ['S4'],None
  if '/fast_pairing.rs' in file or '::fast_pairing::' in n:return ['S8' if any(x in n for x in ['EbyKDot','finish','value','push']) else 'S5'],None
  if '/fast_domain.rs' in file or '::fast_domain::' in n:return ['S7'],None
  if '/multiproof.rs' in file or '::multiproof::' in n or any(x in n for x in ['::batch_tree','::batch_merkle']):return ['multiproof'],None
  if '/compact.rs' in file or '::compact::' in n:return ['S8' if 'check_values' in n else 'parser'],None
  if any(x in n for x in ['::parse_shape','::wide_view','::opening','::slot::','::slot$']):return ['parser'],None
  if any(x in n for x in ['QueryGeometry','::for_range','::accumulate','::query_values','::circle_fold','::line_fold']):return ['S7'],None
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

def verify_frozen_sources(sources):
 assert sources['source_revision']=='b2727acd3abf79315d18b754a260f58f4b1c6326'
 request=''.join(sources['source_revision']+':'+f['path']+'\n' for f in sources['files'])
 output=subprocess.check_output(['git','cat-file','--batch'],input=request.encode(),cwd=R)
 stream=io.BytesIO(output)
 for f in sources['files']:
  header=stream.readline().decode().split();assert len(header)==3 and header[1]=='blob'
  raw=stream.read(int(header[2]));assert stream.read(1)==b'\n'
  assert len(raw)==f['bytes'] and sha(raw)==f['sha256'],f['path']
 assert stream.read()==b''

def build():
 elf=load('elf-graphs.json')['artifacts'];sources=load('source-hashes.json');rows=[];gaps=[];closures={};nondeclarations=[]
 verify_frozen_sources(sources)
 provenance=load('source-provenance.json')
 source_by_path={s['path']:s for s in provenance['host_source_comparison']}
 external_by_path={s['reported_path']:s for s in provenance['external_sources']}
 symbol_kinds=load('elf-symbol-kinds.json')['artifacts']
 extraction=load('extraction-summary.json')
 assert extraction['source_manifest_sha256']==sha((E/'source-hashes.json').read_bytes())
 assert extraction['source_provenance_sha256']==sha((E/'source-provenance.json').read_bytes())
 for attempt in extraction['attempts']:
  for name,digest in attempt['retained_file_hashes'].items():
   assert sha((E/'extraction-attempts'/attempt['attempt']/name).read_bytes())==digest
 for name,digest in extraction['launcher_sources_sha256'].items():
  assert sha((Path(__file__).parent/name).read_bytes())==digest
 assert provenance['frozen_source_revision']==sources['source_revision']
 for attempt in extraction['attempts']:
  if attempt['exit_status']!=0:
   gaps.append(dict(kind='extraction_failed_or_stopped',attempt=attempt['attempt'],exit_status=attempt['exit_status'],review_stop=attempt['review_stop'],receipt_sha256=attempt['receipt_sha256']))
 for mode,g in elf.items():
  raw_symbols=symbol_kinds[mode]
  assert raw_symbols['linked_sha256']==g['linked']['sha256']
  raw_byaddr=collections.defaultdict(list)
  for symbol in raw_symbols['symbols']:raw_byaddr[symbol['address']].append(symbol)
  assert {s['address'] for s in g['symbols']}==set(raw_byaddr)
  ids={s['address'] for s in g['symbols']};seen=set(g['roots']);todo=list(seen);adj=collections.defaultdict(list)
  for c in g['calls']:
   assert c['caller'] in ids
   if c['kind']=='direct':assert c['resolved'] and c['target'] in ids;adj[c['caller']].append(c['target'])
  while todo:
   for target in adj[todo.pop()]:
    if target not in seen:seen.add(target);todo.append(target)
  assert sorted(seen)==g['direct_reachable']
  closures[mode]=dict(roots=g['roots'],direct_reachable=sorted(seen),linked_functions=sum(s['kind']==2 for s in raw_symbols['symbols']),instruction_bodies=len(raw_byaddr),indirect_sites=len({c['address'] for c in g['calls'] if c['kind']=='indirect'}),indirect_symbol_records=g['indirect_calls'],scope='direct-call lower bound; callx targets and inline declarations unresolved')
  assert g['text_equal']
  for s in g['symbols']:
   candidates=[r for r in raw_byaddr[s['address']] if r['size']==s['size']]
   assert candidates
   raw=candidates[0];assert all(r['kind']==raw['kind'] for r in candidates)
   if raw['kind']!=2:
    assert raw['kind']==0 and raw['size']==0
    nondeclarations.append(dict(artifact=mode,**raw,reason='zero-sized STT_NOTYPE assembler label; not a function declaration'))
    continue
   owners,boundary=proposal(s['name'])
   if s['name']=='entrypoint':owners,boundary=['Pool caller' if mode=='pool' else 'S2'],None
   rows.append(dict(id=f'elf:{mode}:{s["address"]:x}:{sha(s["name"].encode())[:16]}',name=s['name'],raw_symbol_aliases=[r['raw_name'] for r in candidates],artifact=mode,address=s['address'],size=s['size'],evidence='linked symbol',reachability='direct entrypoint lower bound' if s['address'] in seen else 'linked candidate; indirect reachability unresolved',owners=owners,trusted_boundary=boundary,source_instance_resolution='unresolved: LLVM inline/instance source map absent'))
  syscalls=sorted({c['target'] for c in g['calls'] if c['kind']=='syscall'})
  for name in syscalls:
   owners,boundary=proposal(name);assert boundary
   rows.append(dict(id=f'syscall:{mode}:{name}',name=name,artifact=mode,evidence='SBF dynamic call relocation',reachability='referenced in linked text',owners=owners,trusted_boundary=boundary))
  gaps.append(dict(kind='indirect_targets',artifact=mode,count=len({c['address'] for c in g['calls'] if c['kind']=='indirect'}),call_sites=sorted({c['address'] for c in g['calls'] if c['kind']=='indirect'})))
 for graph in ['stage2-llbc.json']+[p.name for p in sorted(E.glob('*-v[234].json')) if p.name not in ['inventory.json']]:
  x=load(graph)
  if 'declarations' not in x:continue
  if x.get('has_errors',x.get('input',{}).get('has_errors',False)):
   gaps.append(dict(kind='charon_has_errors',graph=graph))
  byid={f['id']:f for f in x['declarations']}
  assert len(byid)==len(x['declarations'])
  roots=[f['id'] for f in byid.values() if f['name'].endswith('::entrypoint')]
  if graph=='stage2-llbc.json':roots=[0]
  assert roots,'missing expected entrypoint/cut root: '+graph
  seen=set(roots);todo=list(seen)
  while todo:
   for c in byid[todo.pop()]['calls']:
    target=c['target']
    if target is not None:
     assert target in byid,(graph,target)
     if target not in seen:seen.add(target);todo.append(target)
  closures[graph]=dict(roots=roots,direct_reachable=sorted(seen),emitted_declarations=len(byid),scope='LLBC direct-call lower bound within this diagnostic extraction; indirect/error bodies unresolved')
  if 'direct_reachable' in x:assert sorted(seen)==x['direct_reachable']
  for f in x['declarations']:
   file=f.get('source_pin',{});file=file.get('path','') if file else f.get('file',{}).get('Local','')
   owners,boundary=proposal(f['name'],file)
   canonical_file=posixpath.normpath(file)
   source_record=source_by_path.get(canonical_file,external_by_path.get(file))
   if source_record is None or (source_record.get('sha256') is None and not source_record.get('host_matches_frozen',False)):
    gaps.append(dict(kind='source_file_not_frozen_or_unresolved',graph=graph,id=f['id'],path=file))
   for c in f['calls']:
    if c['target'] is not None:assert c['target'] in byid,(graph,c['target'])
   rows.append(dict(id=f'llbc:{graph}:{f["id"]}',name=f['name'],source_path=canonical_file,reported_source_path=file,source_text_sha256=f['source_text_sha256'],source_pin=source_record,instance_name_sha256=f.get('name_sha256'),body_kind=f['body_kind'],evidence=graph,reachability='direct root lower bound' if f['id'] in seen else 'emitted candidate; indirect reachability unresolved',owners=owners,trusted_boundary=boundary,source_instance_resolution='compiler instance within this extraction only; SBF matching unproved'))
   if f['body_kind']!='Structured':gaps.append(dict(kind='missing_or_opaque_body',id=rows[-1]['id'],body_kind=f['body_kind']))
  unknown=[dict(caller=f['id'],call_index=i) for f in byid.values() for i,c in enumerate(f['calls']) if c['kind']=='indirect_or_trait']
  pointer_mentions=sum(len(f['function_pointer_mentions']) for f in byid.values())
  if pointer_mentions:gaps.append(dict(kind='address_taken_functions',graph=graph,count=pointer_mentions))
  if unknown:gaps.append(dict(kind='indirect_or_trait_LLBC',graph=graph,count=len(unknown),sites=unknown))
 gaps += [dict(kind='source_cfg_and_toolchain',detail='Native/forced-cfg Charon runs use nightly rustc, not the frozen SBF Rust/LLVM target. Full inline/monomorphized source-to-SBF correspondence remains open.'),dict(kind='owner_acceptance',detail='Ownership proposals derived from delivery table; owner acceptance of each compiler instance remains open.'),dict(kind='source_driver_tree',detail='No complete frozen Rust Calls tree or source_order/model_order identities supplied. The checked model stage tree is distinct.'),dict(kind='import_collision_adoption',detail='IMPORT-UNION-20261021.md copied-world fix is proposed, not adopted into canonical generated modules.'),dict(kind='pool_and_devnet',detail='No clean full deployed-target entrypoint LLBC for all three modes. Shared .text establishes verifier executable equality only, not declaration completeness.')]
 unassigned=[r['id'] for r in rows if len(r['owners'])==0 and r['trusted_boundary'] is None]
 duplicate=[r['id'] for r in rows if len(r['owners'])+int(r['trusted_boundary'] is not None)>1]
 assert len({r['id'] for r in rows})==len(rows)
 counts=dict(records=len(rows),owners=dict(collections.Counter(o for r in rows for o in r['owners'])),trusted_boundary_records=sum(r['trusted_boundary'] is not None for r in rows),unassigned=len(unassigned),assigned_twice=len(duplicate),gaps=len(gaps))
 files=['extraction-summary.json','elf-symbol-kinds.json','elf-graphs.json','stage2-llbc.json','source-hashes.json','source-provenance.json']+[p.name for p in sorted(E.glob('*-v[234].json'))]
 inputs={name:sha((E/name).read_bytes()) for name in files}
 inputs['design/JOIN-SPLIT-DRAFT-20261021.md']=sha((B/'design/JOIN-SPLIT-DRAFT-20261021.md').read_bytes())
 result=dict(schema='s10-frozen-declaration-reconciliation-v1',source_revision=sources['source_revision'],status='INCOMPLETE',claim='Machine-checked reconciliation of recorded compiler/ELF evidence; not a complete frozen reachable-declaration set',owner_policy_status='PROPOSED; needs cone-owner reconciliation',owners=OWNERS,input_hashes=inputs,counts=counts,reachability_closures=closures,nondeclaration_symbols=nondeclarations,declarations=rows,unassigned=unassigned,assigned_twice=duplicate,gaps=gaps)
 residual=dict(schema='s10-explicit-trusted-boundary-residuals-v1',items=[dict(id=r['id'],name=r['name'],**r['trusted_boundary']) for r in rows if r['trusted_boundary']],status='Explicit proposed trust specifications; no new Lean axioms and no proof of backend/caller safety')
 proof_source=B/'lean/OraclePortS10ModelInventory.lean'
 proof_text=proof_source.read_text()
 site_defs=dict((name,dict(owner=owner,declaration=declaration)) for name,owner,declaration in re.findall(r'def (\w+Site) : Site := ⟨\.(\w+), "([^"]+)"⟩',proof_text))
 ordered=re.search(r'def inventory : List Site := \[([^\]]+)\]',proof_text)
 assert ordered is not None
 site_names=[name.strip() for name in ordered[1].split(',')]
 assert len(site_names)==len(set(site_names))==len(site_defs)==5
 proof_receipt=load('OraclePortS10ModelInventory-7/receipt.json')
 assert proof_receipt['exit_status']==0 and proof_receipt['source_sha256']==sha(proof_source.read_bytes())
 assert len(proof_receipt['print_axioms'])==4
 for line in proof_receipt['print_axioms']:
  assert line.endswith('depends on axioms: [propext, Classical.choice, Quot.sound]'),line
 model_inventory=dict(schema='s10-checked-model-stage-inventory-v1',status='MODEL_ONLY_PROVED',source_module='OraclePortS10ModelInventory',source_sha256=sha(proof_source.read_bytes()),receipt='OraclePortS10ModelInventory-7/receipt.json',sites=[dict(site=name,**site_defs[name]) for name in site_names],coverage_theorem='AspisR1.OraclePortS10ModelInventory.model_S10Join',decomposition_theorem='AspisR1.OraclePortS10ModelInventory.interpret_eq_frozen',source_completeness='OPEN: these five model stages are not the frozen source declaration tree')
 return {'inventory.json':result,'trusted-boundary.json':residual,'model-stage-inventory.json':model_inventory}
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');p.add_argument('--require-complete',action='store_true');a=p.parse_args();outputs=build()
 for name,x in outputs.items():
  b=encoded(x)
  if a.check:assert (E/name).read_bytes()==b,'stale '+name
  else:(E/name).write_bytes(b)
 x=outputs['inventory.json'];print(json.dumps(dict(status=x['status'],counts=x['counts'],check=a.check,source_revision=x['source_revision']),sort_keys=True))
 if a.require_complete and (x['status']!='COMPLETE' or x['unassigned'] or x['assigned_twice'] or x['gaps']):raise SystemExit(2)
if __name__=='__main__':main()
