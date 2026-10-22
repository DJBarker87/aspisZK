#!/usr/bin/env python3
"""Pass-three overlay. Frozen compilation is evidence, not source refinement.
A proposed trust spec is never silently treated as a discharged source join.
"""
import argparse,collections,hashlib,json,resource,subprocess,sys,time
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory3-20261021';P=B/'evidence/s10-inventory2-20261021'
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def encoded(x):return (json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
SPECS={
'indirect_targets':('runtime/library plus owned callback residual','Core formatting/vtable callbacks preserve typed dispatch, evaluation order, successful formatting and panic/abort behavior. Pool digest callbacks hash exactly the ordered byte slices. Observer callbacks must be proved absent (None) along every admitted entry path, or their effects retained. These owned callback claims are not discharged by the core trust specification.'),
'indirect_or_trait_LLBC':('diagnostic compiler boundary','Frozen rustc resolves static traits using the actual concrete type/const/region substitutions and preserves Rust operational behavior during optimization. Runtime function pointers still require target-flow and pre/post-state proofs. Native Charon omissions are not invented edges.'),
'charon_has_errors':('historical diagnostic failure','Errorful Charon output is not a successful translation. Frozen-rustc MIR is independent evidence; a replacement translation must account for every affected declaration and cannot reuse an absent Charon body as a theorem.'),
'address_taken_functions':('compiler/runtime boundary plus target-flow residual','All address-taken functions, drops and callback/vtable targets retain their actual typed arguments, mutation, rejection and oracle effects. Merely taking an address does not establish execution; a pointer set does not identify a call target.'),
'missing_or_opaque_body':('native diagnostic initialization boundary','Native solana_sysvar lazy program-stub initialization and SHA-2 x86 CPUID storage obey their library initialization, synchronization and CPU-feature specifications. They are native diagnostics only; no such state is admitted as a deployed SBF primitive. Cfg/source exclusion still needs a witness.'),
'source_cfg_and_toolchain':('frozen compiler trust boundary','Platform-tools v1.52 Rust 1.89.0-dev / LLVM 20.1.7 implements the recorded SBF target, cfg, feature and ABI configuration and preserves defined Rust semantics through monomorphization, inlining, code generation and linking. Byte-identical diagnostic rebuilds connect compiler evidence to these pins; they do not prove Rust safety or Lean refinement.'),
'owner_acceptance':('owned integration obligation','Each cone owner accepts the exact source and concrete instances, carriers and boundary specification. S10 cannot manufacture owner acceptance; a proposed owner label is not a cone proof.'),
'source_driver_tree':('owned source refinement obligation','Construct the actual frozen Calls tree including Pool, account adapters, both transactions, checkpoints, ordinary errors, mutation and oracle reads. Prove source_order and model_order against dV_frozen (or the precisely sufficient accepted-run transport). CFG dominance is only evidence for this obligation.'),
'import_collision_adoption':('owned coherent replay obligation','Adopt collision-free generated names or compatible canonical objects and replay the final dependency closure with standard axioms. No existing module may be edited by this worker and separate compatible checks do not establish an import union.'),
'pool_and_devnet':('deployed coverage obligation','Account for every deployed entry path, inlined declaration and indirect target in Pool/default/devnet. Exact artifact reproduction proves artifact identity; it does not establish a complete typed source call tree or account/runtime carrier binding.')}
def build():
 old=load(P/'frontier-dispositions.json');orig=load(B/'evidence/s10-inventory-20261021/inventory.json');rows={r['id']:r for r in orig['declarations']}
 linked=load(E/'llvm-linked-definitions.json');matches=load(P/'elf-source-paths.json')['matched'];elf_match={r['id']:r['mir_name'] for r in matches}
 bodies=load(E/'frontiers-default.json');assert len(bodies)==40 and all(len(r['frozen_bodies'])==1 for r in bodies)
 assert [r['id'] for r in bodies]==[r['original']['id'] for r in old if r['status']=='BODY_LOCATED_INSTANCE_OPEN']
 stage2={r['id']:r for r in load(B/'evidence/s10-inventory-20261021/stage2-llbc.json')['declarations']}
 affected=[]
 for f in bodies:
  direct=[dict(mode=mode,**x) for mode,g in linked.items() for x in g['llvm_linked_definitions'] if elf_match.get(x['id'])==f['mir_name']]
  generics=stage2[int(f['id'].rsplit(':',1)[1])]['generics']
  substitutions=dict(type_parameters=[p['name'] for p in generics['types']],const_parameters=[p['name'] for p in generics['const_generics']],regions='erased; source borrow/safety obligations retained',classification='MONOMORPHIC_DECLARATION' if not generics['types'] and not generics['const_generics'] else 'GENERIC_INSTANTIATION_REVIEW')
  affected.append(dict(substitution_shape=substitutions,index=f['index'],id=f['id'],declaration=f['mir_name'],frozen_body=f['frozen_bodies'][0],linked_raw_symbol_matches=direct,
   mono_records=f['monomorphizations'],inline_and_call_observations=len(f['compiler_occurrences']),
   status='FROZEN_BODY_AND_LINKED_SYMBOL' if direct else 'FROZEN_BODY_ONLY',
   residual='Exact generic substitutions and inline provenance through the reachable caller must be established; generic body/mono collection observations do not by themselves prove source semantics or reachable-instance completeness.'))
 frontiers=[]
 for f in old:
  if f['status']!='OPEN':continue
  original=f['original'];kind=original['kind'];category,spec=SPECS[kind]
  frontiers.append(dict(index=f['index'],kind=kind,id=original.get('id'),name=f.get('name'),graph=original.get('graph'),category=category,required_specification=spec,status='SPECIFIED_NOT_DISCHARGED',
   existing_boundary_only=kind in ('indirect_targets','indirect_or_trait_LLBC','address_taken_functions','missing_or_opaque_body','source_cfg_and_toolchain'),
   notes='Trust specification records the required behavior, not a new Lean axiom, owner acceptance, source proof, or an admitted complete inventory.'))
 assert len(frontiers)==18
 order=load(E/'ordering-observations.json')
 # Validate a concrete non-textual ordering fact needed by both source stages.
 facts=[]
 for mode in ('default','devnet'):
  for method in ('tx1','tx2_common'):
   f=next(r for r in order['functions'] if r['mode']==mode and r['header'].startswith('fn '+method+'('))
   before=next(c for c in f['calls'] if '= batch_merkle::' in c['text'])
   after=next(c for c in f['calls'] if '= verifier::QueryGeometry::for_range' in c['text'])
   assert any(p['before']==before['line'] and p['after']==after['line'] for p in f['dominance'])
   facts.append(dict(mode=mode,function=method,before=before,after=after,claim='batch_merkle block dominates QueryGeometry::for_range block; textual block numbering is not used as order'))
 # Keep proof readiness separate from a successful integrity check.
 obligations=[dict(name='deployed instance/inline completeness',status='OPEN',evidence='40 frozen generic bodies; direct raw-symbol witnesses are partial, no complete reachable-inline map'),
  dict(name='runtime indirect targets and caller safety',status='OPEN',evidence='All pass-two sites retained, scoped trust specs do not discharge owned callbacks'),
  dict(name='cone-owner acceptance and coherent imports',status='OPEN',evidence='Other owners retain their modules; no acceptance manufactured'),
  dict(name='source Calls tree and ordering joins',status='OPEN',evidence='MIR CFG/dominance recorded; neither Lean caller identity constructed')]
 return {'affected-declarations.json':affected,'open-frontier-specifications.json':frontiers,'ordering-facts.json':facts,
  'reconciliation.json':dict(schema='s10-pass3-reconciliation-v1',status='COMPLETE' if all(r['status']=='CLOSED' for r in obligations) else 'INCOMPLETE',frozen_source_revision=orig['source_revision'],
  counts=dict(frozen_generic_bodies=len(bodies),monomorphic_declarations=sum(r['substitution_shape']['classification']=='MONOMORPHIC_DECLARATION' for r in affected),frontiers_with_linked_raw_symbols=sum(bool(r['linked_raw_symbol_matches']) for r in affected),frontiers_with_mono_records=sum(bool(r['mono_records']) for r in affected),open_frontiers_explicitly_specified=len(frontiers),mir_functions_with_cfg=len(order['functions']),selected_calls=sum(len(r['calls']) for r in order['functions']),dominance_facts=sum(len(r['dominance']) for r in order['functions'])),
  obligations=obligations,source_stage_order='TX1 shape/canonical scan, prepare, Merkle A, geometry/query loop, weights finish, checkpoint; TX2 resume, Merkle B, geometry/query loop, weights finish, relation. Source/prover/checkpoint reads must be joined to the frozen model prefix, not erased or reordered by this inventory.',
  input_hashes={str(p.relative_to(R)):sha(p.read_bytes()) for p in [P/'frontier-dispositions.json',P/'elf-source-paths.json',E/'build-manifest.json',E/'frontiers-default.json',E/'frontiers-devnet.json',E/'frontiers-pool.json',E/'llvm-linked-definitions.json',E/'ordering-observations.json']})}
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');p.add_argument('--require-complete',action='store_true');args=p.parse_args();start=time.monotonic();out=build()
 for name,x in out.items():
  raw=encoded(x);assert len(raw)<=5_000_000
  if args.check:assert (E/name).read_bytes()==raw,'stale '+name
  else:(E/name).write_bytes(raw)
 status=2 if args.require_complete and out['reconciliation.json']['status']!='COMPLETE' else 0
 if not args.check:
  use=resource.getrusage(resource.RUSAGE_SELF)
  (E/'reconcile-receipt.json').write_bytes(encoded(dict(target=str(Path(__file__).relative_to(R)),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=sha(Path(__file__).read_bytes()),exit_status=status,wall_seconds=time.monotonic()-start,peak_rss_bytes=use.ru_maxrss if sys.platform=='darwin' else use.ru_maxrss*1024,swaps=use.ru_nswap,print_axioms='N/A: compiler evidence; no source Lean theorem claimed',output_hashes={k:sha(encoded(v)) for k,v in out.items()})))
 print(json.dumps(dict(status=out['reconciliation.json']['status'],exit_status=status,counts=out['reconciliation.json']['counts'])));raise SystemExit(status)
if __name__=='__main__':main()
