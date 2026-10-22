#!/usr/bin/env python3
"""Scope the exact delta; never convert a source observation into completeness."""
import argparse,collections,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence';E=B/'s10-repin-20261022'
def load(p):return json.loads(p.read_text())
def enc(x):return (json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
def build():
 source=load(E/'source-inputs.json');diff=load(E/'mir-diff.json');mono=load(E/'mono-diff.json');exact=load(E/'mono-exact-diff.json');llvm=load(E/'llvm-diff.json');elf=load(E/'elf-diff.json')
 adopted=['crates/aspis-r1-cost-probe/src/'+f for f in ['fast_dots.rs','fast_pairing.rs','weights.rs']]
 changed=[r for r in source['files'] if r['changed']]
 assert len(changed)==16 and all(any(r['path']==p for r in changed) for p in adopted)
 assessed=[]
 for mode in diff['modes']:
  rows=[]
  for r in mode['changed']:
   k=r['key'];scopes=[s for b in r['old']+r['new'] for s in b['inline_scopes']]
   if 'four_dots' in k:origin='fast_dots.rs';owner='S4';why='Adopted dot entry/helper and removed closures'
   elif 'from_limbs' in k:origin='fast_pairing.rs';owner='S5';why='Adopted four-limb predicate and removed iterator closure'
   elif 'Q::from_limbs' in '\n'.join(scopes):origin='fast_pairing.rs';owner='S8' if 'EbyKDot' in k else 'S5';why='Unchanged caller source; changed inlined canonical constructor'
   elif k.split(':fn ',1)[1].startswith('weights::powers'):origin='weights.rs';owner='S3';why='Adopted generic loop and removed from_fn closure'
   elif 'weights::powers::<' in '\n'.join(scopes):
    origin='weights.rs';owner='S3' if 'fn weights::' in k else 'S1' if 'fn prepared_claim' in k else 'ordered caller join';why='Unchanged caller source; old powers inline scope is replaced by adopted loop/call lowering'
   else:raise AssertionError('Unexplained compiler body change: '+k)
   assert not r['ambiguous_signature'],k
   rows.append(dict(declaration=k,status=r['status'],owner=owner,origin=origin,explanation=why,
    old_body_hashes=[b['sha256'] for b in r['old']],new_body_hashes=[b['sha256'] for b in r['new']]))
  assert len(rows)==(0 if mode['mode']=='pool' else 17)
  assessed.append(dict(mode=mode['mode'],declarations=rows,counts=dict(collections.Counter(r['status'] for r in rows)),
   mono_coordinate_normalized_deltas=len(mono[mode['mode']]),mono_exact_deltas=len(exact[mode['mode']]),
   llvm_emitted_text_deltas=len(llvm['modes'][mode['mode']]),elf_symbol_name_groups_changed=len(elf[mode['mode']]['symbol_changes']),
   elf_edge_multiset_deltas=len(elf[mode['mode']]['edge_changes'])))
 for mode,records in elf.items():
  for r in records['edge_changes']:
   caller=r['item'][0]
   assert any(s in caller for s in ['::fast_dots::','::weights::','::verifier::Prepared::new','::candidate::tx2_common','core::array::try_from_fn']),caller
 overlay=load(B/'lead-repin-20261022/ownership.json');census=load(E/'declaration-ownership.json')
 assert census['overlay_records']==len(overlay['records'])==161
 ownership=dict(schema='s10-adopted-ownership-reconciliation-v1',source_revision=source['source_revision'],
  overlay_records=overlay['records'],changed_declaration_owners=overlay['changed_declarations'],
  frozen_mir_census=census,elf_records=1042,
  note='The 160 historical native candidates plus the new helper remain source ownership proposals. Removed closures are historical. New emitted body/ELF identities are independently enumerated; no old constant/closure/span ID is reused. Shared consumers do not duplicate owners.',complete=False)
 assessment=dict(schema='s10-adopted-change-assessment-v1',source_revision=source['source_revision'],adopted_files=adopted,
  changed_source_files=changed,other_source_differences=[r for r in changed if r['path'] not in adopted],modes=assessed,
  observed_frozen_mir_substantive_delta_confined_to_adopted_files_and_inline_callers=True,
  whole_source_delta_confined_to_three_files=False,
  limitation='The thirteen other census differences remain explicit. Selected frozen compiler MIR/mono/LLVM and final ELF comparisons show no Pool delta and explain the verifier body/call changes. This is compiler evidence, not a complete source extraction, codegen semantic proof, transferable inline map or source/model identity.',
  diff_versions='v1 captured normalized MIR/mono/ELF; v2 added exact mono and every emitted LLVM declaration/definition; v3 retained duplicate same-name symbol records. Only v3 is the final exhaustive symbol comparison; earlier scripts/receipts remain historical.')
 gates=dict(schema='s10-adopted-gates-v1',artifact_reproduction='PASS',elf_regeneration='PASS',cfg_140='PASS_PYTHON_CERTIFICATE',
  changed_declaration_ownership='PROPOSALS_RECORDED',source_inventory_completeness='INCOMPLETE',exit_status=2,
  s2_caller_identities='OPEN',source_order='OPEN',model_order='OPEN',final_inline_correspondence='OPEN',
  owner_acceptance='OPEN',concrete_source_calls_tree='OPEN',accepted_run_join='OPEN',headline_premises_removed=0,
  target='AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness',target_status='target not yet established')
 return {'change-assessment.json':assessment,'ownership-reconciliation.json':ownership,'gates.json':gates}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');a.add_argument('--require-complete',action='store_true');args=a.parse_args()
 for name,x in build().items():
  if args.check:assert (E/name).read_bytes()==enc(x),name
  else:(E/name).write_bytes(enc(x))
 print(json.dumps(dict(exit_status=2 if args.require_complete else 0,status='INCOMPLETE',headline_premises_removed=0)))
 if args.require_complete:raise SystemExit(2)
