#!/usr/bin/env python3
"""Explain all H5 deltas; preserve the incomplete S2/source identity gates."""
import argparse,collections,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence';E=B/'s10-repin3-20261023'
load=lambda p:json.loads(p.read_text());enc=lambda x:(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
def build():
 source=load(E/'source-inputs.json');diff=load(E/'mir-diff.json');alias=load(E/'alias-mir-diff.json');mono=load(E/'mono-diff.json');exact=load(E/'mono-exact-diff.json');llvm=load(E/'llvm-diff.json');elf=load(E/'elf-diff.json');inv=load(E/'inventory.json');changedowners=load(E/'changed-declaration-ownership.json')
 changed=[r for r in source['files'] if r['changed']]
 expected={'crates/aspis-core/src/state_only_prefix.rs','crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/fast_pairing.rs','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','crates/aspis-r1-cost-probe/src/lib.rs'}
 assert {r['path'] for r in changed}==expected
 assessed=[]
 for mode in diff['modes']:
  m=mode['mode'];ar=next(r for r in alias['modes'] if r['mode']==m);rows=[]
  for r in mode['changed']:
   key=r['key']
   own=next(o for o in changedowners['records'] if o['mode']==m and o['key']==key)
   if key.startswith('aspis_core:'):
    assert 'fn state_only_statement_points(' in key
    file='crates/aspis-core/src/state_only_prefix.rs';why='adopted H5 two-write Core helper'
   elif key.startswith('aspis_r1_cost_probe_program:'):
    assert 'fn require_zero(' in key
    file='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs';why='adopted H5 indexed tail scanner'
   elif any(t in key for t in ['canonical::','fn checked_q(', 'fn fast_pairing::']):
    file='crates/aspis-r1-cost-probe/src/fast_pairing.rs';why='H5 canonical arithmetic/constructor or its inlined checked_q/EbyKDot caller; raw exact text retained'
   else:
    assert key.startswith('aspis_r1_cost_probe:')
    allowed=['factored_s2_libra_weights','grouped_inactive_pair','high_dot','kpowers','partial_dot','process_kind','process_regular_kinds','push_byte_products','reduce_pair','s2_grouped_inactive_pair','shared_high','shared_partials','shared_two_point_guard','twofold_libra_weights','weights::']
    assert any('fn '+s in key for s in allowed),key
    file='crates/aspis-r1-cost-probe/src/weights.rs';why='adopted H5 weights declaration/closure addition, removal or rewritten body'
   rows.append(dict(declaration=key,status=r['status'],source_file=file,classification=why,old_body_hashes=[b['sha256'] for b in r['old']],new_body_hashes=[b['sha256'] for b in r['new']],old_ownership_proposals=own['old'],new_ownership_proposals=own['new']))
  # Every changed endpoint-name multiset is retained, including library edges.
  edgecallers=[]
  for caller in sorted({r['item'][0] for r in elf[m]['edge_changes']}):
   if '::weights::' in caller:why='adopted H5 weights body/new helper'
   elif '::state_only_prefix::state_only_statement_points::' in caller:why='adopted H5 Core helper'
   elif '::verifier::' in caller:why='caller of changed/new/removed H5 weights or dot helper'
   elif '::heap::uninit::' in caller or 'core::array::try_from_fn::' in caller:why='removed out-of-line allocation/array support for old weights implementation'
   else:raise AssertionError(caller)
   edgecallers.append(dict(caller=caller,classification=why,edges=[r for r in elf[m]['edge_changes'] if r['item'][0]==caller]))
  assessed.append(dict(mode=m,declarations=rows,exact_mir_counts=dict(collections.Counter(r['status'] for r in rows)),alias_or_coordinate_only_groups=len(ar['alias_or_coordinate_only']),remaining_alias_normalized_groups=len(ar['remaining_changes']),mono_coordinate_normalized_deltas=len(mono[m]),mono_exact_deltas=len(exact[m]),llvm_emitted_text_deltas=len(llvm['modes'][m]),elf_symbol_name_groups_changed=len(elf[m]['symbol_changes']),elf_edge_multiset_deltas=len(elf[m]['edge_changes']),changed_edge_callers=edgecallers))
 overlay=load(B/'lead-repin-20261022/ownership.json');census=load(E/'declaration-ownership.json');assert census['overlay_records']==len(overlay['records'])==161
 ownership=dict(schema='s10-h5-ownership-v1',source_revision=source['source_revision'],overlay_records=overlay['records'],changed_declaration_owners=changedowners,frozen_mir_census=census,elf_records=len(inv['declarations']),unassigned=inv['unassigned'],assigned_twice=inv['assigned_twice'],note='One disjoint proposed owner/boundary per emitted occurrence, using retained policy and lead overlay. The overlay retains its historical source proposal scope; actual compiler IDs/body hashes are regenerated. Existing policy is extended to new helpers by their actual source placement. No owner acceptance or final deployed reachable/inline correspondence claimed.',complete=False)
 assessment=dict(schema='s10-h5-change-assessment-v1',source_revision=source['source_revision'],comparison_source_revision=source['comparison_source_revision'],changed_source_files=changed,unchanged_adapter_helper_cuts=load(E/'child-pins.json'),modes=assessed,child_generic_mir_unchanged=False,substantive_source_and_project_mir_delta_confined_to_adapter_caller_glue=False,whole_source_delta_confined_to_adapter_files=False,qualification='The requested adapter-only confinement is false against re-pin2: H5 explicitly adopts weights.rs, fast_pairing.rs and Core state_only_prefix.rs child changes. The actual r1_pool_adapter.rs and fast_dots.rs remain identical. lib.rs additionally wires a cfg-excluded host client. All observed changed generic MIR groups are in those H5 child files or the owned tail scanner. Machine edge callers additionally include verifier consumers and removed old out-of-line allocation/array support. Raw LLVM/ELF hashes include text/layout/relocation changes and do not establish semantic equivalence.',pool='Pool ELF, symbol map, mono records and endpoint-name edge multisets are identical. Its emitted Core generic state_only_statement_points body changes, and four non-final LLVM text groups change; dead/non-linked source observations are not changes to the identical final ELF.',limitation='Full exact lists are authoritative; same-name duplicates are retained without guessed instance pairing. No compiler semantic proof, fresh Charon/Aeneas whole-source extraction, final DWARF inline map or source/model identity is supplied.')
 gates=dict(schema='s10-h5-gates-v1',artifact_reproduction='PASS_DEFAULT_POOL; DEVNET_HASH_DISCOVERED',elf_regeneration='PASS',cfg_140='PASS_PYTHON_CERTIFICATE',reselected_ordering_facts=[],changed_declaration_ownership='PROPOSALS_RECORDED',source_inventory_completeness='INCOMPLETE',exit_status=2,s2_caller_identities='OPEN',source_order='OPEN',model_order='OPEN',final_inline_correspondence='OPEN',owner_acceptance='OPEN',concrete_source_calls_tree='OPEN',accepted_run_join='OPEN',headline_premises_removed=0,target='AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness',target_status='target not yet established')
 return {'change-assessment.json':assessment,'ownership-reconciliation.json':ownership,'gates.json':gates}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');a.add_argument('--require-complete',action='store_true');args=a.parse_args()
 for name,x in build().items():
  if args.check:assert (E/name).read_bytes()==enc(x),name
  else:(E/name).write_bytes(enc(x))
 print(json.dumps(dict(exit_status=2 if args.require_complete else 0,status='INCOMPLETE',headline_premises_removed=0)))
 if args.require_complete:raise SystemExit(2)
