#!/usr/bin/env python3
"""Explain exhaustive deltas and ownership without claiming S10 completeness."""
import argparse,collections,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence';E=B/'s10-repin2-20261023'
load=lambda p:json.loads(p.read_text())
enc=lambda x:(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
def build():
 source=load(E/'source-inputs.json');diff=load(E/'mir-diff.json');alias=load(E/'alias-mir-diff.json');mono=load(E/'mono-diff.json');exact=load(E/'mono-exact-diff.json');llvm=load(E/'llvm-diff.json');elf=load(E/'elf-diff.json');inv=load(E/'inventory.json')
 changed=[r for r in source['files'] if r['changed']]
 assert len(changed)==5 and all(r['path'].startswith('programs/r1-cost-probe/src/') for r in changed)
 children=load(E/'child-pins.json');assert len(children['helpers'])==27
 assessed=[]
 for mode in diff['modes']:
  m=mode['mode'];ar=next(r for r in alias['modes'] if r['mode']==m)
  index=collections.defaultdict(list)
  for category,group in [('alias/coordinate text only',ar['alias_or_coordinate_only']),('adapter caller replacement or owned support',ar['remaining_changes'])]:
   for r in group:
    for b in r['old']+r['new']:index[b['sha256']].append(dict(category=category,normalized_key=r['key']))
  rows=[]
  for r in mode['changed']:
   assert r['key'].startswith('aspis_r1_cost_probe_program:'),r['key']
   refs=[q for b in r['old']+r['new'] for q in index[b['sha256']]];assert refs,r['key']
   rows.append(dict(declaration=r['key'],status=r['status'],owner='S6' if any(t in r['key'] for t in ['fn first(', 'fn first_decoded(', 'fn first::{']) else 'S2',classification=sorted(set(q['category'] for q in refs)),alias_comparison_groups=sorted(set(q['normalized_key'] for q in refs)),old_body_hashes=[b['sha256'] for b in r['old']],new_body_hashes=[b['sha256'] for b in r['new']]))
  for r in ar['remaining_changes']:
   assert r['key'].startswith('aspis_r1_cost_probe_program:')
   assert any(s in r['key'] for s in ['owned::','fn snapshot(', 'fn require_zero(', 'fn stage1(', 'fn stage2(', 'fn stage1::', 'fn stage2::', 'fn stage1_owned','fn stage2_owned']),r['key']
  library=[]
  for r in elf[m]['edge_changes']:
   caller=r['item'][0]
   if 'aspis_r1_cost_probe_program::r1_pool_adapter::' not in caller:
    assert ('::clone::' in caller and ('ProgramError' in caller or 'string..String' in caller)),caller
    library.append(r)
  assessed.append(dict(mode=m,declarations=rows,exact_mir_counts=dict(collections.Counter(r['status'] for r in rows)),alias_only_groups=len(ar['alias_or_coordinate_only']),remaining_alias_normalized_groups=len(ar['remaining_changes']),mono_coordinate_normalized_deltas=len(mono[m]),mono_exact_deltas=len(exact[m]),llvm_emitted_text_deltas=len(llvm['modes'][m]),elf_symbol_name_groups_changed=len(elf[m]['symbol_changes']),elf_edge_multiset_deltas=len(elf[m]['edge_changes']),out_of_line_library_clone_edges=library))
 overlay=load(B/'lead-repin-20261022/ownership.json');census=load(E/'declaration-ownership.json')
 assert census['overlay_records']==len(overlay['records'])==161
 ownership=dict(schema='s10-owned-adapter-ownership-v1',source_revision=source['source_revision'],overlay_records=overlay['records'],changed_declaration_owners=overlay['changed_declarations'],frozen_mir_census=census,elf_records=len(inv['declarations']),unassigned=inv['unassigned'],assigned_twice=inv['assigned_twice'],note='Historical overlay retains proposals, not compiler IDs. Owned adapter and its closure/glue declarations inherit S2; first/first_decoded retain S6. New library instances keep existing library-boundary proposals; no new trust admission. Final reachable/inlined source correspondence and owner acceptance remain open.',complete=False)
 assessment=dict(schema='s10-owned-adapter-change-assessment-v1',source_revision=source['source_revision'],comparison_source_revision=source['comparison_source_revision'],changed_source_files=changed,unchanged_adapter_helper_cuts=children,modes=assessed,child_generic_mir_unchanged=True,substantive_source_and_project_mir_delta_confined_to_adapter_caller_glue=True,whole_source_delta_confined_to_adapter_files=False,qualification='The five-file source delta also includes test-only lib.rs wiring and adapter_rw_tests.rs. Exact MIR signatures include pretty-printer alias qualification; the supplemental explicit-alias diff isolates owned caller/support changes. Out-of-line ProgramError::clone and String::clone are newly emitted library support, not inlined adapter code. Raw ELF bodies also reflect call relocation/layout. Strict confinement of every machine-byte or emitted declaration change to r1_pool_adapter*.rs plus only inlined code would be false.',limitation='No new whole-source extraction, compiler semantic proof, final DWARF inline map or source/model execution identity. Exact raw lists remain authoritative; alias normalization only explains textual identity.')
 gates=dict(schema='s10-owned-adapter-gates-v1',artifact_reproduction='PASS',elf_regeneration='PASS',cfg_140='PASS_PYTHON_CERTIFICATE',reselected_ordering_facts=[],changed_declaration_ownership='PROPOSALS_RECORDED',source_inventory_completeness='INCOMPLETE',exit_status=2,s2_caller_identities='OPEN',source_order='OPEN',model_order='OPEN',final_inline_correspondence='OPEN',owner_acceptance='OPEN',concrete_source_calls_tree='OPEN',accepted_run_join='OPEN',headline_premises_removed=0,target='AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness',target_status='target not yet established')
 return {'change-assessment.json':assessment,'ownership-reconciliation.json':ownership,'gates.json':gates}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');a.add_argument('--require-complete',action='store_true');args=a.parse_args()
 for name,x in build().items():
  if args.check:assert (E/name).read_bytes()==enc(x),name
  else:(E/name).write_bytes(enc(x))
 print(json.dumps(dict(exit_status=2 if args.require_complete else 0,status='INCOMPLETE',headline_premises_removed=0)))
 if args.require_complete:raise SystemExit(2)
