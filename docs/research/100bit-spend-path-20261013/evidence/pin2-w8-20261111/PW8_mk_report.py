#!/usr/bin/env python3
"""PW8: PIN2_VERIFYPREFIX_REPORT.json (schema of prov-p9a-20261110/PIN2_ADAPTER_REPORT.json, extended) from the receipts,
PW8_COMPARISON.json and PW8_SUBSTITUTION.json. usage: python3 PW8_mk_report.py"""
import json,sys
sys.dont_write_bytecode=True
from PW8_lib import sha
def run(r):
    rc=json.load(open(r+'/receipt.json'));p=json.load(open(r+'_emitted/'+r+'_PINS.json'));s=json.load(open(r+'_spec.json'))
    return dict(run=r,exit=rc['exit_status'],wall_seconds=round(rc['wall_seconds'],2),peak_rss_kib=int(rc['peak_rss_kib']),swaps=int(rc['swaps']),cgroup_memory_peak_bytes=int(rc['cgroup_memory_peak_bytes']),
      caps='MemoryHigh=3G MemoryMax=4G MemorySwapMax=0 TasksMax=64, timeout 180 s, systemd-run --user --scope',cargo_jobs='--jobs 4 + CARGO_BUILD_JOBS=4, -Zthreads=1',identity='by class receipt PCWE_E003',
      features=s['configuration']['features'],roots=s['configuration']['roots'],opaque=[o['path'] for o in s['opacity']],tools=p['tools'],aeneas_tool=s['aeneas_tool'],
      source=p['frozen_revision'],source_tree_git_hash=p['frozen_source_tree_git_hash'],llbc_sha256=p.get('llbc_sha256'),charon_exit=p.get('charon_exit'),aeneas_exit=p.get('aeneas_exit'),
      lock_unchanged=p['cargo_lock_sha256_before']==p['cargo_lock_sha256_after'],emission_sha256=p.get('output_sha256'),print_axioms='N/A: extract')
C=json.load(open('PW8_COMPARISON.json'));U=json.load(open('PW8_SUBSTITUTION.json'))
funcs=[dict(fn=r['declaration'],verdict=r['cls'],detail=r.get('reason') or r.get('transitive_via') or r.get('tool_map')) for r in C['gate_declarations']]
funcs.append(dict(fn='VerifyPrefix.verify (RPz7_S1SemanticPrefixModelV1; r1_semantic::verify_observed under the recorded fe80 substitution)',verdict='changed-new-gate (transitive; text equal to frozen after recorded maps)',
  detail=dict(pin2_pair='CANNOT_EXTRACT (row: arrow types) PW8_E001 exit 2: Aeneas 0d21a9ec "Arrow types are not supported yet", r1_semantic.rs 311:0-318:1, SymbolicToPureTypes.ml line 422; construct: fn-pointer parameter type obs : Observer = Option<fn(Phase)> in the root signature',
  fe80_tool='PW8_E003 exit 0; comparison (a) vs fe80 emission: mark identical, verify_observed naming-only (Digest32 path, aspis_statement prefix, Challenges path)',
  comparison_b=[(c['declaration'],c['equal_after_maps']) for c in U['comparison_b']],via='r1_semantic.public_transcript -> Public.public_bytes')))
funcs.append(dict(fn='VerifyPrefix.mark',verdict='identical (after recorded map)',detail='comparison (a) identical; (b) equal'))
funcs.append(dict(fn='VerifyPrefix.Finish',verdict='type abbreviation; derived from the verify_finish external signature',detail='differs from frozen only by redundant parentheses'))
D=json.load(open('PW8_NEWGATE_DECLS.json'));inv={'aspis_core.state_only_prefix.r0.Challenges':'r1_wire.Challenges'}
cls={r['declaration']:r['cls'] for r in C['gate_declarations']}
newgate_decls=[dict(declaration=k,section='1 (PW8_E004 Aeneas text)',vs_frozen_gate=cls.get(inv.get(k,k),'no gate counterpart')) for k in D['kept']]
newgate_decls+=[dict(declaration='PrefixAdapter.'+n,section='2 (scripted namespace copy of frozen ExtractedPrefixParseCore)',vs_frozen_gate='identical text, namespace AspisR1PublicPreparationPIN2.PrefixAdapter') for n in ['toOld','fromOld','toOld_fromOld','fromOld_toOld','errorFromOld','parseAccepted','parse_success']]
newgate_decls+=[dict(declaration=k,section='3 (PW8_SUBSTITUTION.json)',vs_frozen_gate='equal to RPz7 after recorded maps'+(' (redundant parentheses only)' if k.endswith('Finish') else '')) for k in ['VerifyPrefix.Finish','VerifyPrefix.mark','VerifyPrefix.verify']]
lg=open('PW8-COMPILE.tsv').read().strip().split('\n')[-1].split('\t')
R=dict(schema='PIN2_ADAPTER_REPORT/1 (PW8 verifier-prefix variant)',target_established=False,source='c7593d23fdc56fcee9a9df1628d5f63b52ac7a95',
 tool='SECOND (PIN2 pair): Charon 454586e9 (sha256 57aa2359...) + Aeneas 0d21a9ec (sha256 230ee9f0...) for PW8_E001/E002/E004 (E004 = E002 + root types Verified, SecureCirclePoint; the emission source of Section 1 and of the comparison); ORIGINAL fe80 pair Charon daad69be (XRa_bin) + Aeneas b59d5188-lean432-extended (sha256 c0cf4fcc...) for PW8_E003 (approved by the lead after E001); -abort-on-error on all three',
 extraction=[run('PW8_E001'),run('PW8_E002'),run('PW8_E003'),run('PW8_E004')],
 recipe=dict(frozen_gate='AspisR1PublicPreparation.{Types,Funs}: mirror-crate emission (tools/public-preparation-extraction-kit, crate aspis_r1_public_preparation); fresh = gate at 4bb3b3f by PCVL_E003/PRVEq_PP_l4 (Funs) and PCWM L005-L008 (Types, 4fcadd19f2e)',
  frozen_verifyprefix='RPz7_S1SemanticPrefixModelV1 = fe80 ExtractedVerifyPrefixModel (verify-helper-prefix-fe80-20261017, binding-audit.json identifier_map + binder) with verifier.Phase -> RPz7_PhaseIso.Phase',
  pin2_method='prov-p9f-20261110 PCXU_ scripts (renamed PW8_), payload = git archive of c7593d23fdc (NHR_FROZEN_PAYLOAD sha256 9fd007ce...)'),
 comparison=dict(counts=C['counts'],stop=C['stop'],table='PW8_COMPARISON.tsv',newgate_identity_all_token_identical=all(x['token_identical'] for x in C['newgate_identity']),newgate_identity_count=len(C['newgate_identity']),fresh_only=C['fresh_only'],fresh_externals=C['fresh_externals']),
 substitution=dict(file='PW8_SUBSTITUTION.json',input_sha256=U['input']['sha256'],output_sha256=U['output_sha256'],recorded_identifier_map=U['recorded_identifier_map'],phase_swap=U['phase_swap'],tool_map_entries=len(U['tool_map_entries_used'])),
 functions=funcs,
 new_gate_files={'PIN2_NEWGATE_verifyprefix.lean':D['sha256'],'layout':'lead option A: twin PIN2 types; imports PIN2_NEWGATE_r1_semantic (and through it _r0), AspisR1PrefixAggregateParser.Funs, RPz7_PhaseIso; %d emitted declarations kept, %d dropped as token-identical to the overlay NEWGATE files, dropped unreferenced: %s'%(len(D['kept']),len(D['dropped_identical_to_overlay']),D['dropped_unreferenced']),'declarations':newgate_decls},
 new_gate_compile=dict(id=lg[0],exit=int(lg[2]),wall_s=lg[3],max_rss_bytes=int(lg[4]),swaps=lg[5],source_sha256=lg[6],revision=lg[7],olean='/Users/dominic/aspis-lead-infra/l187-closure/overlay-PIN2-W8/PIN2_NEWGATE_verifyprefix.olean',
   olean_sha256_16=lg[10],lean='v4.32.0, one process, -M7000, -DElab.async=false, alarm 180 s',lean_path='overlay-HOST-P1 : overlay-PIN2 : objs : base (l187-closure)',
   print_axioms='7 reports (begin, semantic_validated, parseAccepted x2, parse_success, VerifyPrefix.mark: none, VerifyPrefix.verify): only propext, Classical.choice, Quot.sound; no sorryAx/ofReduceBool'),
 agreement_facts_for_W7='parseAccepted_agree (PIN2 PrefixAdapter.parseAccepted bytes = copy of frozen PrefixAdapter.parseAccepted bytes) rests on Section 2 being the namespace-only copy over the same AspisR1PrefixAggregateParser.r1_wire.Prefix.parse and on r1_wire.Prefix/r1_wire.Error being identical (E004 vs gate); begin_agree (PIN2 r1_wire.begin on copied inputs = copy of frozen r1_wire.begin) rests on the token-identity or tool-map-only class of begin and its closure (Prefix.record/validated_record, ValidatedRecord.impl.row/framed, SemanticTranscript.sample_block_validated/semantic_validated, sampler.*, CM31.new, QM31.ZERO, DOMAIN, SemanticTranscript) in PW8_COMPARISON.tsv plus the PCWN_NewLib branch_eq/from_residual_eq lemmas for the Infallible->Never encoding; neither is proved here.',
 candidate_trust_rows=[],
 cannot_extract=[dict(fn='r1_semantic::verify_observed',tool='Aeneas 0d21a9ec',run='PW8_E001',row='arrow types',construct='fn-pointer parameter type Option<fn(Phase)> (crate::verifier::Observer) in the root signature',location="r1_semantic.rs 311:0-318:1; Aeneas symbolic/SymbolicToPureTypes.ml line 422")],
 s1semanticcode_publictranscript='RPz7_S1SemanticCodePublicTranscriptV1.publicTranscript is not translator output: the gate public_transcript Aeneas body retyped into the PreparedHashCode Code monad (SemanticTranscript.new -> newTranscript), tied to the translator constant by the proved theorem publicTranscript_erasure (RPz7_S1SemanticCodePublicTranscriptExactV1)')
json.dump(R,open('PIN2_VERIFYPREFIX_REPORT.json','w'),indent=1,ensure_ascii=False);print(R['comparison']['counts'])
