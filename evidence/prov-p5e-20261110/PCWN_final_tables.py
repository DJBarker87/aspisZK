#!/usr/bin/env python3
"""PCWN: writes PCWN_STATUS/REMAINING/CLASSIFICATIONS/TOOLS from PCWN_TRIAGE.json and PCWN_SCOPES.json."""
import json,collections
tri=json.load(open('PCWN_TRIAGE.json'));scopes=json.load(open('PCWN_SCOPES.json'))
settled_here=[r['key'] for r in tri['keys'] if r['status']=='SETTLED' and r['evidence'].startswith('PCWN')]
settled_prior=[r['key'] for r in tri['keys'] if r['status']=='SETTLED' and r['evidence']=='PCVZ']
openk=[r for r in tri['keys'] if r['status']=='OPEN']
status=dict(schema='PCWN_STATUS/1',target_established=False,note='Target not yet established',frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 (Pool b936275465600469312d1f058cdc91ea2a11f3dc)',
 branch='codex/pc-prov-p5e-20261110',
 lean_scopes=dict(used=len(scopes),budget=35,item1_budget=3,note='L001-L003 item 1; L004 was the heartbeat-reset recheck of item 1, charged to the main batch; main batch L005-L021'),
 extraction_scopes=dict(used=0,budget=10,note='existing frozen emissions reused with their PINS: PCQK_E015 and E010 (P1n), PCVX_E012 (P3u), PCVJ_E002 (P1j), P2d NMH_wide_decode text'),
 cargo_jobs='not applicable: no extraction scope run; identity by class receipt PCWE_E003 not needed',
 item1=dict(claim='public_bytes fresh = gate with the abbrev removed; new-library Result.branch/from_residual/Never copied verbatim into PCWN_NewLib; transport lemmas from_residual_eq and branch_bind; nine fresh=gate theorems',file='PRVEq_PB_w3.lean',scope='PCWN_L004 exit 0, 21.4 s, peak 2.7 GB, swap 0',status='EQUALITY_PROVED',finding='the libraries differ in the empty type (Never vs core.convert.Infallible), not only the name; a literal equality is ill-typed, the proved statements are transports along the empty-type map'),
 settled_by_this_job=settled_here,
 settled_by_merged_jobs_recorded_not_reproved=settled_prior,
 extras_outside_the_12_modules=[e['key'] for e in tri['extra']],
 open_count=len(openk),
 open_by_cause=dict(collections.Counter(r['cause'].split('(')[0] for r in openk)),
 files=['PRVEq_PB_w3.lean','PRVEq_PCWN_TE.lean','PRVEq_AspisR1CanonicalQRawUnified_Types_p1.lean','PRVEq_FIo_QRawTypes_p1.lean','PRVEq_NEI_PushRaw_Types_p2.lean','PRVEq_Stage2ContinuationTypes_p3.lean','PRVEq_AspisR1CanonicalDotFinish_Funs_q1.lean','PRVEq_AspisR1CanonicalDotFinish_Types_p1.lean','PRVEq_AspisR1EbyKFinish_Types_p1.lean','PRVEq_AspisR1EbyKFinish_Funs_r1.lean','PRVEq_S8Kani2MutableSource_s1.lean','PRVEq_FinishCandidateExplicitOps_p1.lean'],
 axioms='every exit-0 scope: standard axioms only (propext, Classical.choice, Quot.sound), no sorry, no axiom, no native_decide, every theorem and lemma at maxHeartbeats 200000; see PCWN_SCOPES.json',
 differences_at_matching_configuration='none found; the only differences are the library model signatures (HM-B into_iter) and the Never/Infallible empty type',
 trust_rows='none added; HM-B (slice iterator) named for NEI update_residue_row, BatchedWeights.push and S8Kani2 push/finish; HM-D (Array.map model) used by the S8Kani2 value proof via the PCVZ lemmas')
json.dump(status,open('PCWN_STATUS.json','w'),indent=1)
rem=dict(schema='PCWN_REMAINING/1',target_established=False,note='Target not yet established',items=[dict(key=r['key'],cause=r['cause'],reason=r['reason']) for r in openk],
 next=['Aeneas patch (approved job) for nested-loop returns, then extract prepared_claim and compare CurrentClaimDotModel','HM-B: decide whether the two into_iter models (template vs hand-repaired transformer form) are identified under the HM-B row; then NEI update_residue_row/push and S8Kani2 push follow from loop_proj','Ops instances from fresh emissions (finish_relation_round, finish_query_dot*; Port3 batch*), conditional on binding by ruling; Port3 additionally needs an overflow-checks OFF emission of the candidate batch functions','QRaw closure and closure_1: lead decision whether a gate-only helper consumed only by an EQUALITY_PROVED parent counts as cleared'])
json.dump(rem,open('PCWN_REMAINING.json','w'),indent=1)
cl=dict(schema='PCWN_CLASSIFICATIONS/1',items=[
 dict(case='public_bytes library-name lemma: new library types the residual with Never, gate with Infallible',classification='transport along the empty-type map (PCWN_NewLib.castR) instead of a literal equality; fresh text references the verbatim new-library constants',reason='a literal equality is ill-typed; the transport lemmas are unconditional and the nine fresh=gate theorems hold with the new constants'),
 dict(case='item 1 budget: L004 reset-heartbeat recheck',classification='charged to the main batch',reason='the lemmas in the first file elaborated under the emission header limit 1000000; AGENTS and the brief require 200000 before the first lemma'),
 dict(case='Stage2ContinuationTypes composite fresh input',classification='PCVX_E012 (cost-probe) plus the WideExact structure from PCVJ_E002 (aspis-core), both frozen 4bb3b3f, recorded in PCWN_mk_s2_input.py',reason='cross-crate types are external in the cost-probe emission; the brief says use the aspis-core emission'),
 dict(case='QRaw Types name substitution fast_pairing.canonical.Q -> canonical.Q and Q.raw.closure -> closure_2',classification='recorded rename in PCWN_mk_qraw_input.py; the closure_2 identification is inherited from PCVZ closure_call',reason='gate closure_2 is the u64->u64 callback'),
 dict(case='DotFinish Funs reuse of the PCVZ EbyKFinish proof',classification='derived file; the four DotFinish gate bodies equal the EbyKFinish ones (diff of the gate sources)',reason='same text, same callbacks'),
 dict(case='alias identification of Dot/Q/Error/closure types in Funs files',classification='alias with Types evidence where a Types proof exists (DotFinish L016, QRaw L005/L006); FinishCandidateExplicitOps Error/closure text-identical only',reason='same practice as the earlier credited P1n/P3w files; stated in the triage'),
 dict(case='NEI update_residue_row/push fresh text does not elaborate against the gate environment',classification='DEPENDS_ON_LIBRARY_TRUST (HM-B), not a proof failure',reason='into_iter back type differs between the template and the repaired model; L012 not rerun'),
 dict(case='Array/Vec/Slice/Option field types in Types equivalences',classification='added to the generator as a field-type conversion through PRVEq_PCWN_TE',reason='Prepared, Accumulator, View carry such fields'),
 dict(case='Q.raw / closure_2.call / loop1 refinement credited by P3w',classification='recorded as SETTLED (merged PCVZ) or OPEN (refinement) without re-proof',reason='brief: subtract keys already proved by merged jobs')])
json.dump(cl,open('PCWN_CLASSIFICATIONS.json','w'),indent=1)
tools=dict(schema='PCWN_TOOLS/1',cargo_jobs='not applicable (no extraction scope)',identity='identity by class receipt PCWE_E003 not needed',files={
 'PCWN_run.py, PCWN_run_host.py':'client and host runner copied from P4x PCWH_run.py; LEAN_PATH adds PCVZ_exports (P3w, read-only) after the L187 objs; attempt ids PCWN_[ELT]nnn; Stream C share < 5',
 'PCWN_gen.py':'PCQK_gen_equalities.py (P1n) with three changes: guillemet field names in structure parsing; field-type conversion through Array/alloc.vec.Vec/Slice/Option via PCWN_TE; inductive and structure leaves as dependencies',
 'PRVEq_PCWN_TE.lean':'generic arrEquiv/vecEquiv/sliceEquiv (L011)',
 'PCWN_mk_w3.py, PCWN_newlib_block.lean':'item 1',
 'PCWN_mk_qraw_input.py, PCWN_mk_dot_input.py, PCWN_mk_s2_input.py':'derived fresh Types inputs with recorded substitutions',
 'PCWN_chain.sh':'serial scope launcher','PCWN_final_tables.py':'this table generator',
 'inputs/':'frozen emission text reused: E015_cp (PCQK_E015), E010_core (PCQK_E010), E012_s2 (PCVX_E012), PCVJ_top (PCVJ_E002)'},
 reuse='PRVEq_P3W_ArrayMap/ArrayMapMon/LoopMap copied from PCVZ (imported from PCVZ_exports)',
 sha256={'E015 Types':'6c455568a42196b151041ab95e3409d3f26fc90e9eb70c5fac49456894cf7874','E015 Funs':'ff07b2a01b0867229c45bbd7500a09856ea5f7ab1c5660ea05708888bb9940f7','E012 Types':'d8c78555848b943f0018a29973c2abdcf74dda5ea5d3f3e7e6f1307cc23a7c2d','PCVJ_E002 Types':'a74a05ae456df66bb9fcd67b7c4d7c0dcee49ae333a83474b55cb758d33fab5f'})
json.dump(tools,open('PCWN_TOOLS.json','w'),indent=1)
