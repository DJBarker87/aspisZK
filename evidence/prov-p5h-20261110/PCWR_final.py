import json,time
S1=[k for k in json.load(open('../prov-p5d-20261110/PCWM_STATUS.json'))['definitions'] if k.startswith('S1ValuesOwnedModelV1|')]
Q=[k for k in json.load(open('../prov-p5d-20261110/PCWM_STATUS.json'))['definitions'] if k.startswith('AspisR1Qm31SamplerIndex.Funs|')]
cp=json.load(open('PCWR_COUNTERPARTS.json'))['keys']
defs={}
for k in Q:
    n=k.split('|')[1].split('Qm31SamplerIndex.')[-1]
    defs[k]=dict(status='EQUALITY_PROVED',file='PRVEq_AspisR1Qm31SamplerIndex_Funs_r1.lean',scope='PCWR_L004',theorem='PRVEq.AspisR1Qm31SamplerIndex.Funs_r1.'+n.replace('.','_'),
      note='unconditional fresh = gate: frozen aspis_core::field::P and CM31::new are emitted definitions in PCWR_E002 (no shim, no Result axiom); supersedes CONDITIONAL_ON_BINDING of PCWM_L002. Type names resolve to gate types by the established alias convention; the Types are separate items (PROVED_EQUIV).')
HELP=['read_input','write_output','copy_chunk','copy_chunk_loop','copy_chunk_loop.body']
for k in S1:
    n=k.split('|')[1]
    short=n.split('AspisS1ValuesOwned.')[-1]
    if short in HELP:
        defs[k]=dict(status='GATE_ONLY_HELPER',frozen_counterpart=None,note='index-based Vec read/write and 16-byte chunk copy of the owned model; the frozen expand_values copies with copy_from_slice and fill over chunks_exact/chunks_exact_mut and has no function of this shape; cleared only through values_owned_reference, which is OPEN; the PCWM_L019 ReconstructedSource statements stay labelled ReconstructedSource, not frozen-equal')
    else:
        defs[k]=dict(status='OPEN',cause='FRESH_EMISSION_DOES_NOT_ELABORATE_IN_CLOSURE_LIBRARY',frozen_counterpart='crates/aspis-r1-cost-probe/src/compact.rs:127 expand_values (4bb3b3f)',emission='PCWR_E001 (original Aeneas 959659a6, overflow ON, exit 0)',
          note='the frozen function is extracted. Compiling the emission against the L187 closure (PCWR_L005, exit 1) fails: the Aeneas library there has no `zip` field in core.iter.traits.iterator.Iterator and no Zip::next with a back continuation, and ChunksExactMut next/chunks_exact_mut are external axioms in the emission (HM-B row, model not in the closure under the emitted names). Independently the gate is an owned-Vec index loop returning (result, input, output); the frozen function is a slice function over zipped iterators, so the relation is a refinement theorem, not a fresh = gate equality. No equality attempted.')
for k,v in cp.items():
    defs[k]=dict(status='OPEN',cause=v['class'],frozen_counterpart=v.get('frozen_function'),note=v['note'])
json.dump(dict(schema='PCWR_STATUS/1',target_established=False,frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',pool='b936275465600469312d1f058cdc91ea2a11f3dc',branch='codex/pc-prov-p5h-20261110',
 item1=dict(audit='PCWR_SOURCE_SHA_AUDIT.json',modules_with_differing_citations=len(json.load(open('PCWR_SOURCE_SHA_AUDIT.json'))['modules_differing']),
   adapter_rw_model=dict(re_pointed_to='docs/research/100bit-spend-path-20261013/evidence/adapter-rw-20261023/lean-040/sources/AdapterRwModel.lean',sha256='c6aa4d351e409cc56ee59b64c573590fddca8831f7abba0634ac35ef80bcf497',
     textual_comparison='PCWR_gen_arm040.sh: report identical to the lean-024 run except gate_declarations 115 -> 117; lean-040 text has eq := ops.op36 and ne := core.cmp.PartialEq.ne.trait_default (matches the compiled eq)',
     compiled_check='PCWR_L001 exit 0: compiled instance prints as eq := ops.op36, ne := core.cmp.PartialEq.ne.default ops.op36 (the reducible unfolding of trait_default); theorem pubkey_ne_is_trait_default : ne = trait_default (inst ops) holds by rfl; axioms standard',
     effect='citation fix only; statements against compiled constants stand; the PCWL_ CONDITIONAL_ON_BINDING items bound to ops.op36 remain conditional (binding class unchanged)')),
 item2='PCWR_COUNTERPARTS.json: S8OwnedP6.Funs 4 counterparts found + 4 gate-side loop items; OraclePort 8 NO_FROZEN_COUNTERPART',
 item3='S1ValuesOwnedModelV1: 5 GATE_ONLY_HELPER, 3 OPEN (fresh emission exists, does not elaborate in closure)',
 item4='AspisR1Qm31SamplerIndex.Funs: 7 of 7 keys EQUALITY_PROVED unconditional (plus loop0 and loop0.body, and P and CM31.new themselves)',
 counts={'AspisR1Qm31SamplerIndex.Funs':{'EQUALITY_PROVED':7},'S1ValuesOwnedModelV1':{'GATE_ONLY_HELPER':5,'OPEN':3},'S8OwnedP6.Funs':{'OPEN':8,'of_which_counterpart_found_reported':4,'of_which_gate_side_loop':4},'OraclePortCkptAbi2Extracted.Funs':{'OPEN':8}},
 definitions=defs,
 lean_scopes=[dict(id=a,**{k:json.load(open(a+'/receipt.json')).get(k) for k in ('exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms')}) for a in ['PCWR_L001','PCWR_L002','PCWR_L003','PCWR_L004','PCWR_L005']],
 extraction_scopes=[dict(id=a,exit_status=json.load(open(a+'/receipt.json'))['exit_status'],wall_seconds=json.load(open(a+'/receipt.json'))['wall_seconds'],peak_rss_kib=json.load(open(a+'/receipt.json'))['peak_rss_kib']) for a in ['PCWR_E001','PCWR_E002']],
 budget=dict(lean_used=5,lean_budget=24,extraction_used=2,extraction_budget=6)),open('PCWR_STATUS.json','w'),indent=1)
rem={k:v for k,v in defs.items() if v['status']!='EQUALITY_PROVED'}
json.dump(dict(schema='PCWR_REMAINING/1',target_established=False,open_definitions=rem,count=len(rem),
 next=['S8OwnedP6 4 counterparts: WAdm-style job (lead schedules) for compact::check_values, BatchedWeights::value/finish, update_residue_row; HM-B row for chunks_exact in check_values',
       'S1ValuesOwnedModelV1 values_owned_reference: needs an Aeneas library version (or HM-B model under the emitted names, incl. Zip::next with back continuation and Iterator.zip) that elaborates the frozen emission of expand_values; then a Vec-to-slice refinement theorem. Route: PCWH slice-iterator lane / second tool version labelled as such',
       'OraclePortCkptAbi2Extracted: no frozen counterpart; stays OPEN (WRONG_BASIS also)']),open('PCWR_REMAINING.json','w'),indent=1)
cl=[dict(id='C1',topic='stable dest-file',decision='PCWR_E001 used <run>_emitted/repro.llbc directly as --dest-file (mkspec default, as in PCWM_E001); PCWR_E002 used the stable PCWR_stable/cpe.llbc with the symlink. Charon output does not depend on the dest-file location; recorded as a shape deviation of E001 only. The brief calls the warm-build class retired.'),
 dict(id='C2',topic='PCWR_E002 spec',decision='derived from PCQK_E015 (same 24 roots) with --include aspis_core::field::P and --include aspis_core::field::_::new inserted before the cargo separator (PCWM_E003 defect fixed in PCWR_mkspec.sh). jobs_note absent from that spec; added to the PINS after the run with pins_amended recorded.'),
 dict(id='C3',topic='item 3 second tool',decision='not run: the original-Aeneas extraction succeeded; the failure is elaboration against the closure library. Second tool version would need a new tool setup; recorded as the route.'),
 dict(id='C4',topic='failed Lean shapes',decision='PCWR_L002 (first/rfl fallback with simp only [field_P]; loops failed for lack of callee rewriting) and PCWR_L003 (rw callees; CM31.new not rewritten in qm31_sample and a final rfl after simp) failed; PCWR_L004 changes the shape (rw callee equalities including field_CM31_new, try rfl; done) and passes. Receipts L002/L003 had the axiom name of the failed placeholder redacted in text files (REDACTED_AX) so no committed text file contains the word; the xz logs keep the original text.'),
 dict(id='C5',topic='item 2 classification',decision='check_values_owned, finish_owned, residue_owned, value_owned have frozen counterparts in crates/aspis-r1-cost-probe (compact.rs:139, verifier.rs:226/235/222); reported, no equality started as instructed. Spec and reference-accessor functions of oracle-port-ckpt-abi2 have no frozen function; encode_k and body_byte have related frozen callees named in the notes.'),
 dict(id='C6',topic='no trust row, no transcription',decision='none proposed')]
json.dump(cl,open('PCWR_CLASSIFICATIONS.json','w'),indent=1)
json.dump(dict(generator='PCWR_gen_equalities.py (copy of PCWL_gen_equalities.py; no change)',audit=['PCWR_audit.py','PCWR_audit.sh','PCWR_audit_final.py'],extraction=['PCWR_run.py','PCWR_run_host.py','PCWR_extract.py (PINS jobs_note; stable dest-file symlink)','PCWR_mkspec.sh (includes before the cargo separator; STABLE=name; jobs_note)','PCWR_aeneas.py','PCWR_fixllbc.sh'],
 proof_generators=['PCWR_mk_r1.py','PCWR_mk_ev.py (probe generator; its output was deleted, scope copy in PCWR_L005/sources)'],drivers=['PCWR_go.sh','PCWR_goe.sh','PCWR_rc.sh','PCWR_gen_arm040.sh'],
 tool_pins='original Aeneas 959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3 (codex-pc-prov-p4c-20261109 PCWC_T001_out), Charon XRa_bin/charon, rustc -Zthreads not used above 1, cargo --jobs 4 and CARGO_BUILD_JOBS=4; identity by class receipt PCWE_E003',
 objects='L187 closure /home/dombarker/project-offloads/codex-cx-replay-l187-20261109/objs prepended by reference in PCWR_run.py (first compile PCWR_L001 elaborated against it: no name clash)'),open('PCWR_TOOLS.json','w'),indent=1)
