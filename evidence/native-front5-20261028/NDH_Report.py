from pathlib import Path
import json
E=Path(__file__).resolve().parent
inv=json.loads((E/'NDH_INVENTORY.json').read_text());cert={c['function']:c for c in json.loads((E/'NDH_CERTIFICATES.json').read_text())}
open_notes={
'filled':'K069/K070/K071 cover empty/singleton u32 only. Arbitrary n/T requires a native resize/allocation step, KMX frame and allocator/error association to the two adopted heap.filled owners; no full Vec/borrowed-result substitution is admitted.',
'FibreIndex::new':'K013/K014 native full constructor and E001 valid-index reference pass. No reached executable cohort constructor exists (FibreIndex is a Usize alias); actual native query/constructor admission and same-index association still need the native query caller, including block_rank/from_fn.',
'four_dots_one':'Native nested-loop iteration and byte/coefficient/load/store association absent. Field products must remain opaque with Lean-discharged laws; no multiplication was attempted in Kani. Existing FIp dots arithmetic does not instantiate the native step.',
'pow5':'NDH_Pow5.value proves the concrete emitted M31 three-product/fifth-power law and canonical outputs. A native three-call opaque log and canonical caller domain still need Kani; multiplication itself must never be proved there.',
'block_rank':'K053/K054 prove the exact arbitrary word callback; NDH_BlockRank.total supplies adopted model totality/order. Native std::from_fn capture/write/array correspondence needs a KMX-controlled arbitrary pre-state step. Old copy-dependent bulk from_fn receipts are not reused.',
'semantic_value':'Exact native reverse-iterator/Horner iteration with input/alpha/index/frame and Lean-discharged multiplication call association is absent. The emitted semantic loop and prior mathematical arithmetic alone cannot create that native trace.',
'selected_mask_linears':'No native one-iteration/load/store call-log packet for the factor/mask schedule. Lower raw field/multiplier domains and actual chosen array cells must be established at each call; no whole-array Kani or source equality is assumed.',
'add_small_base_p':'K049/K050 prove one scalar digit/carry body against E002. Native mutable-array iterator position, write/frame and complete candidate-loop association still need an arbitrary pre-state native step; scalar arithmetic alone is not that iterator proof.',
'decode_pool_v1_pair_live_snapshot_v1':'K078 checks short length rejection only. Full native field/error/canonicality windows and aggregate record/array frame are absent; required contract/result-shape controls and same-input parent association are not supplied by the existing emitted decoder.',
'state_only_statement_points':'No native loop/call-association packet for the actual point/weight schedule. The FIn model remains available; concrete native callee domains, argument positions and state frame need Kani before a new composition can be credited.',
'mark':'Deployed body has no detail-phases callback, but the observer interface is Option<fn>. Rule14/K-2 quarantine forbids credit from a dependent Kani pass; an admitted erasure/native route or lead ruling is needed. No quarantined pass was renamed or credited.',
'decode_pair_afterstate_boxed_v1':'K080 is an unpaired tiny rejection diagnostic, not credit. Full native decoder Result/error, Box allocation/move/cleanup and same-input call association remain; the pinned borrowed/Box/Vec interface restrictions cannot be fixed by a Lean wrapper.',
'VerifierEntryStatusV1::try_from':'K065/K066 provide native value/rejection gates; E001 and NDH_RegistryPrimitives give all four nominal values and invalid cases. Actual function-contract/result-shape packet and association inside the real entry decoder/SDK free codec call are absent.',
'decode_pool_identity_v1':'K078/K079 supply a paired short-rejection fragment only. Valid144-byte native field/canonicality/array windows and the reference-to-actual codec call/record association remain; a whole-codec equality is not assumed.',
'expand_semantic':'No complete native outer-row/inner-value loop step/frame and every-callee domain packet. NCO scalar row_shape/compact_row evidence is reused only in its original scope; its timed-out complete validator/caller shape is not rerun or promoted.',
'decode_pool_v1_pair_forest_checkpoint_v1':'K078 includes a short-rejection diagnostic; it does not cover the full192-byte codec, all errors/fields/canonical words, copies or same SDK input. Native KMX windows and actual op49 call association remain.',
'observer':'Option<fn> return is quarantined by K-2. No new native credit; existing release-None/model facts do not clear the quarantine or supply actual program-entry association.',
'admitted':'K067/K068 prove actual predicate versus E001 for all slices up to1232 bytes under deployed program features. Both inventory counterparts are unrelated theorems named admitted. A reached actual entry/admission counterpart and source/SDK call association are absent; no unbounded/domain transport is inferred.'}
lines=['# NDH frontier bridges','',
'Headline `AspisR1.RPx_Deployed.deployed`; deployed **100-bit per-attempt target not established**. Privacy and two transactions unchanged. L154 remains a statement parameter.',
'', '**10 CLOSED local body-bridge domains; 27 OPEN representatives.** Nineteen functions have completed native/value/reference components; nine of those still fail a required instance/control condition. CLOSED below means local on the listed domain, represented as CLOSED-CONDITIONAL in NCZ. No enclosing SDK/composed/source-to-ELF closure is claimed.',
'', 'The early four registry-slot closure labels are superseded: corrected immutable slots26/28 and paused25/27 are represented, but ruling(s)(ii) still requires actual SDK call-site association. Typed candidate/tail equations plus source syntax are not that native instance. QueryScan::finish also stays OPEN under ruling(t).',
'', '| Function | Dependent rows | Status | Evidence and domain / exact obstacle |','|---|---:|---|---|']
opens=[]
for r in inv:
 f=r['representative'];name=f.split('::',1)[1];c=cert.get(f)
 if c and c['status']=='CLOSED-CONDITIONAL':
  state='CLOSED (local)';note=c['domain']+' '+c['method']+'; '+', '.join(c['kani'])+'; '+', '.join(t for ts in c['lean'].values() for t in ts)+'. '+c['limits']
 else:
  state='OPEN'
  if c:note=c['component_status']+'; '+c['open_obligation']+' Components: '+', '.join(c['kani'])+'; '+', '.join(t for ts in c['lean'].values() for t in ts)+'.'
  else:note=open_notes[name]
  opens.append(dict(function=f,reason=note,requires='new native/call-site/fidelity evidence, or K-2 ruling; existing/new mathematical components do not establish it'))
 lines.append(f"| `{f}` | {r['dependent_rows']} | {state} | {note.replace('|','/')} |")
lines += ['', '## Method and evidence limits','',
'No `stub_verified` or native call-site replacement is used. Actual function contracts are body-check packets; a passed body check is not proof that every interface shape is admitted for substitution. Slot offsets and division use exact native single steps plus symbolic Lean induction/source association. No SHA implementation, field multiplication, whole-buffer Kani proof, XRn_Join kit, output-byte guard adapter or function-pointer verdict is used.',
'', 'Every Kani attempt validates the frozen package/edge graph before execution, offline, records resolved features for every crate, checks the lock afterward, and checks exact KMX file hashes. KMX slice controls K001/K002 and pointer controls K027/K028 are paired; individual claimed packets also have failing controls. All new top theorems have printed standard-axiom audits in their successful receipts.',
'', 'Native-contract semantic transport is the owner-approved P6/D188 tool-trust **reclassification**, never premise removal. Runtime SHA value, SDK/Std/allocator/runtime/ABI interpretation and all enclosing caller-domain/ordered-effect/source-to-ELF obligations remain explicit.',
'', 'The private ledger is validated using the unchanged `NCZ_validate.py::validate_invariants`; this is structural/evidence validation, not adoption into NCZ collect()\'s frozen historical merged report index. Baseline critical-path ranking remains marked historical.']
(E/'NDH_FRONTIER_BRIDGES.md').write_text('\n'.join(lines)+'\n')
(E/'NDH_OPEN_OBLIGATIONS.json').write_text(json.dumps(opens,indent=2)+'\n')
print('10 local CLOSED /',len(opens),'OPEN')
