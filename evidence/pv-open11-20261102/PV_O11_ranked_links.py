"""Bounded D573 inspection of ranks11–14. No proof or native-scope credit."""
from pathlib import Path
import hashlib, json, re, subprocess
D=Path(__file__).parent
S=D/'inputs/ranked'; S.mkdir(exist_ok=True)
rev='ccdc7f48c9'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins={}
def get(path):
    b=subprocess.check_output(['git','show',rev+':'+path])
    name=Path(path).name+('.txt' if path.endswith(('.lean','.md')) else '')
    dest=S/name
    if dest.exists(): assert dest.read_bytes()==b, 'snapshot collision'
    dest.write_bytes(b)
    pins[path]=dict(revision=rev,blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip(),snapshot=str(dest.relative_to(D)),sha256=sha(b))
    return b.decode()
def body(s,anchor):
    a=s.index('{',s.index(anchor));n=0
    for i in range(a,len(s)):
        n+=(s[i]=='{')-(s[i]=='}')
        if n==0:return s[a:i+1]
    raise ValueError(anchor)
def tok(s):
    return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S))
def eq(s,anchor,want): return tok(body(s,anchor))==tok(want)
def ordered(s,parts):
    positions=[s.index(p) for p in parts]
    return positions==sorted(positions) and len(set(positions))==len(positions)
R='docs/research/v8-r0-zk-20261009/lean/R1Z/'
models={n:get(R+n+'.lean') for n in [
 'PV_OWNM_V239','PV_OWNN_SourceDense','PV_OWNP_BuilderShape',
 'PDict_FormatterQuotient244','PDict_SinkCore244','PV_Canon_Deployment','PV_Canon_ReachedPolynomial']}
witness=get('evidence/pv-skwc-20261029/PV_SKWC_OWNM.lean')
old_report=get('evidence/pv-ownp-20261029/REPORT.md')
canon_obligations=get('evidence/pv-canon-20261027/OBLIGATIONS.md')
constraints=get('crates/aspis-statement/src/constraints_v4.rs')
sumcheck=get('crates/aspis-r1-cost-probe/src/host_sumcheck.rs')
adopted_path='evidence/pv-c474b-20261029/expected-sources.json'
expected=json.loads(get(adopted_path))
adopted={p:dict(expected=expected[p],actual=pins[p]['sha256'],equal=expected[p]==pins[p]['sha256'])
 for p in ['crates/aspis-statement/src/constraints_v4.rs','crates/aspis-r1-cost-probe/src/host_sumcheck.rs']}
z9e=(D/'inputs/client/z9e.rs').read_text()
fmt=(D/'inputs/io/core-fmt.rs').read_text()
client_pins=json.loads((D/'PV_O11_adopted-source-pins.json').read_text())
zp=client_pins['docs/research/v8-r0-zk-20261009/z4/z9e.rs']
assert sha(z9e.encode())==zp['sha256']==zp['adopted_expected']
checks={
 'both_new_sources_match_adopted_manifest':all(x['equal'] for x in adopted.values()),
 'mle_complete_value_body':eq(constraints,'pub fn multilinear_evaluate_qm31(','''{
   if column.len() != TRACE_ROWS { return None; }
   Some(sparse_eq_weights(point).into_iter().fold(QM31::ZERO, |sum, (row, weight)| {
      sum.add(weight.mul(column[row]))
   }),) }'''),
 'sparse_complete_body':eq(constraints,'fn sparse_eq_weights(','''{
   let trailing_boolean = point.iter().rev().take_while(|value| **value == QM31::ZERO || **value == QM31::ONE).count();
   let prefix_len = point.len() - trailing_boolean;
   let mut suffix = 0usize;
   for coordinate in &point[prefix_len..] { suffix = (suffix << 1) | usize::from(*coordinate == QM31::ONE); }
   let mut weights = Vec::with_capacity(1usize << prefix_len);
   for prefix in 0..(1usize << prefix_len) {
     let row = (prefix << trailing_boolean) | suffix;
     let mut weight = QM31::ONE;
     for (coordinate, value) in point[..prefix_len].iter().enumerate() {
       let bit = (prefix >> (prefix_len - 1 - coordinate)) & 1;
       weight = weight.mul(if bit == 0 { QM31::ONE.sub(*value) } else { *value });
     }
     weights.push((row, weight));
   }
   weights }'''),
 'scalar_law_already_proved_not_new': 'theorem concrete_source_dense :' in models['PV_OWNN_SourceDense'],
 'actual_builder_model_retains_built_equation':'(built : PV_OWNO_Builder.build' in models['PV_OWNP_BuilderShape'],
 'owned_link_same_source_and_world':'native i p lane = attach (resource i p lane)' in models['PV_OWNM_V239'],
 'owned_link_whole_plan_trace':'plan isBoolean (calls wirePoints i) failures' in models['PV_OWNM_V239'],
 'both_transcript_links_operational': all(x in models['PV_OWNM_V239'] for x in ['i.point = reconstruct879 i.pubData','i.point = reconstruct890 i.pubData']),
 'satisfiability_is_model_native_defined_by_attach': 'def native (i : Input)' in witness and 'attach (resource i p lane)' in witness and 'theorem satisfiable' in witness,
 'prior_failed_samplecarrier_retained_not_retried': '67296 failed' in old_report and 'uncredited' in old_report,
 'p_r1_complete_selected_body':eq(z9e,'pub fn p_r1_check(','''{
   let mut tm = R1CheckTimes::default();
   install_quiet_hook();
   QUIET.with(|q| q.set(true));
   let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Option<bool> {
     let t = Instant::now();
     let p = public_data(ch)?;
     tm.public_data = t.elapsed().as_secs_f64();
     let t = Instant::now();
     let (cert, _) = emit(&p);
     tm.emit = t.elapsed().as_secs_f64();
     let cert = cert?;
     let t = Instant::now();
     let ln = Lanes::new(&p.cx);
     let (mut pb, cc) = convert(&p, &cert, &ln)?;
     extracted_builders(&p, &cert, &ln, &mut pb)?;
     tm.builders = t.elapsed().as_secs_f64();
     let t = Instant::now();
     let ok = ck::check(&pb, &cc);
     tm.check = t.elapsed().as_secs_f64();
     Some(ok)
   }));
   QUIET.with(|q| q.set(false));
   (matches!(verdict, Ok(Some(true))), tm) }'''),
 'quiet_hook_complete':eq(z9e,'fn install_quiet_hook(','''{
   QUIET_HOOK.call_once(|| {
     let previous = std::panic::take_hook();
     std::panic::set_hook(Box::new(move |info| {
       if !QUIET.with(|q| q.get()) && !ck::native_workers::is_worker() { previous(info) }
     }));
   }); }'''),
 'public_data_transport_and_query_gates_retained':all(x in body(z9e,'fn public_data(') for x in ['z5::is_selected()', 'z5::transport()', 'z5::set_transport(pi)', 'qs.sort_unstable()', 'qs.dedup()', 'u >= 1 << 18']),
 'adopted_profile_abort':'panic = "abort"' in (D/'inputs/client/tool-Cargo.toml').read_text(),
 'formatter_native_writer_borrow': "buf: &'a mut (dyn Write + 'a)," in fmt,
 'formatter_write_str_forwards_complete_result':eq(fmt,'pub fn write_str(&mut self, data:', '{ self.buf.write_str(data) }'),
 'reference_formatter_is_safe_quotient':'Its native association remains separate.' in models['PDict_FormatterQuotient244'],
 'sink_reference_retains_failure_state':'(failed,{ f with sink := sink, calls := f.calls ++ [bytes] })' in models['PDict_SinkCore244'],
 'reference_type27_not_native_proof':'Reference carrier installation, not an unconditional native adequacy claim.' in models['PDict_FormatterQuotient244'],
 'recursive_sumcheck_complete_control':eq(sumcheck,'fn prove_sumcheck_rounds<','''{
   if round==10 {
     if oracle.evaluate(&point)?!=running {return Err(Error::Terminal);}
     return Ok((point,running));
   }
   let (point,running)=prove_sumcheck_round(transcript,output,point,running,round,oracle)?;
   prove_sumcheck_rounds(transcript,output,point,running,round+1,oracle) }'''),
 'sumcheck_entry_starts_at_zero':'prove_sumcheck_rounds(transcript,output,[QM31::ZERO;10],initial_claim,0,oracle)' in sumcheck,
 'adopted_ct_parallel_values_branch':'''#[cfg(feature="ct-host-prover")]
            {''' in sumcheck and 'crate::host_work::map(100+round,28*assignments' in sumcheck and 'values=merge_evaluations(&evaluations,assignments)?;' in sumcheck,
 'native_op121_prefix_order': ordered(body(sumcheck,'fn prove_sumcheck_round<'),['values=merge_evaluations(&evaluations,assignments)?;','let polynomial = interpolate(&values);','point[round] = transcript.semantic(15 + round as u8, &framed)?;','output.extend_from_slice(&framed);','running = evaluate_state_only_polynomial(&polynomial, point[round]);']),
 'prefix_link_requires_actual_reached_operands': '∀ p q, reached p q → ∃ e : ExtractedPrefix base ops, e.coefficients=p ∧ e.read=q' in models['PV_Canon_Deployment'],
 'prefix_has_four_exact_equations':all(x in models['PV_Canon_Deployment'] for x in ['round_lt : round.val < 10','interpolation :','semantic :','update :','readback :']),
 'evaluator_source_law_is_separate':'(shipped : Evaluator) (source : P_op121 shipped)' in models['PV_Canon_ReachedPolynomial'],
}
rows={
 'V239':dict(rank=11,status='OPEN',exact_premise=
  'At the SAME actual native op222/point_claims execution instantiate the unchanged five-link conjunction: SourceDense (reuse concrete_source_dense only after its source/caller association), ActualInput, OwnedPublicPlan, Transcript879 and Transcript890. ActualInput needs the real accepted builder/parser/array/point-store histories, including current ct-host-prover evaluation scheduling, not an independently canonical array. OwnedPublicPlan must identify native Result/resource/post-world and the whole first-shape/null-stop plan at every transformed wire point and lane, including sparse Vec tuple initialization, into_iter/drop and allocator-abort prefixes. Transcript879 includes interpolation queries and the distinct terminal callback; Transcript890 reconstructs final alpha from actual public frames. SamePublic/SameSite/SameLengths and every decoder/carrier must be instantiated jointly, not by selecting native=attach in a model witness. No source arithmetic or finite schedule rerun supplies these instances.'),
 'V249':dict(rank=12,status='OPEN',exact_premise=
  'Install SAME op232 with the complete returned (bool,R1CheckTimes) and native ordered post-world, for actual R1PublicChallenges. Bind public_data selected-transport state, query sorting/dedup/range rejection, emitter/rank/certificate allocation and failures, convert, all extracted_builders and ck::check callees. Preserve four clock pairs and Once/TLS/panic-hook/worker behavior, including resource failures and every early Option rejection. The adopted panic=abort profile means catch_unwind does NOT convert a reached panic into a false return; bind its actual hook/abort prefix (or prove it unreachable on the unchanged actual domain), without resetting QUIET or inventing drops on that terminal path. Source documentation claiming any panic is a rejection is not the deployed semantic law. No new success assumption or T field; full native joint observer and V370 retained.'),
 'V269':dict(rank=13,status='OPEN',exact_premise=
  'Install SAME ExternalTypes.op27 with the actual native FormattingOptions and borrowed dyn fmt::Write writer, options/borrow identity and error/state/payload observations for every reached formatter operation. In particular Formatter::write_str returns the actual writer Result and preserves its partial post-state on Err. Bind existing SinkCore/FormatterQuotient emit and options to those native transitions, including dynamic dispatch, formatting options and caller stop-on-error schedule; its generic sink transport is not a supplied native leaf. Alternatively prove each reached call unreachable under the existing guarded endpoint domain or its writer infallible per fmt-1; stderr/JSON/Debug observable paths require a faithful model. Constant client report bytes reduce particular diagnostics only, not arbitrary Formatter or whole-client observer adequacy. No Unit/always-Ok substitution.'),
 'V403':dict(rank=14,status='OPEN',exact_premise=
  'Discharge unchanged PV_Canon.P_NativePrefixBinding for the actual reached relation at EVERY native op121 event in the recursive installed records/host_sumcheck caller. Supply the SAME ExtractedPrefix coefficient/challenge operands, round<10, interpolation, semantic transcript, array-update and readback equations. Entry is round0; success recurses round+1 and round10 performs a distinct terminal oracle callback. The adopted ct-host-prover branch obtains values via host_work::map then ordered merge before interpolation; retain its failures and state when associating the selected dictionary. Bind actual records/transcript frame and successful/error prefixes rather than defining reached as only the proved prefix. The separate P_op121 evaluator-source law remains separate; local canonical producer facts, a bounded-round model or a chosen dictionary do not discharge this native-prefix premise. No new T field.'),
}
result=dict(classification='script-checked source/statement census only; no newly proved theorem, own-1 complete binding or restored row',revision=rev,
 checks=checks,ok=all(checks.values()),rows=rows,pins=pins,adopted_source_identity=adopted,
 local_inputs={str(p.relative_to(D)):sha(p.read_bytes()) for p in [D/'inputs/client/z9e.rs',D/'inputs/io/core-fmt.rs',D/'inputs/client/tool-Cargo.toml']},
 attempts={r:dict(source_inspection_passes=1,lean=0,native=0) for r in rows},
 retained_evidence={'V239':'prior SourceDense and model satisfiability statements inspected, not recompiled/audited',
   'panic_abort':'N90506 retained fixture supports no unwind under abort; not rerun, not a native P_R1 panic witness',
   'fmt-1':'existing owner rule retained; no quarantined Unit formatter semantics credited'},
 restored=0,premises_removed=0,premises_added=0,premises_weakened=0,next_rank=15,next_row='V374')
(D/'PV_O11_ranked-links.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(ok=result['ok'],checks=len(checks),failed=[k for k,v in checks.items() if not v],restored=0)))
assert result['ok']
