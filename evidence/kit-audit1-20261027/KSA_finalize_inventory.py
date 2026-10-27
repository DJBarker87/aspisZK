from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;p=E/'KSA_inventory.json';d=json.loads(p.read_text())
bad={
 'XRn_Join_mpow':('KSA_L002 / XSd_InverseShape.inverse_spine','Replace inverse consumers with AspisR1.SAQ_Inverse.source or the adopted R72 fixed inverse chain; do not repair this helper.'),
 'XRn_Join_qpow':('KSA_L002 generic exponent-two; KSA_L027/028 degree26','Use emitted FIo_Native.aspis_core.field.QM31.pow for u64 powers; for inversion use adopted R72 QM31.try_inv; use emitted selected-mask power26 chain.'),
 'aspis_core.field.M31.inv':('KSA_L002 inverse mismatch; KSA_R002 inverse2','AspisR1.SAQ_Inverse.source / AspisR1M31Inverse.field.M31.inv; adopted R72 inverse chain.'),
 'aspis_core.circle.secure_ood_circle_point_from_parameter':('KSA_R002 both canonical fallback parameters; inherited LPo obstruction','AspisR72Sampler.circle.secure_ood_circle_point_from_parameter and the adopted wrapper adapter.'),
 'sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once':('KSA_R002 fallback parameters; CDX/LPo retained wrapper provenance','Adopted RPz7_AspisR1CircleSampleWrapper_FunsExternal transcript.circle_fallback_point / AspisR1CircleFallback.transcript.circle_fallback_point.'),
 'aspis_core.state_only_hiding.state_only_selected_mask_value':('KSA_L028 KSA.mask_value plus KSA_R002','AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value; adopted wrapper AspisR1.FIp_SemanticArithmetic.mask, with FIp_MaskValue.source canonicality conditions retained.'),
 'aspis_core.field.wide_exact.WideExact.mul_qm31':('KSA_L029 KSA.mixed_value plus KSA_R004','FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31, lean/FIo_NativeFuns.lean:409; canonical_qm31 is already in that body.')}
small={'aspis_core.field.P':'p','aspis_core.field.M31.ZERO':'zero','aspis_core.field.M31.ONE':'one','aspis_core.field.M31.Insts.CoreCloneClone.clone':'clone','aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq':'eq','field.M31.add':'add','aspis_core.field.M31.sub':'sub','aspis_core.field.M31.mul':'mul','aspis_core.field.M31.double':'double','aspis_core.field.M31.reduce_u64':'reduce','aspis_core.field.CM31.new':'cm_new','aspis_core.field.CM31.mul':'cm_mul','aspis_core.field.QM31.Insts.CoreCloneClone.clone':'q_clone','aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne':'q_ne','aspis_core.field.QM31.ZERO':'q_zero','aspis_core.field.QM31.ONE':'q_one','aspis_core.field.QM31.add':'q_add','aspis_core.field.QM31.mul':'q_mul','canon':'canonical','aspis_core.r0.domain.FibreIndex.new':'fibre_new','aspis_core.r0.domain.FibreIndex.get':'fibre_get','aspis_core.r0.merkle.C1_TAG':'c1_tag','aspis_core.r0.merkle.C2_TAG':'c2_tag'}
for suffix,th in [('ZERO','w_zero'),('ONE','w_one'),('new','w_new'),('from_qm31','w_from'),('Insts.CoreCmpPartialEqWideExact.ne','w_ne'),('add','w_add'),('sub','w_sub'),('mul','w_mul'),('mul_qm31','w_mulq'),('mul_m31','w_mulm')]:small['aspis_core.field.wide_exact.WideExact.'+suffix]=th
for r in d['rows']:
 r['kernel_checks']=('KSA_L030 KSA.Small.'+small[r['name']]) if r['name'] in small and 'XRn_Join_' in Path(r['file']).stem else 'No fresh per-definition kernel probe; retained proofs/provenance only; UNDETERMINED'
 r['native_checks']='No fresh differential of this definition; UNDETERMINED'
 r['replacement']='Emitted or adopted body; association still required.'
 if r['name'] in bad and Path(r['file']).stem.startswith('XRn_Join_'):
  r['verdict']='UNFAITHFUL';r['reason']=bad[r['name']][0];r['replacement']=bad[r['name']][1];r['native_checks']='KSA_R002 or KSA_R004 (see failure matrix)'
 if r['name'] in ['aspis_core.field.M31.from_le_bytes']:
  r['kernel_checks']='KSA_L002 zero/P probes';r['native_checks']='KSA_R002 six boundary words; equality holds on tested inputs'
 if r['name'].startswith('aspis_core.field.wide_exact.WideExact.') and r['name'].rsplit('.',1)[-1] in ['from_limbs','to_limbs','from_le_bytes','to_le_bytes','from_qm31','mul_qm31','mul_m31','add']:
  r['native_checks']='KSA_R002 canonical 0,1,2,P-1; KSA_R004 additionally noncanonical mixed multiplier seam'
 if r['name'] in ['oldQ','newQ']:r['kernel_checks']='KSA_L002 KSA.carrier_roundtrip, universal record roundtrip'
 if r['name']=='fast_pairing.canonical.Dot.push':
  r['verdict']='FAITHFUL';r['reason']='KSA_L031 transports the complete same-input emitted push for all input words and arbitrary sums; source/artifact trust retained.';r['kernel_checks']='KSA_L031 KSA.dot_native, universal emitted-body result';r['native_checks']='Retained LPn_Dot_push_LEAF native/Kani scope; no unchanged rerun'
# Small probes do not certify universal source fidelity, so remain UNDETERMINED unless a complete adopted-body theorem is separately identified.
p.write_text(json.dumps(d,indent=2)+'\n')
lines=['# Stand-in inventory','',f"Raw release `{d['raw']['path']}`, SHA256 `{d['raw']['sha256']}`.",'',f"{len(d['rows'])} declarations: all definitions/carriers in non-emitted kit files, 15 edited Funs declarations, and XRo/XSd successor adapters. Unchanged emitted Types are excluded. `KSA_inventory.json` retains full source hashes, candidate paths, emitted-body text comparisons, and per-row validation/replacement status.",'','FAITHFUL is reserved for a complete scoped association, not a passing fixture. UNDETERMINED includes untested definitions and adapters whose whole source/effects/carrier law remains open. Native tiny-field fixtures are not a whole verifier proof.','', '| File:line | Definition | Shipped counterpart or model | Raw comparison | Verdict | Kernel check | Native check |','|---|---|---|---|---|---|---|']
for r in d['rows']:lines.append(f"| {Path(r['file']).name}:{r['line']} | `{r['name']}` | {r['counterpart']} | {r['text_comparison']} | {r['verdict']} | {r['kernel_checks']} | {r['native_checks']} |")
(E/'KSA_INVENTORY.md').write_text('\n'.join(lines)+'\n')
print(collections.Counter(r['verdict'] for r in d['rows']))
