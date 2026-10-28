from pathlib import Path
import json
E=Path(__file__).resolve().parent
rows=json.loads(Path('evidence/native-tx2e-20261027/NBK_MEMBER_STATUS.json').read_text())
for r in rows:
 r['inherited_status']=r['status'];r['inherited_evidence_or_open']=r.pop('evidence_or_open')
 r['native_status']=r['status'];r['model_status']='inherited' if r['status'].startswith('CLOSED') else 'OPEN'
 r['new_evidence']='Inherited exact domain and obligation retained; see preceding NBK member table. No promotion from standalone fragments.'
 f=r['id'].split('::')[-1];u=r['unit']
 if u=='U03' and r['status']=='OPEN':
  names={'decode_pool_v1_pair_verified_afterstate_v1':'NBN_AfterstateDecoderDependency.source / L074; native K012 same21 ranges, first error, parsed record and return fields', 'encode_pool_v1_pair_verified_afterstate_v1':'NBN_EncoderSummary.after_source / L057; imported validator/bytes/induction and all20 NBK fixed-row frames; native K008 copy32 and K009 iterator step', 'encode_pool_v1_pair_live_snapshot_v1':'NBN_EncoderSummary.live_source / L057; imported NBK live step/20-row induction/frame; native K005 fill step,K008 copy32,K009 iterator; all20 inherited row windows', 'encode_pool_v1_pair_late_public_statement_v1':'NBN_LateSummary.source / L060; arbitrary output length,index/error and full mutation frame; native K004 header,K005 fill step,K010 guards,K013 child ranges,K016 child error order'}
  r['model_status']='CLOSED-CONDITIONAL';r['native_status']='OPEN';r['new_evidence']=names[f]+'. NBN_U03.conditional/L077 bundles all four with exactly canonical DigestEncode + full DigestDecode. No other hypothesis. Native P6 promotion retains KDX lowered-copy/move fidelity exposure; no new fidelity assumption is adopted.'
 if u=='U04' and f in ['first_canonical_byte','pool_v1_pair_forest_output_lane_v1']:
  r['model_status']='CLOSED-CONDITIONAL';r['new_evidence']='NBN_U04.conditional_helpers/L092; full lower raw DigestEncode for unguarded first byte, canonical law derived for output lane (guard establishes its domain). Native K014/K015 scalar cuts. Native whole-member credit retains KDX exposure of lowered values; no lower codec pass is assumed.'
 elif u=='U04' and r['status']=='OPEN':
  if 'verifier_registry.rs' in r['id']:
   gap='Actual SDK retains adapter slots25–34; flags/active/decoded-record behavior and internal status/retirement/required-binding/reserved-scan composition must be associated on the SAME registry/entry. NBN_CallbackObstruction.registry_unconstrained/no_fixed_registry_law proves a fixed op25 law does not follow from selection alone.'
  elif f in ['decode_pool_identity_v1','decode_verifier_policy_v1','validate_verifier_policy_v1']:
   gap='Associate the exact parsed identity/policy Result to SAME enclosing master/policy input and op15; forwarding an arbitrary adapter policy callback does not establish native semantics.'
  else:
   gap='Full SAME master/checkpoint carrier, reserved scans,16-sequence induction, master/identity/policy validation and op48/49 association remain. NBN_AccountCallbackObstruction.master_unconstrained/checkpoint_unconstrained witnesses arbitrary SDK replies on identical bytes.'
  r['new_evidence']=gap+' This is an independent higher-unit interpretation gap, not an unmerged lower U00–02 theorem; the authorized conditional rule cannot assume it. All inherited native domains remain exact, with KDX exposure retained.'
 if u=='U05':
  if f=='validate_pool_v1_pair_forest_terminal_statement_v1':
   r['model_status']='CLOSED-CONDITIONAL';r['new_evidence']='NBN_ValidatorSummary.source/L081: full ordered Result, same variant payment, five exact bindings, same nullifier/lane and late calls; only canonical DigestEncode + TransferEncode + WithdrawalEncode. NBN_U05.conditional/L083 bundles parent; native K003 ordered control and inherited NBD projections. Native P6 OPEN pending KDX lowered-value exposure and complete same-reference source association.'
  elif f=='encode_pool_v1_pair_forest_terminal_statement_v1':
   r['model_status']='CLOSED-CONDITIONAL';r['new_evidence']='NBN_StatementEncoderSummary.source/L082 and NBN_U05.conditional/L083: only raw DigestEncode + TransferEncode + WithdrawalEncode; no caller/child-success premise. Same validator derives all reached child readiness; exact1880 bytes and full Result retained. NBN_EncoderObservation.faithful/width/L098 proves observation lossless. Installed op22 law NBN_InstalledEncoder.source/L053. Native K017 same refs/order/error cut, inherited NBH_K029 fixed prefix/NBK_K042 ranges. Native P6 OPEN due KDX lowered copy/move fidelity; no unapproved extra hypothesis.'
  elif f in ['nullifier','transition_kind'] and r['status']=='OPEN':
   r['model_status']='SAME-input call association proved';r['new_evidence']='NBN_U05.validator_nullifier/encoder_kind/L083, inherited NBD_TerminalProjection.source_parts/nullifier_same and NBD_K009 on both variants. SAME tuple component reaches validator; SAME variant chooses prefix kind. No separate adopted getter is invented. Native member promotion retains broader lowered-value association exposure.'
  elif f=='validate_result':
   r['model_status']='CLOSED-CONDITIONAL';r['new_evidence']='Optional: NBN_ResultValidator.source/L094 full emitted Result; NBN_ResultDependency.source/L096 only canonical DigestEncode, with U03 afterstate summary imported. Native K018 ordered checks, same nullifier/entire-afterstate references. Complete native/cohort result carrier/P6 fidelity remains OPEN; universal op53 does not need this for headline soundness.'
  elif f=='decode_pool_v1_pair_forest_terminal_request_v1':
   r['new_evidence']='Full same-variant TransferDecode/WithdrawalDecode plus exact ASQ8 public/request carrier and post-payment zero bindings remain; no earlier payment error may be skipped. Actual SDK op23 is forwarded and unconstrained: NBN_AccountCallbackObstruction.request_unconstrained/L076. Lower codec hypotheses alone cannot fix op23; no new dictionary adopted.'
  elif f in ['encode_pool_v1_pair_forest_terminal_result_v1','validate_pool_v1_pair_forest_terminal_result_against_statement_v1']:
   r['new_evidence']='Optional ASR8: result validator model now available (NBN_ResultValidator/source and NBN_ResultDependency/source);8 unchanged dependencies built once L084–091. Whole result encoder or statement-first/result-second enclosing validator with ENTIRE afterstate equality is still OPEN; source model/emitter association must be on SAME carriers, with exact bytes/error priority and KDX exposure. Not needed to narrow universal op53.'
 r['status']=r['native_status']
(E/'NBN_MEMBER_STATUS.json').write_text(json.dumps(rows,indent=2)+'\n')
for u in ['U03','U04','U05']:
 rs=[r for r in rows if r['unit']==u];closed=sum(r['native_status'].startswith('CLOSED') for r in rs);cond=sum(r['model_status']=='CLOSED-CONDITIONAL' for r in rs)
 text=f'# NBN {u}: native P6 OPEN\n\n{closed}/{len(rs)} inherited CLOSED labels; {len(rs)-closed} native members still OPEN. {cond} full source-model member laws are CLOSED-CONDITIONAL under named lower codec laws. These counts distinguish Lean source association from native bridge closure. No headline premise removed; deployed target not established. Inherited labels retain their exact original domains and the KDX exposure caveat.\n\n'
 text+='| Frozen member | Native status | New source-model status | Exact evidence / remaining obligation |\n|---|---|---|---|\n'
 for r in rs:text+='| `'+r['id']+'` | '+r['native_status']+' | '+r['model_status']+' | '+r['new_evidence'].replace('|','\\|')+' |\n'
 text+='\nOriginal per-member fragments and domains are retained verbatim in NBN_MEMBER_STATUS.json.inherited_evidence_or_open and the NBK unit tables. NBN_KDX_UPDATE.md records why an adequate-bound PASS does not by itself settle native P6 fidelity. No U04 adapter-law premise or replacement SDK is silently added.\n'
 (E/('NBN_'+u+'_BRIDGE.md')).write_text(text)
