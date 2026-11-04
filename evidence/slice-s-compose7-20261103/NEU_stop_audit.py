"""Member-by-member stop audit, grounded in imported reasons and this job's receipts."""
from pathlib import Path
import json,datetime,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
old=json.loads((E.parent/'slice-s-compose6-20261102/NEQ_REMAINING_OBLIGATIONS.json').read_text());summary=json.loads((E/'NEU_DECODER_VALIDATION.json').read_text());openrows=json.loads((E/'NEU_OPEN_MEMBERS.json').read_text());prior={m['function']:m for m in old['members']}
updates={
 'asq8_common':('Need a complete native same-input/Box field and physical-frame certificate. K118/K119/K120 have no verdict and are excluded; L015 proves full arbitrary-index assembly but cannot identify native output.', ['NEU_K118','NEU_K119','NEU_L015']),
 'reconstruct_asq8_statement':('Both constructor children are now composed. L010/L011 prove the full raw/adopted result/state/ordered trace and L012 discharges reached arguments/carriers/ranges. Native common,64-bit guard and finish associations remain OPEN: K120/K126 outer timeouts and K121 solver timeout are excluded; scalar read-set projection is not full native input association.', ['NEU_L010','NEU_L011','NEU_L012','NEU_K120','NEU_K121','NEU_K126']),
 'scan_proof_buffer':('Actual root calls only afterstate decoder/encoder and Variant::S2.tag, not SHA. Need SAME688-byte header, full child Result/Box frame, exact tag byte696 and the frozen library/compiler equality-to-iteration association. L020 and K127/128 cover symbolic induction and one arbitrary equality step only; no whole-buffer bridge.', ['NEU_L020','NEU_K127','NEU_K128']),
 'emit_result':('Need actual binding validator and792-byte result encoder leaf bridges at derived s, native guard/parent join and an approved coherent effect carrier for the real ordered set_return_data event. L004 retains BindingBridge and EncoderBridge EXPLICITLY; L006 proves the event frame cannot be empty. op53 Unit cannot erase it. K003/004 and K009/010 are supporting cuts only.', ['NEU_L004','NEU_L006','NEU_K003','NEU_K004','NEU_K009','NEU_K010']),
 'decode_pool_v1_pair_forest_terminal_request_v1':('Need full320-byte request return/ordered parent composition, actual slice-versus-array magic comparison, payment child/domain join and three zero-binding comparisons. K011..022 prove only the scalar/copy/suffix cuts with relevant comparison replies EXPLICIT arbitrary leaves. Existing NED range/NEQ payment laws are reused; no corrected full extracted reference/native join is established.', ['NEU_K011','NEU_K012','NEU_K013','NEU_K014','NEU_K015','NEU_K016','NEU_K017','NEU_K018','NEU_K019','NEU_K020','NEU_K021','NEU_K022']),
 'decode_pool_v1_pair_forest_terminal_statement_v1':('Both boxed payment helper branches now compose on the caller-established216-byte domain. Need actual1880-byte parent control, same native field/range reads, terminal-common and late-transition Box children and complete Result/state/frame association. The parent must establish the new helpers\'216-byte domain at its own native call sites; model geometry is not that native witness.', ['NEU_L017','NEU_L018','NEU_K122','NEU_K123','NEU_K124','NEU_K125']),
}
members=[]
for m in openrows:
 p=dict(prior[m['function']]);short=m['function'].rsplit('::',1)[-1]
 p['current_open_edges']=len(m['open_internal_edges']);p['retained_inner_names']=m['baseline_inner_names'];p['rows']=m['rows'];p['composed_status']='OPEN'
 if short in updates:p['exact_remaining_obligation'],p['current_receipts']=updates[short]
 else:p['current_receipts']=[]
 p['lean_only_obligation_remaining']=False
 p['why_more_Lean_alone_is_insufficient']='Existing emitted/model/domain/induction/carrier facts are reused read-only; the exact remaining obligation is an actual native carrier/call/Result/frame association, an OPEN native child, or owner resolution of the effect interface. Another model equality cannot supply that native witness. No outstanding independent pure Lean fact has been identified by this audit.'
 members.append(p)
rootresults=[]
base=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text());closed=set(summary['slice_closed'])
for p in old['roots']:
 p=dict(p);f=p['function'];rr=[r for r in base['rows'] if r['function']==f];p['closed_rows']=sum(r['row'] in closed for r in rr);p['total_rows']=len(rr)
 if f.rsplit('::',1)[-1] in updates:p['exact_remaining_obligation']=updates[f.rsplit('::',1)[-1]][0]
 if f.endswith('reconstruct_asq8_statement'):p['model_theorem']='NEU_ReconstructAdopted.result_state_effects (model only; native bridge OPEN)'
 if f.endswith('emit_result'):p['model_theorem']='NEU_EmitModel.result_state_effects (BindingBridge and EncoderBridge EXPLICIT; native/effect bridge OPEN)'
 rootresults.append(p)
L=list(E.glob('NEU_L*/receipt.json'));K=list(E.glob('NEU_K*/receipt.json'))
out=dict(slice='S',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_revision=base['frozen_revision'],baseline_composed_rows=68,composed_rows_closed=72,additional_rows=4,functions_closed=41,roots_closed=2,root_results=rootresults,budget=dict(kani_limit=130,kani_used=len(K),kani_remaining=130-len(K),lean_limit=80,lean_used=len(L),lean_remaining=80-len(L)),members=members,target_complete=False,target_established=False,unproved_root_theorems_claimed=False,trust='approved NDT rows and RuntimePersistence unchanged; P6/D188 option A is reclassification, never removal',stop_reason='Native budget exhausted; all20 remaining members need the exact native/effect/child witnesses listed; independent Lean assembly/model obligations completed and audited. No root bridge is assumed to manufacture closure.')
(E/'NEU_STOP_AUDIT.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(budget=out['budget'],open_members=len(members),target_complete=False)))
