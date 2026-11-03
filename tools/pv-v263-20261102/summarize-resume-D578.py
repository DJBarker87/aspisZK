"""Record this continuation, keeping the original-block and new-block budgets distinct."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102'
read=lambda p:json.loads(p.read_text())
receipts=[read(p) for p in sorted(E.glob('receipt-*.json'))]
current=[r for r in receipts if 79963<=r['attempt']<=79974]
assert len(current)==12 and sum(r['accepted'] for r in current)==7
native=[read(p) for p in sorted(E.glob('N*-receipt.json'))]
assert len(native)==6 and read(E/'N90125-receipt.json')['accepted']
records=[v for p in sorted(E.glob('modules-*.json')) for v in read(p)]
new=[v for v in records if v['source_revision'] in {r['source_revision'] for r in current} and v['module'].split('.')[-1] in ['PV_V263_'+x for x in ['RawGrowth','GrowingPush','GrowingFacts','GrowthSchedule','OwnedForks','OwnedIterator','LayoutBounds']]]
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
log=subprocess.check_output(['git','log','--oneline','6ee81e0f24..HEAD'],text=True)
(E/'COMMITS-resume-D578.txt').write_text(log)
sources={}
for v in new:
 if v['accepted']:
  sources[v['module']]=dict(source_revision=v['source_revision'],source_sha256=v['source_sha256'],
   object_sha256=v['object_sha256'],axioms=v['axioms'],axiom_audit_kind='SUMMARY-BASED only')
assert len(sources)==7
out=dict(source_revision=revision,entry_revision='6ee81e0f24',branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),
 accepted_sources=sources,
 continuation=dict(charged_lean=12,accepted=7,rejected=5,ids=list(range(79963,79975)),
   wall_seconds=round(sum(r['host_wall_seconds'] for r in current),2),peak_rss_bytes=max(r['peak_rss_bytes'] for r in current),swaps=sum(r['swaps'] for r in current),native_ids=['N90125'],kani=0),
 cumulative=dict(charged_lean=len(receipts),accepted=sum(r['accepted'] for r in receipts),rejected=sum(not r['accepted'] for r in receipts),
   wall_seconds=round(sum(r['host_wall_seconds'] for r in receipts),2),peak_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=sum(r['swaps'] for r in receipts),native_charged=len(native)),
 budget=dict(original_block_charged=75,original_block_normal_remaining=22,next_lean_id=79975,
   original_unused_audits=[79997,79998,79999],new_normal_range=[91300,91396],new_normal_charged=0,new_normal_remaining=97,
   new_unused_audits=[91397,91398,91399],normal_remaining_total=119,native_remaining=14,next_native='N90126',kani=0,
   note='SUMMARY.json remaining_budget=22 refers to the ORIGINAL 97-attempt block. New 913xx block is authorized by resume prompt and entirely unused. Before first 913xx launch extend only own accepted ID-range/budget checks and record diff; perform normal cross-job ID scan. No runner range changed in this continuation.'),
 before_after=dict(V263=['OPEN','OPEN'],actual_op257=['residual','residual'],actual_reached_success=['unproved','unproved'],Nonempty_P=['unproved','unproved'],rows_removed=[],endpoint_premises_removed=[],endpoint_premises_added=[],trust_items_added=[],links_changed=[]),
 source_bindings=['growth-source-binding-continuation.json','iterator-source-binding-continuation.json'],
 source_binding_complete=False,actual_op257_installed=False,actual_reached_success=False,
 skeleton_consistency='reduced to non-emptiness',V183='SUSPENDED(K-3)',
 native_credit='N90125 finite std Vec growth validation only; representative payloads and changed-policy failing control, not actual encoder/oracle or full-crate build',
 failed_source_guard_sha256=hashlib.sha256((R/'tools/pv-v263-20261102/compile.py').read_bytes()).hexdigest(),
 raw_NEPor_coherence_audit=False,full_frozen_replay=False,
 stopping_reason='incomplete context checkpoint under explicit resume instruction; not completion, budget exhaustion, or impossibility')
(E/'continuation-summary-resume-D578.json').write_text(json.dumps(out,indent=2)+'\n')
print('Continuation 12 Lean:7 accepted/5 rejected; original22+new97 normal left; next79975; native14 left,nextN90126; no endpoint removal')
