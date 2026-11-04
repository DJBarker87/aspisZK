"""Inspect pinned provider statements and retained audits; no Lean launches."""
from pathlib import Path
exec((Path(__file__).resolve().parent/'audit13.py').read_text().split('# Each historical')[0])
# Reuse the main audit manifest only once it has completed.
assert (P/'manifest.json').exists()
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
codec=txt('own2','lean/PV_OWN2_Codec.lean');fresh=txt('own2','lean/PV_OWN2_FreshAllocation.lean')
for word in ['FreshAllocationValidity','FreshSuccess','GrantedRegions','clone_disjoint']:assert word in fresh
assert 'valid : FreshAllocationValidity resources granted s' in fresh
assert 'Valid s v ∧' in codec and 'separate : Separate' in codec
rr=obj('own2','evidence/pv-own2-20261104/receipt-93690.json');out=txt('own2','evidence/pv-own2-20261104/out-93690.log')
raw=[json.loads(x[len('NEP_RESULT '):]) for x in out.splitlines() if x.startswith('NEP_RESULT ')]
assert len(raw)==35 and all(x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw)
rm=obj('own2','evidence/pv-own2-20261104/raw-audit/manifest.json')
walker=read('own2','lean/PV_OWN2_RawWalker.lean');authority=read('research','evidence/axaudit2-20261102/NEP_Driver.lean')
# Driver is parameterized; provider records walker identity against the exact authority.
assert rm['walker_byte_identical'] and hashlib.sha256(walker).hexdigest()==rm['walker_sha256']
assert rr['exit']=='0' and rr['admission']['allowed'] and rr['accepted']
owner_receipts=[]
for n in [93610,93611,93612,93690]:
 r=obj('own2',f'evidence/pv-own2-20261104/receipt-{n}.json');owner_receipts.append({k:v for k,v in r.items() if k!='admission'})
read('own2','evidence/pv-own2-20261104/replay-manifest.json')
read('own2','evidence/pv-own2-20261104/INTERFACES-D648.md')
# Before/after premise inventory, with no new counted row.
new_premise={'name':'PV_OWN2_FreshAllocation.FreshAllocationValidity','source_revision':revs['own2'],'path':'lean/PV_OWN2_FreshAllocation.lean','before':'Resources accepts arbitrary full replies; no named valid-fresh-allocation predicate relating answer regions to reached live OWNER ranges.','after':'NEW NAMED PREMISE FreshAllocationValidity resources granted s at reached OWNER pre-state s: each successful non-null positive-sized malloc/calloc/posixMemalign reply is in externally granted regions and range-disjoint from every nonempty positive-width Owned header.','not_proved':True,'classification':'rdea-1/V370 world-answer obligation below endpoint; not T','unrestricted':'null, zero-size, error, divergence, fault, pending; realloc is not fresh','consequences':'clone_disjoint and grant containment conditional on this premise and supplied resolved places; native source-place and layout associations remain open','endpoint_premises_removed_added_weakened':[0,0,0],'counted_rows_added':0}
# No new translator exists in the pinned stx deliverable.
stx=txt('stx','BLOCKER-STX19.md');read('stx','BLOCKER-STX18.md');read('stx','BLOCKER-SOURCE7.md')
coverage=obj('stx','evidence/pv-stx-20261104/D651/relaunch1/coverage-and-boundary.json')
assert 'No translator patch/build was attempted' in stx and coverage['parent_bindings_closed']==0
# Every currently credited source path is captured by closing_statement13.
rows=json.loads((P/'rows13.json').read_text()); credited=[x for x in rows if x['recount13_status'].startswith('CLOSED')]
scan=[]
for k in pins['revisions']:
 hits=git('grep','-n','-i','-E','patched translator|translator patch|stx-2',revs[k],'--','lean','evidence/pv-stx-20261104','design/PV-OWNER-PACKET-20261027.md') if k=='stx' else b''
 scan.append({'ref':k,'revision':revs[k],'scope':'stx status, Lean source and owner packet' if k=='stx' else 'credited row closing sources checked below','hit_count':len(hits.decode().splitlines()),'hits':[line[:700] for line in hits.decode().splitlines()[:25]], 'long_lines':'First25 excerpts, each at most700 chars; query reproducible from status13.py against the pinned Git tree.'})
closing_sources=[]
for r in credited:
 s=r.get('closing_statement13')
 if s:
  source=txt('rw',s['path']);assert 'PV_OWN2_' not in source and 'Instrumented' not in source
  closing_sources.append({'row':r['id'],'source':s,'new_translator_citation':False})
# Source-only graph imports cannot create credit. No patched objects are loaded here.
read('stxb','evidence/pv-stxb-20261104/HANDOFF-B.md')
# Find D649 final receipt and graph roots directly, not by LOG claim alone.
sb=obj('stxb','evidence/pv-stxb-20261104/receipt-92995.json')
sb_out=txt('stxb','evidence/pv-stxb-20261104/out-92995.log')
sb_raw=[json.loads(x[len('NEP_RESULT '):]) for x in sb_out.splitlines() if x.startswith('NEP_RESULT ')]
assert len(sb_raw)==46 and all(x['equal'] for x in sb_raw)
# D650 retained audit and local certificate inventory; no whole wrapper theorem.
bp='evidence/pv-b3p6-20261028/resume18/'
bh=txt('b3p6',bp+'HANDOFF.md');plan=obj('b3p6',bp+'PLAN-D650.json')
braw=obj('b3p6',bp+'lean-92898/receipt/receipt.json');bout=txt('b3p6',bp+'lean-92898/receipt/stdout.log')
assert '27' in bh and 'DeployedWrapper557' in bh
read('b3p6',bp+'verification-summary-D642.json');read('b3p6',bp+'NEP-PROVENANCE-D642.json')
read('b3p6',bp+'WRAPPER-APPS-D650.json') if bp+'WRAPPER-APPS-D650.json' in tree('b3p6') else None
# Exact current bounded support as recorded before the k4 suspension.
support=obj('research',str(B/'recount11/k3-row-support11.json')) if str(B/'recount11/k3-row-support11.json') in tree('research') else None
for p in tree('research'):
 if p.startswith(str(B.relative_to(Path.cwd()))+'/recount11/') and ('support' in p) and p.endswith('.json'):read('research',p)
changes=json.loads((P/'definition-audit13.json').read_text())
def_changes=collections.Counter((s['ref'],s['path']) for a in changes for s in a['changed'])
assert all(k=='own2' or p.endswith('/LOG.md') for k,p in def_changes)
dump('status-audit13.json',{'D653':{'new_named_premise':new_premise,'typed_memory':'PROVED interface on supplied places, partial fixed decoders for initialized byte images; raw representatives retained, no canonicality restriction. Physical Rust layout and original activation/place installation remain V370/native obligations. Closes no row.','raw_audit':{'target':rr['target'],'exit':rr['exit'],'wall':rr['wall'],'peak_rss_kib':rr['peak_rss_kib'],'swap':rr['swaps'],'source_revision':rr['source_revision'],'roots':len(raw),'zero_unresolved':True,'raw_results':raw,'provider_manifest':rm,'summary_based_axioms':rr['print_axioms_summary_based']},'focused_receipts':owner_receipts},'D651_D656':{'status':'PENDING authorized instrumented-machine route and minimal translator patch; stx-2(1) unmet; erasure, fuel and native places unproved.','unmodified_ae1_failure':coverage['failure'],'no_patched_translator_credit':True,'credit_source_checks':closing_sources,'scan':scan,'requirements':'Pinned hashed diff plus binary; option-off byte identity over complete existing extraction cohort; option-on explicit native instruction/local/call identity; modification to existing Aeneas tool trust and owner packet notice BEFORE adoption; no T, endpoint premise or frozen-source change.'},'D646_D649':{'status':'stx/stxb paused on place obstruction; stx reactivated only for D651 route. own2 paused pending places. No row change.','stxb_raw_roots':len(sb_raw),'stxb_receipt':{k:v for k,v in sb.items() if k!='admission'}},'D650':{'status':'27/217 local conditional caller certificates; original-entry/ops/opaque associations/DeployedWrapper557 OPEN. No row closure.','receipt':braw,'later_live_branch_plan':plan,'live_plan_status':'D650 follow-up work is not treated as extra row closure.'},'defining_source_differences':[{'ref':k,'path':p,'row_occurrences':n,'disposition':'Newly pinned own2 inherited cohort; contextual interface input only, never substitutes for candidate row authority.' if k=='own2' else 'LOG reporting change only.'} for (k,p),n in def_changes.items()],'execution':'Inspection only, Lean 0/40, Kani 0/0; no host scope, no repeated regression.'})
dump('manifest.json',list(manifest.values()))
print('PASS status/statement/retained raw audits; one NEW NAMED PREMISE below endpoint')
