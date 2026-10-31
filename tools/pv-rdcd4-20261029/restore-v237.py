"""V237 closure: unchanged constructor binding plus input-free byte default."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
receipts={}
for p in E.glob('lean-*/receipt.json'):
 x=json.load(open(p))
 if x['exit']==0:receipts[x['module']]=dict(x,receipt=str(p.relative_to(E)))
root=receipts['R1Z/PV_RDCD4_V237'];assert all('sorryAx' not in a for a in root['axioms'])
for m in ['R1Z/PV_DL_DefaultNative','R1Z/PV_AL_SplitNativeShape','R1Z/ProverRwFullFuns']:
 assert m in receipts,m
single=json.load(open(E/'v237-singleton/receipt.json'));assert single['exit']==0
actual=json.load(open(E/'v237-singleton-result.json'));assert actual['result']=='PASS' and actual['literal_hex']=='00'*64
assert actual['classification']=='exhaustive over a singleton input domain, deployed-configuration harness'
cone=json.load(open(E/'v237-influence-census.json'));assert not cone['disqualifying_channels'] and len(cone['records'])==45
h6=json.load(open(E/'h6-v237/receipt.json'));assert h6['exit']==0
reuse=json.load(open(E/'reused-projects.json'));assert len(reuse['modules'])>=10
cohReceipt=json.load(open(E/'v237-coherence/receipt.json'));assert cohReceipt['exit']==0
coh=json.load(open(E/'v237-coherence-result.json'));assert coh['external_count']==5673 and len(coh['h6_reuse_checks'])>=10
assert 'R1Z/PV_RDCD4_V237' in coh['modules']
gates=json.load(open(R/'evidence/pv-rdcd-20261028/original-gates-recovered/results.json'))
gate=next(x for x in gates['results'] if 'V237' in x['rows']);assert gate['result']=='PASS'
old=json.loads(gates['outputs']['evidence/pv-dlib-20261028/V237/structural-binding.json'])
dep={(x['crate']+'/src/'+x['relative']):x for x in json.load(open(E/'buffer-dependency-sources.json'))}
for key,pin in old['sources'].items():assert dep[key]['sha256']==pin['sha256'],key
helper=old['owned_reference'];b=subprocess.check_output(['git','show','HEAD:'+helper['path']],cwd=R);assert hashlib.sha256(b).hexdigest()==helper['sha256']
association=dict(row='V237',theorem='R1Z.PV_RDCD4_V237.complete',literal_theorems=['R1Z.PV_RDCD4_V237.buffer_literal','R1Z.PV_RDCD4_V237.result_literal'],consumed_callback='R1Z.PV_DL_DefaultNative.consumed',original_gate=gate,unchanged_constructor_binding=old,influence='v237-influence-census.json',singleton='v237-singleton-result.json',coherence='v237-coherence-result.json',evidence_classes=dict(wrapper_and_BlockBuffer='structural (K-1 substitute); reclassification within existing Rust/Aeneas/compiler trust',byte_array_only=actual['classification']),before='Complete deployed CoreWrapper Default source-to-reference Result law at original Core::default boundary was unbound because concrete byte default was not closed.',after='Same generic Core result and moved-core owned reference, including failure/divergence. Fixed64-byte default equals literal zeros, position0. No arbitrary byte/default/library callback is introduced.',endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[],retained=['V370/D381/D386, including harness-to-shipped codegen','E1/E2','native RunJoin/world/physical observer','client route','L1/L2/L3','T exactly entropy_law/entropy_kernel/observation'])
(E/'v237-proof-association.json').write_text(json.dumps(association,indent=2)+'\n')
x=json.load(open(E/'rows/V237.json'));x.update(status='RESTORED',rdcd4_status='RESTORED at original source/Result boundary',**{'class':'B'},source_classification_complete=True,concrete_native_cone_complete_at_stated_primitive_boundary=True,native_link_evidence_class='structural constructor binding plus exhaustive singleton byte-default harness',kernel_theorem=association['theorem'],source_revision=root['source_revision'],coherence_revision=cohReceipt['source_revision'],reason=association['after'],source_association='v237-proof-association.json',next_deliverable='Final combined statement/axioms audit, focused restored-row replay and one frozen manifest.')
(E/'rows/V237.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'rows/V237.md').write_text(f'''# V237 — RESTORED / B

`R1Z.PV_RDCD4_V237.complete` preserves the original full Core::default Result,
including failures and divergence, against the original moved-core owned reference.
`PV_DL_DefaultNative.consumed` supplies the actual generated callback/trait consumer.

The recovered original constructor checker is reused at unchanged source hashes.
The byte-array subcall is closed under own-2 triple-prime: **{actual['classification']}**.
[The45-node influence census](../v237-influence-census.json) closes outside-input,
address and allocator-write channels. Memory primitives remain V370; no allocator
is called by this helper. No Core::default input-free claim is made.
The exact64-byte zero comparison passes in the optimized, deployed configuration;
[its artifact](../v237-singleton-result.json) records the binary hash, and
[inputs](../v237-singleton-inputs.json) record toolchain, complete features and lockfile.

[Kernel receipt](../{root['receipt']}): exit0, wall{root['wall']},
peak{root['peak_rss_kib']}KiB, swap{root['swap']}; standard axioms only.
[Singleton scope](../v237-singleton/receipt.json): exit0, wall{single['wall']},
peak{single['peak_rss_kib']}KiB, swap{single['swap']}.
[Coherent closure](../v237-coherence/receipt.json): exit0, wall{cohReceipt['wall']},
peak{cohReceipt['peak_rss_kib']}KiB, swap{cohReceipt['swap']}; all5673 external hashes,
fresh launch snapshots and h6 source/object/import fingerprints pass.

Before/after is the same source-to-reference Result statement. Core remains its
original complete-Result parameter; no extra arbitrary library callback is added.
No endpoint premise is removed, added or changed. V370/D381/D386, E1/E2,
native RunJoin/world/observer, client route, L1/L2/L3 and T remain. Final audit/replay pending.
''')
print('V237 RESTORED / B; own-2 credit confined to fixed byte-array default.')
