"""Credit only an exact focused, source-bound, coherent existing row instance."""
from pathlib import Path
import json,hashlib,sys,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101';row=sys.argv[1];assert row in ['V233','V236']
coh=json.load(open(E/'coherence-result.json'));cr=json.load(open(E/'final-coherence/receipt.json'));assert cr['exit']==0 and coh['external_count']==5673
required={'V233':['BlockCarrier','V233'],'V236':['BufferSource','UpdateSplit','V236']}[row]
passed={}
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.load(open(p))
 if j['exit']==0:passed[j['module']]=dict(j,receipt=str(p.relative_to(E)))
for name in required:
 m='R1Z/PV_RDCD5_'+name;j=passed[m];p=R/j['source_path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==j['source_sha256']==coh['modules'][m]['source_sha256']
 assert all('sorryAx' not in x for x in j['axioms'])
rows=json.load(open(E/'ROWS.json'))
if row=='V236':assert rows['V233']['status']=='RESTORED'
if row=='V233':
 theorem='R1Z.PV_RDCD5_V233.consumed_instance';before='For every original valid byte slice and native Eager64 GenericArray family, the concrete source split has the existing SplitSelected.consumed typed carrier and complete Result.'
 after='Same base/ops/input slice quantifiers and complete typed Result; arbitrary logical origin retained. Typed encode/flatten inverse, wrapper roundtrip and projection injectivity distinguish exact GenericArray storage trees. Source pointer/base/count/tail geometry and aliases preserved. Native layout/codegen remains V370/D381/D386.'
 evidence='v233-source-bindings.json';support=['PV_RDCD5_BlockCarrier.encode_flatten','PV_RDCD5_BlockCarrier.flatten_injective','PV_RDCD5_V233.typed_roundtrip','PV_RDCD5_V233.typed_projection_injective','PV_RDCD5_V233.source_reference','PV_RDCD5_V233.aliases','PV_RDCD5_V233.valid_tail']
else:
 theorem='R1Z.PV_RDCD5_V236.op216_instance';before='For the original safe Eager64 private-buffer domain (64 bytes, pos<64), concrete BlockBuffer branches/cursor/ordered callbacks have the existing UpdateCarrier/UpdateSelected.selected_native complete Result.'
 after='Same typed core/update callback, arbitrary valid input Slice and pos<64 guard; typed storage has length64 by construction. Short, first-block, bulk, suffix, dead-buffer bytes, cursor truncation, error/divergence and callback order retained. Exact UpdateSplit.typed_batches/compression_instance associates callback arguments with V233 typed split; no singleton-fold or extra callback premise.'
 evidence='v236-source-bindings.json';support=['PV_RDCD5_BufferSource.cursor_transport','PV_RDCD5_BufferSource.finish_binding','PV_RDCD5_BufferSource.source_instance','PV_RDCD5_UpdateSplit.storage_encoding','PV_RDCD5_UpdateSplit.typed_batches','PV_RDCD5_UpdateSplit.compression_instance','PV_RDCD5_V236.carrier_instance']
bind=json.load(open(E/evidence));j=passed['R1Z/PV_RDCD5_'+row]
a=dict(row=row,status='RESTORED',theorem=theorem,support=support,before=before,after=after,source_bindings=evidence,focused_receipt=j['receipt'],coherence='coherence-result.json',coherence_receipt='final-coherence/receipt.json',route='own-1/k-prime structural argument at existing source/compiler boundary; complete kernel-checked Result and typed association; historical native differential retained as finite validation only',endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[],retained=['V370/D381/D386','E1/E2','native RunJoin/world/physical observer','client route','L1/L2/L3','T exactly entropy_law/entropy_kernel/observation'],fmt='No Aeneas.Std fmt credit. Original guarded domains exclude credited diagnostic/UB branches; physical observer remains unproved.',kani='No Kani runs or re-credit; historical suspended credits are not used.',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip())
(E/(row+'-ASSOCIATION.json')).write_text(json.dumps(a,indent=2)+'\n');rows[row].update(status='RESTORED',blocker=None,existing_instance=theorem,association=row+'-ASSOCIATION.json');(E/'ROWS.json').write_text(json.dumps(rows,indent=2)+'\n')
print(row,'RESTORED at existing qualified source/typed Result link; no endpoint premise removed')
