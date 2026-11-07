"""Carry the complete approved appendix verbatim as an indexed inventory."""
from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent;P=E.parent/'ledger24-20261110';p=Path('design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md');s=p.read_text();prior=json.loads(lzma.decompress((P/'NLX_LEDGER.json.xz').read_bytes()));ids={r['id']for r in prior['trust_rows']};rows=[];heading=''
for i,line in enumerate(s.splitlines(),1):
 if line.startswith('#'):heading=line
 if line.startswith('| ')and not line.startswith('|---'):
  cells=[v.strip()for v in line.strip('|').split('|')]
  if cells[0]in ['Exact projection (one row per field)','Surface']:continue
  rows.append(dict(line=i,section=heading,verbatim=line,classification='inventory only; original literal status retained, no new adoption',direct_closed_spend_rows=[],uses_note='Field detail of inherited aggregate trust/inventory. No new064 direct runtime/library implementation assumption; headline realization retains its exact binders.'))
sections=[]
for m in re.finditer(r'^### (\S+).*$',s,re.M):
 stop=s.find('\n### ',m.end());text=s[m.start():stop if stop!=-1 else len(s)];id=m.group(1)
 sections.append(dict(id=id,line=s[:m.start()].count('\n')+1,verbatim=text,direct_closed_rows=[],closed_pool_packet_context={'ReviewedTranscription-POOL324':['POOL:324'],'ReviewedTranscription-POOL345':['POOL:345'],'ReviewedTranscription-POOL296':['POOL:296'],'ReviewedTranscription-POOL320':['POOL:320'],'ReviewedTranscription-POOL223':['POOL:223'],'ReviewedTranscription-POOL332':['POOL:332']}.get(id,[]),spend_spine_uses=[],already_carried_in_ledger24=id in ids,classification='Carry read-only lead item; option-A RECLASSIFICATION for ReviewedTranscription, never removal'))
additions=[]
for r in sections:
 if r['id']not in ids:additions.append(dict(id=r['id'],scope=r['verbatim'],status='ADDED-LEAD-20261110; carried read-only',classification='RECLASSIFICATION of P6/D188 option A',direct_closed_rows=[],pool_closed_packet_context=r['closed_pool_packet_context'],evidence=[str(p)]))
# The literal Pool-entry seven-field admission was not an aggregate row in ledger24.
if 'RuntimeEntrypointAdmission-Pool'not in ids:
 additions.append(dict(id='RuntimeEntrypointAdmission-Pool',status='ADDED-LEAD-20261107; carried read-only',classification='Existing runtime-entry admission indexed, not newly adopted',scope='Same initial seven admission fields at Pool program entrypoint only; no CPI frame, callee semantics or success.',direct_closed_rows=[],pool_closed_rows=[],evidence=[str(p)],ruling='ap'))
out=dict(source=str(p),sha256=hashlib.sha256(s.encode()).hexdigest(),prior_aggregate_ids=sorted(ids),literal_table_rows=rows,dated_sections=sections,aggregate_additions=additions,aggregate_removals=[],runtime_or_crypto_trust_changed=False,native_transport_064=dict(item='NativeContractSemanticTransport',classification='existing P6/D188 option-A reclassification',new_closed_rows_if_gate_passes=['TX2:064']),context=dict(lead_rulings=['bh','bi','bj','bk','bl'],stream_c_rulings=['c-a','c-b','c-c','c-d','c-e','c-f','c-g','c-h','c-h amendment bl'],read_only=True),no_inference='Pending/unrecorded/historical rows retain those statuses. No imported unreachable external axiom is newly admitted; raw ax2 enforces standard axioms only on required roots.')
(E/'NMQ_TRUST_INVENTORY.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(table_rows=len(rows),sections=len(sections),aggregate_additions=[r['id']for r in additions],spend_spine_new_pool_uses=0)))
