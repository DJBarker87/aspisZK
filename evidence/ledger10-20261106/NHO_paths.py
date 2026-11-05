from NHO_ledger import J,put,closure,E,R
import collections,re,hashlib,json
L=J('evidence/ledger10-20261106/NHO_LEDGER.json');entry='programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction';sinks={'TX1':'crates/aspis-r1-cost-probe/src/candidate.rs::tx1','TX2':'crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation'}
source=R/'evidence/slice-d-entry2-20261106/NHD_SPINE.md';owners={}
for line in source.read_text().splitlines():
 if re.match(r'\| TX[12]:',line):
  parts=[x.strip()for x in line.split('|')[1:-1]];owner,obligation=parts[3].split(': ',1);owners[parts[0]]=dict(owner=owner,obligation=obligation,source=str(source.relative_to(R)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
for rid in ['TX1:094','TX2:064','TX2:065']:
 owners[rid]['last_historical_owner']=owners[rid]['owner'];owners[rid]['owner']='NHL_ prepare/tx1 model lane; NFW_ retained native producer boundary'
 owners[rid]['latest_evidence']='NHO_READONLY_NHL_HANDOFF.md (pinned read-only branch); zero promotions, missing child native producer laws remain'
owners['TX2:115']['owner']='NHE_/NHI_ TX2 tail; parent finish_relation remains OPEN'
owners['TX2:115']['obligation']='NGW point/weight constructors, NHE polynomial/round/dot and NHI scalar_factor/tensor are CLOSED. Remaining pair TX2:129, filled/factored/grouped/process_kind/byte/high/shared/partial wrappers and SAME Prepared/view producer boundaries must compose, with full errors and frames.'
owners['TX2:115']['latest_evidence']='evidence/slice-d-pair-20261106/NHI_REMAINING.md; NHI_PAIR_CONE.md'
records={};lines=['# Recomputed shortest entry-to-accept dependency paths','','These are shortest dependency paths in the immutable599-row canonical call graph, not an execution CFG. TX1 sink is its checkpoint-producing candidate; TX2 sink is the acceptance-relation checker. All reached sibling callees and caller domains must also compose.','']
for tx,sink in sinks.items():
 rows=[r for r in L['rows']if r['transaction']==tx];ix={r['function']:r for r in rows};g=collections.defaultdict(set,{f:{c for c in r['canonical_callees']if c in ix}for f,r in ix.items()});paths=closure(g,[entry]);rr=[]
 for f in paths[sink]:
  r=ix[f];row=dict(row=r['row'],function=f,status=r['composed_status'])
  if r['composed_status']=='OPEN':assert r['row']in owners;row.update(owners[r['row']])
  rr.append(row)
 records[tx]=dict(sink=sink,path=rr,OPEN_rows_in_order=[r['row']for r in rr if r['status']=='OPEN'],all_reachable_OPEN=[dict(row=r['row'],function=r['function'])for r in rows if r['function']in paths and r['composed_status']=='OPEN'])
 lines+=['## '+tx,'','| Row | Status | Function | Owner and last recorded obligation |','|---|---|---|---|']+['| '+r['row']+' | '+r['status']+' | '+r['function']+' | '+r.get('owner','')+': '+r.get('obligation','')+' |'for r in rr]
 lines+=['','OPEN sequence: '+', '.join(records[tx]['OPEN_rows_in_order'])+'.','']
old=J('evidence/ledger9-20261105/NGZ_SHORTEST_PATHS.json');assert all([x['function']for x in old[t]['path']]==[x['function']for x in records[t]['path']]for t in records)
lines+=['## Adjacent blockers and provenance','','NHD_SPINE.md supersedes the NGL ownership report for entry/adapter rows. Ruling(ak) provides explicit-constructor logging stubs for non-Arbitrary Result interfaces; it supplies no callee packet by itself. NHF closes only wide_view TX1:095; prepare TX1:087 and Prepared::new TX1:179 remain OPEN. The pinned NHL branch snapshot provides model advances only, zero composed row promotions. TX1:137 verify_observed remains OPEN, despite the11 NGX leaf packets (two already CLOSED in NGZ).','','NHE/NHI replace obsolete scalar_factor/tensor blockers with their CLOSED packets; pair TX2:129 and finish_relation TX2:115 stay OPEN. Full remaining member table: NHI_PAIR_CONE.md. Pool production prefix/settlement ownership is NHC_, outside599; supported_loader is CLOSED while AccountInfo/decoder/marker/custody/registry/CPI/same-return association remains OPEN. NHC_POOL_B.md and NHC_REMAINING.md supersede the old NGG item10 conflict: canonical retarget is complete, production native associations remain.','','Every OPEN spine row above has an explicit owner and last recorded obligation. A currently running worker is not evidence of closure. No live sibling worktree was read or edited. See NHO_READONLY_PROVENANCE.json for immutable sibling revision.']
put('NHO_SHORTEST_PATHS.json',records);(E/'NHO_SHORTEST_PATHS.md').write_text('\n'.join(lines)+'\n');print({t:records[t]['OPEN_rows_in_order']for t in records})
