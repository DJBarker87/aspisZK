from NGZ_ledger import J,put,closure,E
import collections
L=J('evidence/ledger9-20261105/NGZ_LEDGER.json');entry='programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction'
sinks={'TX1':'crates/aspis-r1-cost-probe/src/candidate.rs::tx1','TX2':'crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation'}
records={};lines=['# Shortest entry-to-accept dependency paths','','The NGB inventory is a call graph, not an execution CFG: these are shortest dependency paths to the TX1 checkpoint-producing candidate and TX2 acceptance-relation checker. They identify necessary OPEN driver rows; they do not assert that a single graph path contains every call of an accepting execution. All reached sibling callees and domains must also compose.','']
for tx,sink in sinks.items():
 rows=[r for r in L['rows'] if r['transaction']==tx];ix={r['function']:r for r in rows};g=collections.defaultdict(set,{f:{c for c in r['canonical_callees'] if c in ix} for f,r in ix.items()});paths=closure(g,[entry]);path=paths[sink];rr=[dict(row=ix[f]['row'],function=f,status=ix[f]['composed_status']) for f in path];records[tx]=dict(sink=sink,path=rr,OPEN_rows_in_order=[r['row'] for r in rr if r['status']=='OPEN'])
 lines += ['## '+tx,'','| Position | Row | Status | Function |','|---|---|---|---|']+['| '+str(i+1)+' | '+r['row']+' | '+r['status']+' | '+r['function']+' |' for i,r in enumerate(rr)]
 # Every OPEN descendant of path vertices is disclosed in stable path order.
 open_cone=[dict(row=r['row'],function=r['function']) for r in rows if r['function'] in paths and r['composed_status']=='OPEN'];records[tx]['all_reachable_OPEN']=open_cone
 lines+=['','OPEN rows on this shortest path, in order: '+', '.join(records[tx]['OPEN_rows_in_order'])+'.','']
put('NGZ_SHORTEST_PATHS.json',records);(E/'NGZ_SHORTEST_PATHS.md').write_text('\n'.join(lines).rstrip()+'\n')

old=J('evidence/ledger8-20261105/NGJ_SHORTEST_PATHS.json')
comparison={tx:dict(old_OPEN_rows=old[tx]['OPEN_rows_in_order'],new_OPEN_rows=records[tx]['OPEN_rows_in_order'],same_function_path=[x['function']for x in old[tx]['path']]==[x['function']for x in records[tx]['path']])for tx in records}
put('NGZ_PATH_COMPARISON.json',comparison)
with (E/'NGZ_SHORTEST_PATHS.md').open('a') as f:
 f.write('\nComparison with NGJ: '+str(comparison)+'\n')
