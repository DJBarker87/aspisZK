"""Check native request windows and source-exact child-call substitution."""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent
rows=[]
ids=[58,59,70,71,72,73,74,75,76,77,78,79,80]
path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
a=src.index('pub fn encode_pool_v1_pair_forest_terminal_request_v1(');z=src.index('\n}',a)+2;original=src[a:z]
expected=original[original.index('{\n')+2:original.rindex('}')]
for k,v in json.loads((E/'NFV_REFERENCE_INPUTS.json').read_text())['offsets'].items():expected=expected.replace(k,str(v))
expected=expected.replace('encode_pool_v1_private_transfer_public_v1(&public)','transfer(&public)').replace('encode_pool_v1_withdrawal_public_v1(&public)','withdrawal(&public)')
for n in ids:
 a=f'NFV_K{n:03}';r=json.loads((E/a/'receipt.json').read_text());s=json.loads((E/(a+'-shape.json')).read_text());out=(E/a/'stdout.log').read_text();positive=n in [58,70,72,74,76]
 assert r['exit_status']==int(not positive),a
 assert 'timed out' not in out.lower() and 'unwinding assertion' not in out,a
 if not positive:assert 'assertion failed:' in out,a
 if positive:
  native=s['source'].split('where T:FnOnce',1)[1].split('>{\n',1)[1].split('}\n#[kani::proof]',1)[0]
  assert native==expected,(a,'not source-exact')
 graph=json.loads((E/(a+'-graph-check.json')).read_text());assert graph['graph_matches_frozen'] and graph['exact_LPm_graph']
 rows.append(dict(attempt=a,mode=s['mode'],window=s['window'],range=s['range'],exit=r['exit_status'],wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=r['swaps'],receipt_sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest()))
(E/'NFV_REQUEST_WINDOWS.json').write_text(json.dumps(dict(status='controlled request-encoder native source-cut; outer production prefix OPEN',source_exact_positives=5,source=path,frozen_function_sha256=hashlib.sha256(original.encode()).hexdigest(),full_typed_child_results=True,all_errors_retained=True,modifies='none; pure encoder children, local call counters only',model=['NFV_Envelope.emitted','NFV_RequestWindows.envelope','NFV_RequestIndexes.header/profile/release/program/payment','NFV_RequestOracle.erase','NFV_RequestGuards.zero_binding'],open='SAME production decoded request/public and both payment-child PacketDomains must be derived from admitted account/data context. No complete process-prefix or composed NDT row follows from this source cut.',rows=rows),indent=1)+'\n')
print('Request source cuts checked; production prefix remains OPEN')
