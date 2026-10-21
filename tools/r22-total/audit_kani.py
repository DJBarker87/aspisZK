#!/usr/bin/env python3
"""Summarize existing P6 receipts; never launch or re-run a Kani gate."""
import hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[2]
B=ROOT/'docs/research/100bit-spend-path-20261013'; OUT=B/'evidence/r22-total-20261021'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for d in sorted((B/'evidence/asq8-kani-20261021/receipts').glob('kani-relocation-*')):
 p=d/'receipt.json'; r=json.loads(p.read_text()); log=(d/'stdout.log').read_text()
 overflow=[l for l in log.splitlines() if re.search('overflow',l,re.I) and re.search(r': (?:SUCCESS|FAILURE)',l)]
 assert r['exit_status']==0
 assert not any(': FAILURE' in l for l in overflow)
 cmd=r['command']; assert '--no-overflow-checks' not in cmd
 rows.append({'cone':'ASQ8','harness':cmd[cmd.index('--harness')+1],
 'form':'OTHER: equality of full Results; accepted_request byte inverse is guarded by decoder success.',
 'R22':'Kani default Rust overflow assertions pass for every executed path in harness domain, including error paths.',
 'domain':'Arbitrary stored field words/bindings or arbitrary 320-byte requests; comparison slices length0..320.',
 'receipt':str(p.relative_to(ROOT)),'receipt_sha256':sha(p),'stdout_sha256':sha(d/'stdout.log'),
 'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],
 'command':cmd,'overflow_assertion_count':len(overflow),'overflow_assertion_examples':overflow[:3],
 'remaining':'P6 tool/compiler/reference/extraction identity; no complete verifier or account/caller claim.'})
p=ROOT/'docs/research/v8-r0-zk-20261009/r1p-final/builder-cont3-evidence/kani-and-extraction.json'
d=json.loads(p.read_text())
for name,r in d['kani'].items():
 if name not in ('raw_word_shipped_equals_reference','mat4_owned_equals_shipped','external_owned_call_trace_and_outputs') and name not in ('records_path_bit_indexed_reference','records_path_sibling_indexed_reference','records_scalars_indexed_reference','records_digest_cell_indexed_reference','records_public_frontier_indexed_reference','records_public_empty_indexed_reference'):continue
 assert r['exit_status']==0
 cmd=r['command'];assert '--no-overflow-checks' not in cmd
 rows.append({'cone':'D90 builder/Poseidon','harness':name,'form':'OTHER: shipped/reference equality, not Lean outer-ok totality.',
 'R22':'Default Rust overflow checks cover reached non-stubbed operations on harness domain.',
 'domain':'All u32 words; indexed observations assume only level/lane bounds. External layer quantifies over arbitrary shared mat4 output tables.',
 'receipt':str(p.relative_to(ROOT))+'#/kani/'+name,'receipt_sha256':sha(p),
 'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],
 'command':cmd,'remaining':('Compose exact mat4 leaf with equal ordered call inputs/counts; no hash abstraction beyond that callee.' if name=='external_owned_call_trace_and_outputs' else 'Retain raw-word/empty-root helper composition boundaries; whole caller admission not covered.')})
(OUT/'kani-audit.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows),'existing passing P6 harness receipts summarized; zero reruns')
