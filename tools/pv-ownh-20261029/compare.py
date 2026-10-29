"""Byte-for-byte comparison against the exact source literals of named laws."""
from pathlib import Path
import json,re,hashlib,struct
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownh-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
sha=lambda b:hashlib.sha256(b).hexdigest()
rowfile=L/'PV_RDB2D_PV_B3P_Sorted133.lean';maskfile=L/'PV_RDB2D_MaskChunk13.lean'
rowdef=re.search(r'^def expected : List Nat := (.+)$',rowfile.read_text(),re.M)[1]
assert re.fullmatch(r'[\d,\s\[\]()+]+',rowdef)
rows=[int(x) for x in re.findall(r'\d+',rowdef)];assert len(rows)==214
maskdef=re.search(r'^def after : Masks := (.+)$',maskfile.read_text(),re.M)[1]
assert re.fullmatch(r'[\d,#\s\[\]]+',maskdef)
masks=[int(x) for x in re.findall(r'(\d+)#16',maskdef)];assert len(masks)==64
# Cross-check the separate Aeneas U16 reference literal, rather than substituting
# a newly computed output for either proved literal.
rtyped=(L/'PV_RDB2D_PV_B3P_Law133.lean').read_text().split('theorem source')[0]
assert rows==[int(x) for x in re.findall(r'(\d+)#u16',rtyped)]
# Masks -> increasing rows. This independently checks the fold's indexing/bit
# interpretation and makes the crate rows fingerprint applicable to V230.
expanded=[16*i+b for i,w in enumerate(masks) for b in range(16) if w&(1<<b)]
assert expanded==rows
fnv=lambda payload:fold(payload)
def fold(payload):
 h=0xcbf29ce484222325
 for b in payload:h=((h^b)*0x100000001b3)&((1<<64)-1)
 return h
payload=lambda ws:b''.join(struct.pack('<H',w) for w in ws)
expected=lambda ws:b'\0'+struct.pack('<Q',len(ws))+payload(ws)
proof=json.loads((E/'lean-63853/receipt.json').read_text());assert proof['exit']==0
# Require the audited new Result theorem compilation, not just literal parsing.
assert 'v229_result' in (E/'lean-63853/output.log').read_text() and 'v230_result' in (E/'lean-63853/output.log').read_text()
native=json.loads((E/'native-result.json').read_text());runs=[]
for run,words in zip(native['runs'],[rows,masks],strict=True):
 assert run['exit']==0
 fields=dict(l.split('=',1) for l in run['stdout'].strip().splitlines())
 actual=bytes.fromhex(fields['result']);want=expected(words);assert actual==want,(run['mode'],actual.hex(),want.hex())
 assert fields['rows_fingerprint']==f'{fold(payload(rows)):016x}'
 assert fields['schedule_fingerprint']=='480809b836778dc6' # inherited original schedule cohort cross-check
 if run['mode']=='rows':assert fields['capacity']=='272'
 runs.append(dict(mode=run['mode'],equal=True,result_hex=want.hex(),result_bytes=len(want),result_sha256=sha(want),payload_sha256=sha(payload(words)),word_count=len(words),rows_fingerprint=fields['rows_fingerprint'],schedule_fingerprint=fields['schedule_fingerprint'],mask_expansion_matches_rows=True if run['mode']=='masks' else None))
out=dict(evidence_class='exhaustive over a singleton input domain, deployed-configuration harness',literal_sources=[dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes())) for p in [rowfile,maskfile,L/'PV_RDB2D_PV_B3P_Law133.lean']],named_laws=['R1Z.PV_OWNH_Literals.v229_result','R1Z.PV_OWNH_Literals.v229_selected_values','R1Z.PV_OWNH_Literals.v230_result'],binary=native['binary'],runs=runs,encoding='native exit0 represents outer semantic success; inner Rust Ok tag00, LE u64 length, then all LE u16 words; no padding or pointer bytes',schedule_crosscheck='crate fingerprint matches inherited original-root diagnostic; not a new Lean schedule-fingerprint theorem',compiler_boundary='V370/D381/D386 retained',rdea_1='retained')
(E/'byte-comparison.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(runs,indent=2))
