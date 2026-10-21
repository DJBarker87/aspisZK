#!/usr/bin/env python3
"""Static frozen-layout audit. No Rust build or acceptance claim."""
import hashlib,json,pathlib,subprocess
root=pathlib.Path(__file__).resolve().parents[5]
ev=pathlib.Path(__file__).resolve().parent
rows=[];at=48
for row in range(27):
 tag,size=(1,32) if row==2 else (3,32) if row==14 else (2,896) if 15<=row<=24 else (4,3712) if row==25 else (5,928) if row==26 else (0,0)
 stored=size//2 if row>=14 else size
 rows.append(dict(row=row,stored_range=[at,at+5+stored],stored_payload=stored,logical_framed_bytes=5+size,encoding='tag:u8 + len:u32le + expanded payload',absorption='semantic absorb; row 0 follows public/root initialization'))
 at+=5+stored
assert at==7031
for row,lo,hi,n in [(27,7031,7495,928),(28,7495,7527,32),(29,7527,7751,224),(30,7751,8007,256),(31,8007,10055,2048),(32,10055,10055,0)]:
 rows.append(dict(row=row,stored_range=[lo,hi],logical_framed_bytes=4+n,encoding='len:u32le + payload (row 27 QM31 expanded)',absorption='late transcript absorb'))
slots=[];at=28359
for name,count in zip(['C1 A','C2 A','folded A','C1 B','C2 B','folded B'],[146,146,128,172,172,150]):
 slots.append(dict(name=name,range=[at,at+32*count],capacity=count));at+=32*count
assert at==57607
# Two well-framed canonical compact layouts differ only in the first C1 salt.
wire=bytearray(b'R1P3CB18'+bytes([2])+bytes(7)+bytes(32))
for r in rows[:27]:
 row=r['row'];tag,size=(1,32) if row==2 else (3,32) if row==14 else (2,896) if 15<=row<=24 else (4,3712) if row==25 else (5,928) if row==26 else (0,0)
 wire+=bytes([tag])+size.to_bytes(4,'little')+bytes(r['stored_payload'])
wire+=bytes(57607-len(wire));other=bytearray(wire);other[10055+608]=1
assert len(wire)==len(other)==57607 and wire[:10055]==other[:10055] and wire!=other
files=['crates/aspis-r1-cost-probe/src/compact.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-statement/examples/j1_terminal_codec_trace.rs','docs/research/100bit-spend-path-20261013/lean/OraclePortCompactDraft.lean']
result=dict(schema='oracle-port-layout-c4-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_pins={f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files},header=[0,16],c1_root=[16,48],rows=rows,openings=dict(range=[10055,28359],count=22,stride=832,fields=[['C1',0,480],['C2',480,608],['C1 salt',608,640],['C2 salt',640,672],['folded',672,800],['folded salt',800,832]]),slots=slots,proof_length=57607,row_capacity_ceiling=33*3717,logical_semantic_including_root=32+sum(r['logical_framed_bytes'] for r in rows[:27]),logical_row_framing_total=sum(r['logical_framed_bytes'] for r in rows),opening_node_bytes=57607-10055,fixture_sha256=[hashlib.sha256(x).hexdigest() for x in [wire,other]],fixture_kind='syntactically framed canonical zero fields; no acceptance asserted',codec_1233_scope='Pool live-snapshot, candidate-afterstate, late-statement encodings; not compact proof or opening coverage',hash_classes=dict(transcript='row absorb plus squeeze/advance',merkle='salted leaf and binary node inputs; do not advance transcript state',checkpoint='hashes complete stored proof, public and prepared checkpoint; includes slot padding'))
(ev/'OraclePortLayoutC4.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['proof_length','row_capacity_ceiling','logical_row_framing_total','opening_node_bytes','fixture_sha256']}))
