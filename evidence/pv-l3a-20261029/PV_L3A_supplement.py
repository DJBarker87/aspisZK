from pathlib import Path
import json,lzma,re,collections
D=Path(__file__).resolve().parent
s=lzma.open(D/'disassembly.txt.xz','rt').read()
lines=[]
for line in s.splitlines():
 m=re.match(r'\s*([0-9a-f]+):\s+(\S+)\s*(.*)',line)
 if m and 0x96520<=int(m[1],16)<=0x96606:lines.append(dict(address=hex(int(m[1],16)),op=m[2],args=m[3],instruction=line.strip()))
branches=[i for i in lines if i['op'].startswith('j')]
assert len(branches)==1 and branches[0]['address']=='0x96606' and branches[0]['op']=='jne'
assert lines[-2]['address']=='0x96603' and lines[-2]['op']=='cmp' and lines[-2]['args'].split('<')[0].strip()=='%rcx,%r9'
assert not [i for i in lines if i['op'] in ['call','div','idiv']]
(D/'pole-loop-review.json').write_text(json.dumps(dict(range=['0x96520','0x9660c'],containing_function=['0x96060','0x9682e'],instructions=lines,classification='CLEAN for this candidate slice under the stated public shape/address inputs; source attribution and complete inline inventory UNRESOLVED',method='Manual dataflow review plus exact branch/call/division checks on the saved binary disassembly',secrets='chi lanes xmm0..3 and four QM31 values read through rdx; equality accumulator al',public_inputs='rdx values pointer; rcx row; r9 values.len; masks and stack addresses; invariant input to this slice, not proved for every predecessor',reasoning=['All witness reads are fixed offsets 0,16,32,48 from rdx. rdx advances by 64 per row.','Mask address uses row>>4; mask bit uses row&15. No witness-derived address.','pcmpeqd/por/movmskps/cmp/sete/and reduce four comparisons into al. No al-derived branch in the slice.','The sole conditional transfer at 0x96606 reads flags from public cmp rcx,r9 at 0x96603; rcx increments by 1.','Final verdict is subsequently used by the retry/error control path; this slice does not discharge its joint bad-event law.'],source_candidate='crates/aspis-r1-cost-probe/src/ct_pole.rs:18 all_slots_clear, inlined via host_semantic.rs:361 no_pole',source_from_debug=None,latency='V371 retained; DOITM pending; this is not a hardware timing proof'),indent=2)+'\n')
func={r['address']:r for r in json.load(lzma.open(D/'function-index.json.xz'))}
rows=json.loads((D/'instances.json').read_text());calls=[]
for r in rows:
 for c in r['call_sites']:
  f=func[c['caller']]
  calls.append(dict(**c,caller_names=f['names'],caller_end=f['end'],target_names=r['names'],target_end=r['end'],source_from_debug=None,classification='UNRESOLVED at composed witness/public argument provenance boundary'))
(D/'kernel-call-sites.json').write_text(json.dumps(calls,indent=2)+'\n')
# Include the complete inverse callers, not only selected kernel bodies.
a={c['caller'] for r in json.loads((D/'inversions.json').read_text()) for c in r['transfers']}
blocks=re.split(r'(?=^[0-9a-f]+ <)',s,flags=re.M)
(D/'inversion-caller-disassembly.txt').write_text('\n'.join(b for b in blocks if any(b.startswith(f'{int(x,16):016x} <') for x in a)))
print(dict(pole_instructions=len(lines),kernel_call_sites=len(calls),inversion_caller_bodies=len(a)))
