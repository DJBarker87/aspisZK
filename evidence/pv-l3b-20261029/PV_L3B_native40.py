from pathlib import Path
import json,lzma,re,hashlib,collections
D=Path(__file__).resolve().parent
def read(name):
 p=D/name
 return json.loads(p.read_text() if p.exists() else lzma.open(str(p)+'.xz','rt').read())
def stack(n,addr):
 p=D/f'native{n:02}-debug-lines.txt'
 s=p.read_text() if p.exists() else lzma.open(str(p)+'.xz','rt').read()
 b=re.split(r'(?m)^(0x[0-9a-f]+)\n',s)
 for i in range(1,len(b),2):
  if int(b[i],16)==int(addr,16):return b[i+1].strip().splitlines()
 raise ValueError((n,addr))
proofs=[
 ('PV_Inv_InterpolationSource.source_inverse_operand','Bind the deployed bounded interpolation initializer to its owned extraction; i<28, canonical inputs. No probabilistic event needed.'),
 ('PV_Inv_Pivot.selected_nonzero / selected_inverse','Bind find(nonzero), swap(c,p), and a[c][c] to the selected pivot; prove canonical matrix invariant. The generic find theorem is not this native binding. Retain complete F6 joint challenge history.'),
 ('PV_Inv_Pivot.selected_nonzero / PV_Inv_Guard.nonzero_branch','Bind the v[i]==0 continue guard to the loaded pivot across row updates and retain canonicality. Retain F6 joint history.'),
 ('PV_Inv_Guard.nonzero_branch','Immediate 4 in edi; no witness-dependent zero at this call. Compiler preservation retained.'),
 ('PV_Inv_Guard.nonzero_branch','Immediate 2 in edi; no witness-dependent zero at this call. Compiler preservation retained.'),
 ('PV_Inv_Guard.nonzero_branch','Immediate 2 in edi in normalize_d; no witness-dependent zero at this call.'),
 ('PV_Inv_Guard.nonzero_branch','Immediate 2 in edi; no witness-dependent zero at this call.'),
 ('PV_Inv_Guard.nonzero_branch','Immediate 4 in edi in design_relations; no witness-dependent zero at this call.'),
 ('PV_Inv_Sentinel.nonzero_success / zero_reject','The machine guard test edi,edi; je 0x175fa4 precedes the inverse with no edi write. Bind native constructor to the reference. Prove joint retry/rejection law for zero sentinel; guarded inversion alone does not cover that earlier observable prefix.'),
 ('PV_Inv_NativeNormQ.norm_operand + PV_Inv_NativeNormC.norm_operand','Transport canonical nonzero QM31 input through both actual norm computations to the M31 operand; caller binding and same-run canonicality are required.'),
 ('PV_Inv_Guard.difference / nonzero_branch','normalize_d denominator alpha[9]-1/2 may be zero; prove the exact input law and same-run containment/simulation of its failure prefix. No charged-event inclusion is supplied by the generic lemma.'),
 ('PV_Inv_Guard.difference / nonzero_branch','emit denominator alpha[9]-1/2 may be zero; prove exact challenge law and failure-prefix simulation/containment on the headline coupling.'),
 ('PV_L2_InversionPole.producer; PV_Inv_NativeRegistry.producer; PV_Inv_NativePackScan.guarded_packing','Producer slot 0: bind registry tuple/tag, active row, packed slot and no_pole guard to this same run; use existing pole charge, not a new event.'),
 ('PV_L2_InversionPole.producer; PV_Inv_NativeRegistry.producer; PV_Inv_NativePackScan.guarded_packing','Producer slot 1: bind registry tuple/tag, active row, packed slot and no_pole guard to this same run; use existing pole charge, not a new event.'),
 ('PV_L2_InversionPole.consumer; PV_Inv_NativePackScan.guarded_packing','Consumer slot 0: bind registry tuple/tag, active row, packed slot and no_pole guard to this same run; use existing pole charge, not a new event.'),
 ('PV_L2_InversionPole.consumer; PV_Inv_NativePackScan.guarded_packing','Consumer slot 1: bind registry tuple/tag, active row, packed slot and no_pole guard to this same run; use existing pole charge, not a new event.'),
 ('PV_Inv_Circle.singular_iff / denominator_nonzero; PV_Inv_CircleSubfield.outside_subfield_safe','Bind actual parameter sampler and subfield exclusion, including raw candidates and fallback, to the headline joint history. Zero at +/-i is possible without that domain restriction; do not assign an unproved charge.')]
calls=[]
for i,(p,o) in enumerate(proofs):
 n=22+i;r=read(f'native{n:02}-detail.json');a=r['debug_corresponding_site'];assert a is not None
 calls.append(dict(site=r['baseline']['site'],caller=r['baseline_function'],debug_site=a['address'],debug_source_stack=stack(n,a['address']),proof=p,obligation=o,classification='LOCAL NONZERO immediate' if i in [3,4,5,6,7] else 'CONDITIONAL PROOF / native or event obligation OPEN',provenance='DWARF guide only; debug .text differs'))
(D/'call-proof-obligations.json').write_text(json.dumps(calls,indent=2)+'\n')
branches=[]
for n,addr in [(9,'0x19b812'),(12,'0x19e6f5')]:
 r=read(f'native{n:02}-detail.json');old=(D/f'native{n:02}-baseline-disassembly.txt').read_text().splitlines();new=(D/f'native{n:02}-debug-disassembly.txt').read_text().splitlines()
 oi=next(i for i,l in enumerate(old) if l.startswith(addr[2:]+':'))
 dbg=[l.strip() for l in new if re.match(r'\s*[a-f0-9]+:\s',l)]
 assert r['masked_sequence_equal'] and len(old)==len(dbg)
 da='0x'+dbg[oi].split(':',1)[0]
 inv=json.loads((D.parent/'codex-pv-l3a-20261029/inversions.json').read_text())
 target='0x19b810' if n==9 else '0x19e6d0'
 incoming=next(x['transfers'] for x in inv if x['address']==target)
 branches.append(dict(baseline=addr,instruction=old[oi],debug_address=da,debug_source_stack=stack(n,da),incoming_sites=[x['site'] for x in incoming],provenance='index correspondence in masked equal instruction sequences; DWARF guide only'))
(D/'zero-branch-guide.json').write_text(json.dumps(branches,indent=2)+'\n')
with lzma.open(D/'inline-kernel-guide.json.xz','rt') as f:rows=json.load(f)
f1=[r for r in rows if r['family'].startswith('F1')]
(D/'F1-inline-summary.json').write_text(json.dumps(dict(counts=collections.Counter(r['name'] for r in f1),instances=[dict(die=r['die'],name=r['name'],debug_ranges=r['ranges'],decl_file=r['decl_file'],decl_line=r['decl_line'],call_file=r['call_file'],call_line=r['call_line'],parents=r['parents'],mapped_instructions=len(r['guide_instruction_pairs']),unmapped=len(r['unmapped_debug_instructions'])) for r in f1]),indent=2)+'\n')
receipts=[]
for i in range(2,40):
 n=f'native{i:02}';r=read(n+'-receipt.json');ad=read(n+'-admission.json')
 assert r['exit']==0 and ad['allowed'] is True and r['swap_bytes']=='0'
 assert r['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
 log=(D/(n+'-time.log')).read_text();rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)
 receipts.append(dict(scope=n,**r,peak_rss_kib=int(rss[1])))
(D/'native-receipt-index.json').write_text(json.dumps(receipts,indent=2)+'\n')
assert len(calls)==17 and len(branches)==2
identity=read('debug-identity.json');assert not identity['text_identical']
flags=read('configuration-fingerprints.json');assert all(not x['rustflags'] for units in flags.values() for x in units)
# Publish compact logs without committing any file larger than 20 MiB.
for p in D.iterdir():
 if p.is_file() and p.suffix in ['.json','.txt','.log'] and p.stat().st_size>20*1024*1024:
  b=p.read_bytes();(D/(p.name+'.sha256')).write_text(hashlib.sha256(b).hexdigest()+'\n')
  with lzma.open(str(p)+'.xz','wb',preset=6) as f:f.write(b)
print(json.dumps(dict(calls=len(calls),zero_branches=len(branches),f1_inline_instances=len(f1),validated_prior_scopes=len(receipts),all_rustflags_empty=True)))
