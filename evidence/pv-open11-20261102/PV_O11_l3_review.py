"""Inspect retained machine/source evidence; this is not a native binding proof."""
from pathlib import Path
import hashlib,json,lzma,re
D=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((D/'PV_O11_l3-review-input-pins.json').read_text())
for p in pins.values():assert sha((D/p['snapshot']).read_bytes())==p['sha256']
A=D/'l3-audit-v2';summary=json.loads((A/'summary.json').read_text())
assert summary['binary_sha256']=='da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0'
assert summary['selected']==17 and summary['classifications']=={'CLEAN':10,'UNRESOLVED':7}
assert not summary['dwarf_present'] and not summary['inline_completeness']
assert (A/'PV_O11_machine_audit.py').read_bytes()==(D/'PV_O11_machine_audit.py').read_bytes()
assert (A/'PV_O11_machine_controls.py').read_bytes()==(D/'PV_O11_machine_controls.py').read_bytes()
controls=json.loads((A/'controls.json').read_text());assert len(controls)==9 and all(controls.values())
asm=lzma.decompress((A/'disassembly.txt.xz').read_bytes()).decode()
assert sha(asm.encode())==(A/'disassembly.txt.sha256').read_text().strip()
functions=json.loads(lzma.decompress((A/'function-index.json.xz').read_bytes()))
byaddress={f['address']:f for f in functions}
lines=asm.splitlines();contexts=[]
inverses=json.loads((A/'inversions.json').read_text())
for inv in inverses:
    for call in inv['transfers']:
        i=next(i for i,line in enumerate(lines) if re.match(r'\s*'+call['site'][2:]+r':',line))
        contexts.append(dict(**call,callee=inv['names'],caller_names=byaddress[call['caller']]['names'],
            instruction_context=lines[max(0,i-14):i+2],
            status='OPEN: symbol/transfer context only; no native operand or same-run observer binding'))
assert len(contexts)==16
(D/'PV_O11_inversion-call-contexts.json').write_text(json.dumps(contexts,indent=2)+'\n')
zero={
 'M31':{'address':'0x16fe02','instruction':'16fe02:\tje     17065f <aspis_core::field::M31::inv+0x85f>',
        'predicate':'test edi,edi; scalar raw input zero'},
 'QM31':{'address':'0x171168','instruction':'171168:\tje     171617 <aspis_core::field::QM31::try_inv+0x4d7>',
         'predicate':'OR of four loaded u32 limbs equals zero; canonical native representation remains to bind'}}
assert all(z['instruction'] in asm for z in zero.values())
rows={
 'V374':dict(rank=15,status='OPEN',exact_premise='Supply a preregistered whole-client leakage experiment for adopted da36d6aa, fixed public statement/domain and controlled witness classes, setup boundaries, randomized ordering, sample count/power, matched controls, thermal/frequency policy, raw samples and fail-closed statistical/cropping/multiple-test analysis. N73509 is baseline/draft fixture throughput; D299 measures old kernel-harness intervals with incomplete instruction equivalence. Neither supplies whole-client witness-class evidence. Finite non-detection remains measurement evidence, not universal constant-time proof.'),
 'V373':dict(rank=16,status='OPEN',exact_premise='Complete the adopted da36d6aa compiled-kernel audit: resolve seven selected bodies, actual operand/public-address/exponent/length ABIs, every indirect callee, every reached inlined copy and caller association. The corrected finite scanner covers 17 sized symbol bodies with 10 conditional heuristic CLEAN and 7 UNRESOLVED, 3048 unresolved indirect transfers and no DWARF/inline completeness. The old fa888460 debug guide has different text and cannot certify this image; its 345 incomplete origins are not resolved by relocation. Retain V370, V371, all failure/rejection prefixes and the full joint observer; no scanner label proves noninterference.'),
 'V380-inversion':dict(rank=17,status='OPEN',exact_premise='Bind every actually reached inversion, including all inlined copies, to the SAME adopted native operands, canonical representations, caller state and full observer. The 16 resolved transfers and zero branches at 0x16fe02/0x171168 are finite symbol evidence only. Instantiate existing interpolation i<28/denominator law, pivot find/swap/nonzero law, norm canonical-nonzero transports, sentinel zero rejection and joint retry law, actual constant-4 sites, normalize_d alpha[9]-1/2 zero failure law, circle sampler/subfield exclusion, and producer/consumer row/tag/slot/noPole equations jointly at their actual runs. Preserve earlier failure/pole events and their existing same-coupling charge/simulation obligations; do not invent a new charged event or dismiss zero branches as hardware trust. C056 remains suspended; old 17-call/debug-guide addresses do not establish new-image or inline coverage.')}
report=dict(classification='retained source/statement inspection plus finite static binary evidence; no theorem or complete native association',
 rows=rows,zero_branches=zero,summary=summary,controls=len(controls),
 unresolved=[dict(address=x['address'],names=x['names']) for x in json.loads((A/'instances.json').read_text()) if x['audit']['classification']=='UNRESOLVED'],
 attempts={'V374':dict(inspections=1,lean=0,native=0),'V373':dict(inspections=1,lean=0,native=2),'V380-inversion':dict(inspections=1,lean=0,native=0,reuses='N90509')},
 procedure=dict(N90509='Prelaunch regex matched a digit substring inside an old SHA, not an attempt ID. Shell sequencing nevertheless launched. Supplementary exact-token check found no other-job collision; it is not prelaunch evidence. Admission itself was allowed:true/exit0. No repeat was made.'),
 hashes={str(p.relative_to(D)):sha(p.read_bytes()) for p in [D/'PV_O11_l3-review-input-pins.json',D/'PV_O11_machine-audit.diff',D/'PV_O11_inversion-call-contexts.json']+[p for p in A.iterdir() if p.is_file()]},
 restored=0,premises_removed=0,premises_added=0,premises_weakened=0)
(D/'PV_O11_l3-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(ok=True,rows=list(rows),controls=len(controls),resolved_inversion_transfers=len(contexts),restored=0)))
