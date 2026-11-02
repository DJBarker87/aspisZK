"""Read-only adopted-artifact layout/source binding; never executes the client."""
from pathlib import Path
import hashlib,json,subprocess,sys

E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
adopted=json.loads((E/'adopted-backend-confirmation.json').read_text())
binary=adopted['adopted_build_receipt']['receipt']['path']
command=['objdump','-d','-C','--start-address=0x1457a0','--stop-address=0x1459d7',binary]
r=subprocess.run(['ssh','dombarker@100.108.41.90','sha256sum '+binary+' && '+' '.join(command)],text=True,capture_output=True)
assert r.returncode==0,r.stderr
digest,asm=r.stdout.split('\n',1)
assert digest.split()[0]==adopted['adopted_build_receipt']['receipt']['sha256']
assert asm==(E/'entropy-layout-da36d6aa.txt').read_text()
anchors={
 'frame':'sub    $0xe8,%rsp',
 'original':'mov    %rsp,%r13',
 'field':'lea    0x40(%rsp),%r12',
 'seed':'lea    0x60(%rsp),%r15',
 'second_half':'lea    0x20(%rsp),%r8',
 'length':'mov    $0x40,%esi',
 'pointer':'mov    %r13,%rdi',
 'number':'mov    $0x13e,%eax',
 'flags':'xor    %edx,%edx',
 'syscall':'145817:',
 'interrupted':'cmp    $0xfffffffffffffffc,%rax',
 'decrease':'sub    %rax,%rsi',
 'advance':'add    %rax,%rdi',
 'field_copy':'movdqa %xmm2,0x40(%rsp)',
 'seed_copy':'movdqa %xmm0,0x60(%rsp)',
 'mask_stage':'movdqa %xmm4,0x80(%rsp)',
 'field_stage':'movdqa %xmm0,0xa0(%rsp)',
 'seed_stage':'movdqa %xmm2,0xc0(%rsp)',
 'mask_return':'movdqu %xmm4,0x1(%rbx)',
 'field_return':'movdqu %xmm0,0x21(%rbx)',
 'seed_return':'movdqu %xmm2,0x41(%rbx)',
 'ok_tag':'movb   $0x0,(%rbx)',
 'cleanup':'movb   $0x0,(%rsp,%rax,1)',
}
for name,anchor in anchors.items():assert anchor in asm,(name,anchor)
frame=json.loads((E/'entropy-frame-source.json').read_text())
copy=json.loads((E/'entropy-copy-restoration.json').read_text())
current_source=subprocess.check_output(['git','show','HEAD:'+frame['source']['path']])
adopted_revision=adopted['adopted_build_receipt']['revision']
adopted_source=subprocess.check_output(['git','show',adopted_revision+':'+frame['source']['path']])
assert adopted_source==current_source and frame['source']['sha256']==sha(current_source)
assert 'let bytes1 := as_mut_back s1' in copy['body']
assert 'let field_mask_entropy1 := deref_mut_back a5' in copy['body']
assert 'let leaf_salt_seed1 := deref_mut_back1 a7' in copy['body']
raw=json.loads((E/'getrandom-034-linux-raw-source.json').read_text())
backend=next(x['text'] for x in raw if x['relative']=='src/backends/linux_raw.rs')
assert 'options(nostack, preserves_flags)' in backend
assert 'options(nomem' not in backend and 'options(readonly' not in backend
out=dict(
 evidence_class='own-1 structural source binding with read-only adopted-binary layout support; V370 retained',
 baseline='e08d80635057554f109651811ea8be512e24b1ff',
 binary=dict(path=binary,sha256=digest.split()[0],executed=False),
 adopted_source=dict(revision=adopted_revision,path=frame['source']['path'],sha256=sha(adopted_source),byte_equal_current=True),
 disassembly=dict(command=command,path=str(E/'entropy-layout-da36d6aa.txt'),sha256=sha(asm.encode()),anchors=anchors),
 source_inputs=[dict(path=str(E/n),sha256=sha((E/n).read_bytes())) for n in ['entropy-frame-source.json','entropy-copy-restoration.json','getrandom-034-linux-raw-source.json','adopted-backend-confirmation.json']],
 layout=dict(base='rsp after six pushes and sub 232; SYMBOLIC, no chosen numeric stack address',reserved=232,
   original=[0,64],field=[64,96],seed=[96,128],mask_staging=[128,160],field_staging=[160,192],seed_staging=[192,224],
   returned_base='incoming rdi saved in rbx',result_tag=[0,1],returned_mask=[1,33],returned_field=[33,65],returned_seed=[65,97],result_initialized_footprint=[0,97],
   result_allocation_extent='Not inferred from max store offset; full ABI size/alignment/padding remains V370/runtime metadata'),
 binding=[
  'Original Zeroizing([0;64]) initializer maps to four xmm zero stores at rsp offsets0,16,32,48.',
  'AsMut reaches original64; register rdi=rsp,rsi=64,rax=318,rdx=0 at first syscall. EINTR repeats; positive partial return reduces rsi and advances rdi before next syscall.',
  'Both source inner initializers precede copies. Optimized artifact elides their zero stores before overwriting both32; this compiler transformation remains V370, not evidence that source has no initializer.',
  'Both original and inner backward continuations are applied in the pinned extraction. Copies target field rsp+64 and seed rsp+96, preserving original rsp..rsp+64.',
  'Reject calls seed32 zeroize then field32 zeroize and clears original64; next retry reuses numeric offsets with fresh ghost lifetimes.',
  'Accept stages all three Self fields at rsp+128..224, writes all96 bytes at returned_base+1..97, writes Ok tag, then clears original64. No inner moved-from destructor or staging zeroing is emitted.',
  'Addresses are a layout of the actual adopted entropy function; arbitrary StackZero.State is NOT thereby proved to interpret a reached call. No universal heap coherence follows from source text.'
 ],
 remaining_premises=[
  dict(id='FRAME-CALL',classification='V370 compiler-cohort item',statement='At each reached call, StackZero memory/live keys interpret the actual Rust frame; symbolic base is the post-prologue rsp; original/inner addresses equal the recorded offsets. Compiler preserves source initialization/copy/drop and borrow restoration, including elided stores and SIMD reads.'),
  dict(id='FRAME-ENTRY',classification='runtime obligation with compiler stack preservation under V370',statement='The actual 232-byte writable reserved frame has a valid nonwrapping64-bit extent and is disjoint from each pre-existing live owner and each live heap allocation. The caller-provided Result destination (including its actual ABI padding; success initializes97 bytes) and32-byte mask input are valid and obey Rust call aliasing rules. This is required only of reached entry states, never arbitrary State.'),
  dict(id='HEAP-ENTRY',classification='runtime allocator obligation (rdea-1)',statement='Every represented live heap block is an actual live allocation and its initialized bytes equal the physical memory interpretation; malloc/RawVec/System metadata and ownership are faithful.'),
  dict(id='KERNEL-WRITE',classification='runtime obligation',statement='Each actual getrandom syscall writes only within its passed mutable suffix on EVERY terminal or interrupted prefix, preserves other process heap/live bytes and allocator ownership, and returns a buffer/world/event record decoded from that same memory. KernelFrame alone covers only consumed-prefix equality and is weaker than this full obligation.'),
  dict(id='RAW-ABI',classification='V370 compiler-cohort item plus runtime ABI obligation',statement='Actual syscall register and pointer-width/signed-return interpretation matches the pinned x86_64 driver, including compiler memory clobber and preserved state; no nostack/preserves_flags option implies a kernel memory footprint.'),
  dict(id='MOVE-L3',classification='V370 compiler-cohort item and runtime observation obligation',statement='Return destination backing, all staging slots/registers/spills and old inner32 residues participate in the existing L3 observer and advancing native world family; copying returned values is not erasure of those other locations.')
 ],
 discharged_at_layout_level=['pairwise original64/field32/seed32 numeric separation','all three extents and containment inside the232-byte reserved frame','actual source/getrandom register request selection, conditional on retained compiler/ABI association'],
 kernel_memory_discharged=False,actual_entry_interpretation_discharged=False,
 axioms_mode='SUMMARY-BASED only (ax1-prime); no full-data NEP/coherence claim',
 trust_fields_added=[],rows_removed=[],native_runs=0,kani_runs=0)
p=E/'frame-source-binding-D572.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS adopted frame offsets/source call binding; exact V370/runtime premises retained; T unchanged')
