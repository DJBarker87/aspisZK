"""Inspect physical entropy laws and exact source steps; no native closure claim."""
from pathlib import Path
import hashlib,json,re,sys

E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
names=['StackCopy','EntropyPhysicalCopy','NativeEntropyPhysical','StackMove',
       'LinuxRawABI','LinuxRawMachine','StackByteCodec','EntropyInnerFrame','EntropyCopiedRead']
modules=[]
for name in names:
    module='PV_EVH_'+name
    p=Path('lean/'+module+'.lean');raw=p.read_bytes();s=raw.decode()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s',s,re.M)
    laws=re.findall(r'^theorem (\w+)',s,re.M)
    assert set(laws)==set(re.findall(r'^#print axioms (\w+)',s,re.M))
    receipts=[json.loads(q.read_text()) for q in E.glob('receipt-*.json')]
    accepted=[r for r in receipts if r.get('accepted') and r['target']==module]
    assert len(accepted)==1,(module,'not uniquely accepted')
    r=accepted[0];assert r['source_sha256']==sha(raw)
    modules.append(dict(module=module,source_sha256=sha(raw),attempt=r['attempt'],laws=laws))

frame=json.loads((E/'entropy-frame-source.json').read_text())
copy=json.loads((E/'entropy-copy-restoration.json').read_text())
raw=json.loads((E/'getrandom-034-linux-raw-source.json').read_text())
assert sha(frame['source']['body'].encode())==frame['source']['body_sha256']
assert sha(copy['body'].encode())==copy['body_sha256']
for r in raw:assert sha(r['text'].encode())==r['sha256']
asm=next(r['text'] for r in raw if r['relative']=='src/backends/linux_raw.rs')
a=asm.index('} else if #[cfg(target_arch = "x86_64")]')
asm=asm[a:asm.index('} else {\n            compile_error!',a)]
for text in ['OFFSET + 318','in("rax") __NR_getrandom','in("rdi") buf',
             'in("rsi") buflen','in("rdx") flags','lateout("rax") r0',
             'lateout("rcx") _','lateout("r11") _','options(nostack, preserves_flags)']:
    assert text in asm
for text in ['field_mask_entropy.copy_from_slice(&bytes[..32]);',
             'leaf_salt_seed.copy_from_slice(&bytes[32..]);',
             'mask_nonce,\n                    field_mask_entropy,\n                    leaf_salt_seed,']:
    assert text in frame['source']['body']
assert 'ptr::copy_nonoverlapping(src.as_ptr(), dest.as_mut_ptr(), dest.len())' in copy['sources'][1]['text']
out=dict(
    evidence_class='checked local physical-state/value laws with structural source-step correspondence; actual native association incomplete',
    baseline='fa394f3858',modules=modules,
    source_inputs=[dict(path=str(E/n),sha256=sha((E/n).read_bytes())) for n in
      ['entropy-frame-source.json','entropy-copy-restoration.json','getrandom-034-linux-raw-source.json']],
    raw_asm=asm,
    correspondence=[
      'Both32 source initializers precede both copies; their derived ghost keys are distinct from each other and every prior live/retired lifetime',
      'copy_from_slice checks equal lengths then copy_nonoverlapping; source laws establish both exact32 lengths; StackCopy is byte-snapshot memory semantics, not an installed native primitive',
      'NativeEntropyPhysical consumes the SAME delivered raw history in the original extracted body and both destination backing laws, without per-half answer premises',
      'StackByteCodec proves U8 encoding lossless symbolically; it does not choose physical addresses',
      'StackMove relocates bytes and ghost ownership without inserting destructor/zeroize; residue is preserved only outside the destination footprint; it is not an actual native move instance',
      'LinuxRawABI matches the pinned x86_64/pointer64 register selection and signed64 conversion; LinuxRawMachine retains buffer/world/events on every outcome',
      'KernelFrame is transported from the machine interface footprint; the footprint is an explicitly RETAINED P, never inferred from joint density'],
    retained=[
      'ACTUAL original/inner/returned source-frame physical address, valid64-bit extents, separation/coherent heap interpretation',
      'actual source-pointer/inline-asm ABI/kernel interface and memory footprint association; no real kernel instance is supplied',
      'actual copy/read/move installation and returned structure including mask_nonce, compiler spills/residues, retry/drop and advancing family',
      'allocator metadata/padding/RawVec/Global/System ValidAnswer, owned Vec/native Heap/Box; resource failures remain WORLD answers',
      'complete libc/TLS/io::Error/EBADF/guards/hooks/backtrace diagnostics; seven callbacks and full entry',
      'L3/V370/V371/V400, D159/D166, V221/V222 deployed zeroize1.9.0, all endpoint/deployment conditions',
      'actual-family oraclePrefix/countTrace/nonce-store fileTrace links, D520/U/D524 inputs and actual success nonemptiness under v-prime'],
    axioms_mode='SUMMARY-BASED cached module lists (ax1-prime); no full-data NEP/coherence audit',
    native_runs=0,kani_runs=0,release_replay=False,rows_removed=[],trust_fields_added=[])
p=E/'physical-source-binding-D569.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS physical copy/byte/ownership/ABI source steps; actual native association OPEN')
