"""Check D582 structural evidence only; never certify an actual process run."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path('evidence/pv-evh10-20261102');O=E/'os-model-D582'
sha=lambda b:hashlib.sha256(b).hexdigest()
m=json.loads((O/'manifest.json').read_text())
commit=json.loads((O/'tag-object-v6.8.json').read_text())['object']['sha']
assert commit=='e8f897f4afef0031fe618a8e94127a0934896aba'
sources={}
for item in m['sources']:
 p=Path(item['path']);b=p.read_bytes();assert len(b)==item['bytes'] and sha(b)==item['sha256'];sources[item['upstream_path']]=b.decode()
anchors={
 'drivers/char/random.c':['SYSCALL_DEFINE3(getrandom','import_ubuf(ITER_DEST, ubuf, len, &iter)','return get_random_bytes_user(&iter);','copied = copy_to_iter(block, sizeof(block), iter);','return ret ? ret : -EFAULT;'],
 'lib/iov_iter.c':['iov_iter_ubuf(i, rw, buf, len);','len = raw_copy_to_user(iter_to, from, len);','if (len > MAX_RW_COUNT)'],
 'include/linux/iov_iter.h':['if (unlikely(iter->count < len))','len = iter->count;','return iterate_ubuf(iter, len, priv, priv2, ustep);','iter->iov_offset += progress;','iter->count -= progress;'],
 'include/linux/uio.h':['.ubuf = buf,','.count = count,'],
 'include/linux/uaccess.h':['outside of those areas.','All data past to + size - N must be left unmodified.'],
 'fs/binfmt_elf.c':['if (p_flags & PF_R)','prot |= PROT_READ;','if (p_flags & PF_W)','prot |= PROT_WRITE;','elf_flags = MAP_PRIVATE;'],
 'fs/exec.c':['vm_flags = VM_STACK_FLAGS;','stack_expand = min(rlim_stack, stack_size + stack_expand);','ret = expand_stack_locked(vma, stack_base);'],
 'include/linux/mm.h':['#define VM_STACK_FLAGS','VM_DATA_FLAGS_NON_EXEC\t(VM_READ | VM_WRITE'],
 'mm/mmap.c':['VM_DATA_DEFAULT_FLAGS | VM_ACCOUNT | mm->def_flags'],
 'kernel/fork.c':['if (clone_flags & CLONE_VM) {','mm = oldmm;'],
 'arch/x86/entry/syscalls/syscall_64.tbl':['318\tcommon\tgetrandom\t\tsys_getrandom'],
}
for f,values in anchors.items():
 for s in values:assert s in sources[f],(f,s)
asm=json.loads((E/'out-N91601.log').read_text())
a=next(f['disassembly'] for f in asm['functions'] if 'generate_for_mask_nonce' in f['header'])
for pc,s in [('145806','mov    $0x40,%esi'),('145810','mov    $0x13e,%eax'),('145817','syscall')]:
 line=next(l for l in a.splitlines() if re.match(r'\s*'+pc+':',l));assert s in line,(pc,line)
# This arithmetic illustrates a missing implication, not a fabricated actual q.
# A 16-aligned sp can be 16 bytes below a stack VMA whose lower bound is L.
L=4096;sp=L-16
assert sp%16==0 and sp+232>=L and sp<L
assert all(0<=o<=64 and sp+o+(64-o)==sp+64 for o in range(65))
# Keep the exact requested statement and the actual domain unchanged.
old=(E/'BLOCKER-D580.md').read_text();new=(E/'BLOCKER-D582.md').read_text()
i=old.index('```text\nactual_frame_entry');j=old.index('\n```',i)+4
assert old[i:j] in new
for p in O.iterdir():assert p.stat().st_size<=20*1024*1024
out=dict(evidence_class='binary-structural (adopted binary), plus OS-model; V370 compiler-cohort',linux_reference_commit=commit,linux_is_observed_deployment=False,source_manifest_sha256=sha((O/'manifest.json').read_bytes()),sources_checked=len(sources),mapped_permission_class_supplied=True,mapped_frame_coverage_discharged=False,same_prefix_kernel_structural_association_supplied=True,binary_sha256=asm['binary']['sha256'],kernel_payload_boundary='same reached syscall; bounded ITER_DEST user copy; post-buffer from same actual bytes',kernel_universal_ValidAnswer_claimed=False,owner_dependency='OWNER_actual_prefix (pv-evhB4; consume only after lead merge)',owner_implemented_here=False,actual_domain_implemented=False,actual_frame_entry_discharged=False,kernel_Lean_instance_installed=False,five_projections_installed=False,rows_removed=[],trust_fields_added=[])
if '--os-only' not in sys.argv:
 r=json.loads((E/'receipt-N91602.json').read_text());x=json.loads((E/'out-N91602.log').read_text())
 meta=json.loads((E/'host-final-D582.json').read_text())
 assert meta['scope']['status']=='inactive'
 assert meta['objdump']==asm['tools']['objdump']
 assert r['exit']=='0' and r['admission_allowed'] and r['admission_exit']==0
 assert sha((E/'out-N91602.log').read_bytes())==r['output_sha256']
 assert x['binary_sha256']==asm['binary']['sha256'] and x['executed'] is False
 assert re.search(r'GNU_STACK\s+.*\bRW\b',x['program_headers'])
 assert re.search(r'LOAD\s+.*\bRW\b',x['program_headers'])
 assert 'DYN (Position-Independent Executable file)' in x['elf_header']
 assert subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']])==Path(r['source_path']).read_bytes()
 assert sha(Path(r['source_path']).read_bytes())==r['source_sha256']
 out['mapping_inspection']=dict(attempt='N91602',output_sha256=r['output_sha256'],program_headers=x['program_headers'])
p=E/'runtime-boundary-D582.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
elif '--os-only' not in sys.argv:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS D582 reference OS/source/ABI/boundary checks; no whole-runtime proof claim')
