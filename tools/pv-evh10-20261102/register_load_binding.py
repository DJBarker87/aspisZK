"""Read-only structural binding of the interleaved adopted return reloads."""
from pathlib import Path
import hashlib,json,re,sys
E=Path('evidence/pv-evh10-20261102');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=E/'entropy-layout-da36d6aa.txt';text=p.read_text();accepted=text[text.index('  14595d:'):]
loads=[];stores=0
for line in accepted.splitlines():
 m=re.search(r'^\s*([0-9a-f]+):.*\b(?:movdqa|movdqu|movups)\s+([^,]+),%xmm([0-5])\s*$',line)
 if m:loads.append(dict(pc=int(m[1],16),register=int(m[3]),operand=m[2],precedingStores=stores,instruction=line.strip()))
 if re.search(r'\b(?:movdqa|movdqu|movaps|movups)\s+%xmm\d+,0x[0-9a-f]+\(%(?:rsp|rbx)\)',line) or 'movb   $0x0,(%rbx)' in line:stores+=1
expected=[(0x14595d,0,'(%rsp)',0),(0x145962,1,'0x10(%rsp)',0),
 (0x14597a,2,'(%r8)',2),(0x14597f,3,'0x10(%r8)',2),
 (0x145997,4,'(%r14)',4),(0x14599c,5,'0x10(%r14)',4)]
assert [(x['pc'],x['register'],x['operand'],x['precedingStores']) for x in loads]==expected
assert stores==13
model=Path('lean/PV_EVH_ReturnRegisterLoads.lean');s=model.read_text()
for pc,reg,operand,n in expected:
 addr={'(%rsp)':'sp','0x10(%rsp)':'sp+16','(%r8)':'sp+32',
  '0x10(%r8)':'sp+48','(%r14)':'mask sp','0x10(%r14)':'mask sp+16'}[operand]
 assert f'⟨{hex(pc)},{reg},{addr},{n}⟩' in s
cleanup=text[text.index('  145920:'):text.index('  145956:')]
assert not re.search(r'%xmm\d+',cleanup)
receipt=json.loads((E/'frame-source-binding-D572.json').read_text())
out=dict(evidence_class='own-1 structural adopted interleaved register-load binding; V370 retained',
 inputs=[dict(path=str(p),sha256=sha(p)),dict(path=str(model),sha256=sha(model))],
 adopted_binary=receipt['binary'],loads=loads,ordered_return_stores=stores,
 checked=[
  'The six 16-byte reloads occur before store counts 0,0,2,2,4,4, respectively. They are not hoisted to branch entry by this interpretation.',
  'ReturnRegisterLoads.current_reload proves the current physical memory at EACH reload equals the entry-to-return snapshot for all sixteen lanes. Only existing named store-footprint laws and numeric interval separation are used.',
  'Adopted original64 cleanup and return epilogue contain no XMM instruction. The six loaded vectors are not cleared there. This is structural artifact evidence, not a theorem that all other register/spill channels have been covered.'
 ],retained=[
  'Actual reached FRAME-CALL/RAW-ABI/MOVE-COMPILER under V370, runtime FRAME-ENTRY and full KERNEL-WRITE instance.',
  'Actual L3 observer and advancing native family installation, including all caller-saved registers, syscall clobbers, callee-saved registers, stack spills, inner/staging residues and caller continuation.',
  'No NativeEvent is invented to expose a private snapshot, and no memory or register operation is claimed silent.'
 ],rows_removed=[],trust_fields_added=[],native_runs=0,kani_runs=0)
p=E/'register-load-binding-D578.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS six interleaved adopted reloads and retained XMM values; actual L3 family remains open')
