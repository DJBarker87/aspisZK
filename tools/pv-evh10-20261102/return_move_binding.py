"""Own-1 source return binding with ordered adopted machine-store support."""
from pathlib import Path
import hashlib,json,re,sys
E=Path('evidence/pv-evh10-20261102');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=(E/'entropy-layout-da36d6aa.txt').read_text()
a=s.index('  14595d:');accepted=s[a:]
loads=[('xmm0','(%rsp)'),('xmm1','0x10(%rsp)'),('xmm2','(%r8)'),
       ('xmm3','0x10(%r8)'),('xmm4','(%r14)'),('xmm5','0x10(%r14)')]
for reg,src in loads:
 assert re.search(r'\b(?:movdqa|movdqu|movups)\s+'+re.escape(src)+',%'+reg+r'\b',accepted),(reg,src)
for anchor in ['lea    0x20(%rsp),%r8','mov    %rsi,%r14','mov    %rdi,%rbx']:assert anchor in s
stores=[]
for line in accepted.splitlines():
 m=re.search(r'\b(?:movdqa|movdqu|movaps|movups)\s+%(xmm\d+),(0x[0-9a-f]+)\(%(rsp|rbx)\)',line)
 if m:stores.append(dict(register=m[1],offset=int(m[2],16),base=m[3],size=16,instruction=line.strip()))
 if 'movb   $0x0,(%rbx)' in line:stores.append(dict(register='zero',offset=0,base='rbx',size=1,instruction=line.strip()))
expected=[('xmm1',176,'rsp',16),('xmm0',160,'rsp',16),('xmm2',192,'rsp',16),('xmm3',208,'rsp',16),
 ('xmm5',144,'rsp',16),('xmm4',128,'rsp',16),('xmm3',81,'rbx',16),('xmm5',17,'rbx',16),
 ('xmm4',1,'rbx',16),('xmm2',65,'rbx',16),('xmm1',49,'rbx',16),('xmm0',33,'rbx',16),('zero',0,'rbx',1)]
assert [(x['register'],x['offset'],x['base'],x['size']) for x in stores]==expected
entry=json.loads((E/'entry-frame-binding-D572.json').read_text())
body=next(x['body'] for x in entry['emitted'] if x['name'].endswith('generate_for_mask_nonce_loop.body'))
for token in ['mask_nonce,','field_mask_entropy := field_mask_entropy1','leaf_salt_seed := leaf_salt_seed1']:
 assert token in body,token
rust=next(x['body'] for x in entry['source'] if 'generate_for_mask_nonce(' in x['anchor'])
for token in ['return Ok(Self {','mask_nonce,','field_mask_entropy,','leaf_salt_seed,']:assert token in rust,token
out=dict(evidence_class='own-1 structural complete successful Self return binding with adopted ordered-store support; V370 retained',
 inputs=[dict(path=str(E/n),sha256=sha(E/n)) for n in ['entropy-layout-da36d6aa.txt','entry-frame-binding-D572.json','caller-source-binding-session2.json']],
 compiler_support=dict(register_loads=loads,stores=stores,executed=False),
 source_steps=[
 'Both source 32-byte inner copies are restored from the SAME original64 before the two nonzero checks.',
 'Only after both nonzero checks succeed does the source construct Self with the original mask_nonce, copied field_mask_entropy1 and leaf_salt_seed1.',
 'Self is moved into Ok. The two inner Zeroizing values are moved; no moved-from32 destructor is inserted. Original64 is dropped after constructing the return value.',
 'The adopted artifact captures six16-byte register values from original64 and the mask input, stages all96 bytes, stores the interleaved complete96-byte payload and the Ok tag, then jumps to original64 cleanup.',
 'EntropyReturnFootprint records exactly the13 physical stores in their observed order. It retains inner and staging residues. It is a memory-footprint model, not event-silence or a complete native-family installation.'
 ],remaining=[
 'V370: source-to-machine/register/ABI interpretation, elided source initializers, dead-load elimination and correspondence of original64 register reloads with the restored inner arrays.',
 'Runtime FRAME-ENTRY/HEAP-ENTRY/KERNEL-WRITE: actual valid call memory, allocator ownership/coherence and same-memory kernel replies on every prefix.',
 'MOVE-L3: actual load/store/register/spill events and lifetime transfer must be installed in the advancing world family, including all stale inner and staging bytes; the StackStores state alone does not establish those events.',
 'No full Result ABI extent/alignment/padding is inferred from97 initialized bytes. No actual successful worldRun or endpoint premise removal is claimed.'
 ],rows_removed=[],trust_fields_added=[],native_runs=0,kani_runs=0)
p=E/'return-source-binding-session2.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS complete96-byte return/tag/staging source binding; ordered13 stores; full native world remains open')
