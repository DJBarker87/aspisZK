"""Check D581 binary/source correspondence; never asserts runtime adequacy."""
from pathlib import Path
import json,hashlib,subprocess,re,sys
E=Path('evidence/pv-evh10-20261102');sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads((E/'out-N91601.log').read_text())
assert x['binary']['sha256']=='da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0'
find=lambda name:next(f['disassembly'] for f in x['functions'] if name in f['header'])
plan=find('plan::prove');retry=find('prover::retry_attempt');entropy=find('generate_for_mask_nonce');zero=find('<[Z; N]')
def at(asm,pc,operand):
 line=next(l for l in asm.splitlines() if re.match(r'\s*'+pc+':',l));assert operand in line,(pc,operand,line)
for asm,pc,op in [(plan,'4f3a5','sub    $0x2a8,%rsp'),(plan,'527b5','call   5c990'),(retry,'5c99a','sub    $0x108,%rsp'),(retry,'5c9ac','cmp    $0x7,%rbp'),(retry,'5c9cb','cmp    0x100(%rdx),%rbp'),(retry,'5c9ec','movups (%rdx,%rax,1),%xmm0'),(retry,'5ca02','mov    %rbp,0x100(%rdx)'),(retry,'5ca09','lea    0x40(%rsp),%rdi'),(retry,'5ca0e','lea    0x10(%rsp),%rsi'),(retry,'5ca13','# 1e80a0'),(entropy,'1457aa','sub    $0xe8,%rsp'),(entropy,'1457d2','je     1458f7'),(entropy,'1457ef','movdqa %xmm4,0x30(%rsp)'),(entropy,'145801','movdqa %xmm4,(%rsp)'),(entropy,'145817','syscall'),(entropy,'145851','movdqa %xmm2,0x40(%rsp)'),(entropy,'145868','movdqa %xmm0,0x60(%rsp)'),(entropy,'1458c0','call   144ac0'),(entropy,'1458c8','call   144ac0'),(entropy,'1458d4','movb   $0x0,(%rsp,%rax,1)'),(entropy,'145934','movb   $0x0,(%rsp,%rax,1)'),(entropy,'1459a9','movdqa %xmm4,0x80(%rsp)'),(entropy,'145971','movdqa %xmm0,0xa0(%rsp)'),(entropy,'145985','movdqa %xmm2,0xc0(%rsp)')]:at(asm,pc,op)
assert any('00000000001e80a0' in l and l.rstrip().endswith('1457a0') for l in x['relocations'])
assert plan.count('sub    $0x1000,%rsp')==5
stores=re.findall(r'movb\s+\$0x0,(?:(0x[0-9a-f]+))?\(%rdi\)',zero)
assert sorted(int(offset,16) if offset else 0 for offset in stores)==list(range(32))
assert 'xmm' not in entropy[entropy.index('  145920:'):entropy.index('  145956:')]
# Preserve the requested statement verbatim instead of silently changing its binders.
a=(E/'BLOCKER-D580.md').read_text();b=(E/'BLOCKER-D581.md').read_text()
start=a.index('```text\nactual_frame_entry');stop=a.index('\n```',start)+4
assert a[start:stop] in b
assert 'prove_for_proof_accounts' not in '\n'.join(x['symbols'])
slots=[('original64',0,64,'1457ef..145801'),('field32',64,96,'14584b..145851'),('seed32',96,128,'145862..145868'),('mask_staging',128,160,'145997..1459a9'),('field_staging',160,192,'14595d..145971'),('seed_staging',192,224,'14597a..14598e'),('unassigned_tail',224,232,'no secret store identified')]
for _,a,b,_ in slots:assert 0<=a<b<=232
for a,b in zip(slots,slots[1:]):assert a[2]==b[1]
# ABI arithmetic is conditional on valid nonwrapping entry stacks, not permissions.
assert (8-6*8-232)%16==0 and (8-6*8-264)%16==0
assert 232+8==240 and 240+16==256 and 240+64==304
rev='4ea2abfcc3a50f1b6e766ed41ff07cf815085a87';sources=[]
for p in ['tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs','crates/aspis-r1-cost-probe/src/RealR1_client.rs','crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-prover/src/state_only_entropy.rs']:
 raw=subprocess.check_output(['git','show',rev+':'+p]);sources.append(dict(revision=rev,path=p,sha256=sha(raw),blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip()))
assert 'accounts.nonce(k)' in subprocess.check_output(['git','show',rev+':'+sources[0]['path']],text=True)
assert 'self.entered += 1' in subprocess.check_output(['git','show',rev+':'+sources[1]['path']],text=True)
frontier=[]
for field,projection in [('native','events plus faithful terminal conversion'),('fileTrace','PV_RJ4IDB.nativeFiles run.events'),('countTrace','(PV_RJ4IDB.nativeCounts run.events, PV_RJ4IDB.nativeRejections run.events)'),('timeTrace','PV_RJ4IDB.nativeTimes run.events'),('oraclePrefix','PV_RJ4IDB.nativeOracle run.events')]:
 text=Path('lean/PV_EVH_RuntimeBinding.lean').read_text();assert re.search(r'^  '+field+r' := missing\.'+field+r'_OPEN$',text,re.M)
 frontier.append(dict(field=field,projection=projection,installed=False))
out=dict(evidence_class='binary-structural (adopted binary), plus V370 compiler-cohort',binary=x['binary'],tools=x['tools'],analysis_sha256=sha((E/'out-N91601.log').read_bytes()),sources=sources,slots=[dict(name=n,start=a,stop=b,pc=pc) for n,a,b,pc in slots],frames=dict(plan_reserved=0x52a8,retry_reserved=264,entropy_reserved=232,entropy_sp_relative_to_retry_sp=-240,mask_relative_to_entropy_sp=256,result_relative_to_entropy_sp=304),domain_implemented=False,actual_frame_entry_discharged=False,kernel_instance_discharged=False,projections=frontier,rows_removed=[],trust_fields_added=[])
p=E/'binary-correspondence-D581.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS binary anchors/source pins/slot arithmetic/five OPEN selectors; no runtime-instance claim')
