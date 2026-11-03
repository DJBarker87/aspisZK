"""Structural caller-to-callee layout binding over committed artifact evidence."""
from pathlib import Path
import hashlib,json,sys
E=Path('evidence/pv-evh10-20261102')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=json.loads((E/'entropy-callers-da36d6aa.json').read_text())
adopted=json.loads((E/'adopted-backend-confirmation.json').read_text())
assert d['binary']['sha256']==adopted['adopted_build_receipt']['receipt']['sha256']
assert len(d['windows'])==1
w=d['windows'][0];s=w['function']+'\n'+w['window']
for a in ['<aspis_r1_cost_probe::prover::retry_attempt>:',
          'sub    $0x108,%rsp','lea    0x40(%rsp),%rdi',
          'lea    0x10(%rsp),%rsi','call   *0x18b687(%rip)',
          'cmpb   $0x0,0x40(%rsp)']:assert a in s,a
assert any('1e80a0' in r and '1457a0' in r for r in d['relocations'])
callee=(E/'entropy-layout-da36d6aa.txt').read_text()
prologue=callee.split('sub    $0xe8,%rsp')[0]
assert prologue.count('\tpush   ')==6
out=dict(evidence_class='own-1 structural binding with adopted call-site support; V370 retained',
 binary=d['binary'],inputs=[dict(path=str(E/n),sha256=sha(E/n)) for n in
 ['entropy-callers-da36d6aa.json','entropy-layout-da36d6aa.txt','entry-frame-binding-D572.json']],
 relation=dict(caller_rsp='callee_sp + 8 return-address bytes + 48 saved-register bytes + 232 reserved bytes',
               caller_offset=288,mask_offset=304,result_offset=352,caller_reserved=264,
               initialized_result_bytes=97,full_result_ABI_size='not inferred'),
 discharged=['CallerSeparate at this identified retry_attempt call site',
             'mask input outside callee frame and disjoint from initialized return footprint',
             'initialized return footprint contained in caller reservation'],
 retained=[
 'FRAME-CALL and MOVE-COMPILER: actual reached invocation and source-memory interpretation are V370 compiler-cohort obligations; a single static call-site inventory is not a full address-escape/control-flow proof.',
 'FRAME-ENTRY: caller reservation must actually be writable, aligned, nonwrapping, externally disjoint and mapped to the same memory; no arbitrary numeric address is invented.',
 'HEAP-ENTRY and KERNEL-WRITE runtime obligations unchanged; register selection and disjoint stack offsets do not prove a kernel footprint.',
 'Full Result ABI layout/padding, complete actual Self move and all L3 observations, advancing native family and successful actual run remain open.'
 ],theorem='PV_EVH_EntropyCallerLayout.returned_backing',rows_removed=[],trust_fields_added=[])
p=E/'caller-source-binding-session2.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS caller/callee offset binding; exact invocation/runtime obligations retained')
