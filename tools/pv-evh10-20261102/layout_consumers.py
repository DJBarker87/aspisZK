"""Tie checked layout consumers to the adopted source binding and old laws."""
from pathlib import Path
import hashlib,json,re,sys
E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
binding=json.loads((E/'frame-source-binding-D572.json').read_text())
assert binding['binary']['sha256'].startswith('da36d6aa')
assert binding['layout']['reserved']==232
assert binding['layout']['original']==[0,64]
assert binding['layout']['field']==[64,96]
assert binding['layout']['seed']==[96,128]
names=['EntropyDeployedLayout','NativeEntropyLayout','EntropyLayoutReads',
 'NativeRawLayout','EntropyLayoutCleanup','EntropyReturnLayout','EntropyMoveKeys','LinuxRawLayout','NativeEntropyAdmittedLayout']
receipts=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')]
rows=[]
for name in names:
 module='PV_EVH_'+name;p=Path('lean/'+module+'.lean');raw=p.read_bytes();s=raw.decode()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s',s,re.M)
 accepted=[r for r in receipts if r['target']==module and r['accepted']]
 assert len(accepted)==1,(module,'requires exactly one accepted compile')
 r=accepted[0];assert r['source_sha256']==sha(raw)
 laws=re.findall(r'^theorem (\w+)',s,re.M)
 assert set(laws)==set(re.findall(r'^#print axioms (\w+)',s,re.M))
 rows.append(dict(module=module,source_sha256=sha(raw),attempt=r['attempt'],laws=laws))
layout=Path('lean/PV_EVH_EntropyDeployedLayout.lean').read_text()
for term in ['original owner sp w','owner (sp+64)','(sp+96)','sp+232','sp+64+32','sp+96+32']:
 assert term in layout,term
returns=Path('lean/PV_EVH_EntropyReturnLayout.lean').read_text()
for term in ['address := result+33','address := result+65','result+97 ≤ sp ∨ sp+232 ≤ result']:
 assert term in returns,term
comparisons=[
 dict(before='PV_EVH_NativeEntropyPhysical.source_and_backing',after='PV_EVH_NativeEntropyLayout.source_and_backing',removed=['original.initialized=64','field.initialized=32','seed.initialized=32','Separate field original','Separate seed original','Separate seed field'],retained='completed raw fill, source branch/retry guard; FRAME-CALL and KERNEL-WRITE actual association'),
 dict(before='PV_EVH_EntropyPhysicalReads.from_delivery',after='PV_EVH_EntropyLayoutReads.from_delivery',removed=['the same three extents and three local Separate inputs'],retained='bounded source read; actual read/copy interpretation FRAME-CALL'),
 dict(before='PV_EVH_NativeRawSpatial.error_with_request_frames',after='PV_EVH_NativeRawLayout.error_with_request_frames',removed=['independent original-slot HeapSeparate/LiveSeparate'],retained='actual whole232-byte reserved-frame external boundary FRAME-ENTRY; HEAP-ENTRY coherence; raw error and source branch guards'),
 dict(before='PV_EVH_EntropyRejectCleanup.all_cleared/heap_coherent',after='PV_EVH_EntropyLayoutCleanup.all_cleared/heap_coherent',removed=['three local pair separation and three independent per-slot heap frames'],retained='whole-frame external heap boundary and initial heap coherence'),
 dict(before='PV_EVH_EntropyMoveBacking.returned_backing',after='PV_EVH_EntropyReturnLayout.returned_backing',removed=['four independent source/returned-field region relations','three independent32-byte read bounds'],retained='CallerSeparate for actual caller97-byte initialized return footprint vs callee232-byte frame; pair relocation only, no complete installed Self/staging/observations'),
 dict(before='PV_EVH_EntropyMoveBacking.original_lookup',after='PV_EVH_EntropyMoveKeys.original_lookup/moved_ready_lookup',removed=['original key differs from each moved source key','returned keys do not shadow original','pre-move lookup for the admitted source-shaped ready state'],retained='existing pair relocation representation; full native move remains open'),
 dict(before='PV_EVH_LinuxRawABI.suffix_inputs',after='PV_EVH_LinuxRawLayout.suffix_inputs',removed=['independent original64 pointer-fit bound'],retained='runtime valid nonwrapping232-byte reservation; syscall footprint is not proved')]
comparisons.append(dict(before='PV_EVH_NativeEntropyPhysical.source_and_backing plus supplied original lookup',after='PV_EVH_NativeEntropyAdmittedLayout.source_and_backing',removed=['all six local extent/separation inputs','supplied pre-move original-slot lookup'],retained='one admitted source-shaped state with SAME raw history and original source; actual invocation/kernel association remains named P'))
out=dict(evidence_class='checked consumers of existing laws using own-1 adopted-layout binding; no new primitive implementation',
 source_binding_sha256=sha((E/'frame-source-binding-D572.json').read_bytes()),modules=rows,before_after=comparisons,
 caveat='Specialization to the mechanically recorded layout discharges local mathematical premises, not the relation of arbitrary State to an actual reached native invocation. Whole-frame and caller-frame boundaries remain named P, not claimed discharged by repackaging.',
 remaining_premises=binding['remaining_premises'],kernel_memory_discharged=False,actual_entry_interpretation_discharged=False,
 actual_native_closure=False,axioms_mode='SUMMARY-BASED cached module lists (ax1-prime); full-data NEP/coherence audit not run',
 rows_removed=[],trust_fields_added=[],native_runs=0,kani_runs=0,release_replay=False)
p=E/'layout-consumers-D572.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS layout consumers; local FRAME inputs discharged, exact external V370/runtime premises retained')
