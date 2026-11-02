"""Read-only structural association of the recorded deployed zeroize law.
This does not assert full-entry native adequacy or an L3 observer law.
"""
from pathlib import Path
import json,hashlib,subprocess,sys
E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
old_path='evidence/pv-rdcd-20261028/zeroize190-complete-structural.json'
raw=subprocess.check_output(['git','show','HEAD:'+old_path]);old=json.loads(raw)
current=json.load(open(E/'native-sources.json'))
z=next(v for v in current['library'] if '/zeroize-1.9.0/' in v['path'])
assert old['sources'][z['path']]['sha256']==z['sha256']
assert old['selected_cfg']==dict(target_arch='x86_64',miri=False)
steps=[]
associations=[
 ('impl<Z> Drop for Zeroizing<Z>','delegate once to the owned array, then end stack lifetime','PV_EVH_StackZero.drop'),
 ('impl<Z, const N: usize> Zeroize for [Z; N]','delegate to exclusive iter_mut over initialized array','PV_EVH_DeployedZeroCursor.source'),
 ("impl<Z> Zeroize for IterMut<'_, Z>",'visit every element once and restore each changed byte','PV_EVH_ZeroAddressBridge.cells_deployed'),
 ('impl<Z> Zeroize for Z','volatile default-zero store followed by barrier for EACH element','PV_EVH_DeployedZeroWorld.byte'),
 ('fn volatile_write<T: Copy + Sized>(dst: &mut T, src: T)','ptr::write_volatile to the same exclusive address','PV_EVH_DeployedZeroWorld.byte'),
 ('pub fn optimization_barrier<T: ?Sized>','selected x86_64 readonly/preserves_flags/nostack assembly barrier','PV_EVH_ZeroAddressBridge.physical_trace'),
 ('fn next(&mut self) -> Option<$elem>','non-ZST cursor: detect end, advance one byte, return OLD exclusive reference','PV_EVH_DeployedZeroCursor.source'),
]
for anchor,meaning,law in associations:
 hits=[v for v in old['checks'] if v['anchor']==anchor];assert len(hits)==1,anchor
 v=hits[0];assert v['complete_body_tokens_match']
 steps.append(dict(anchor=anchor,source=v['path'],body_sha256=sha(v['body'].encode()),structural_step=meaning,law=law))
# Tie the ? cleanup obligation to the frozen project source, not the helper's name.
p=next(p for p in current['project'] if p['path'].endswith('state_only_entropy.rs'))
project=subprocess.check_output(['git','show','HEAD:'+p['path']]);assert sha(project)==p['sha256']
s=project.decode();assert 'Zeroizing::new([0u8; 64])' in s
assert 'getrandom::fill(bytes.as_mut())?' in s
# Pin the exact extracted dictionary used by our retained cohort.
prep=json.load(open(E/'prepare-PV_EVH_NativeZeroBoundary.json'))['result']
funs=next(v['source'] for v in prep['project_checks'] if v['module']=='R1Z.ProverRwFullFuns')
fraw=subprocess.check_output(['git','show',funs['revision']+':'+funs['path']]);assert sha(fraw)==funs['source_sha256']
for anchor in ['def zeroize.Zeroize.Blanket','def Array.Insts.ZeroizeZeroize','zeroize-1.8.1/src/lib.rs']:assert anchor in fraw.decode()
result=dict(evidence_class='structural source association (own-1), existing deployed dependency law replay',
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 recorded_source=dict(path=old_path,sha256=sha(raw)),deployed_zeroize_sha256=z['sha256'],
 steps=steps,project_entropy=dict(path=p['path'],sha256=p['sha256'],
 error_cleanup='? ordinarily drops the original initialized 64-byte stack array, including partially written bytes',
 laws=['PV_EVH_StackCleanup.error_drop_full','PV_EVH_StackCleanup.error_zeroized','PV_EVH_StackCleanup.abort_preserves_prefix']),
 extracted_dictionary=funs,version_boundary='Retained extraction names zeroize1.8.1; only its dictionary routing is used. Deployed effects/values come from the separately bound recorded 1.9.0 law, never the old fence law.',
 native_selection=['PV_EVH_NativeZeroBoundary.array_residual','PV_EVH_NativeZeroBoundary.scalar_residual','PV_EVH_NativeZeroInstall.execution_native'],
 status='zeroize leaf association only; native entry closure remains OPEN',
 retained=['V370 source-to-machine compiler preservation','valid exclusive initialized array and actual stack admission','whole residual dictionary family provenance at entry','heap/stack address coherence','L3 register/spill/copy/retired-memory observation and joint law','all remaining heap, diagnostic, callback and mutable-restoration leaves'],
 trust_fields_added=[],endpoint_rows_removed=[])
p=E/'zero-native-binding.json'
if '--check' in sys.argv:
 prev=json.load(open(p));result['source_revision']=prev['source_revision'];assert prev==result
else:p.write_text(json.dumps(result,indent=2)+'\n')
print('PASS deployed zeroize source steps and actual dictionary routing; entry obligations retained')
