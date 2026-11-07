from pathlib import Path
import json,hashlib,subprocess,os,shutil
import NMX_stage as S
B=Path.cwd();src=B/'NMX_registry_r5_emitted';out=B/'NMX_registry_r6_emitted';out.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((src/'NMX_PINS.json').read_text());assert pins['charon_exit']==0 and pins['llbc_sha256']==sha(src/'registry.llbc')=='44630437baad081b172d85de02c66403b3aa12802d0ede9da0079944a629abfa'
manifest=S.stage(B/'NMX_registry_r5_src');assert sha(B/'NMX_registry_r5_src/Cargo.lock')==pins['lock_before']==pins['lock_after']
for name,h in S.PINS.items():assert sha(S.TOOLROOT/name)==h
current=json.loads((src/'registry.llbc').read_text());assert not current['has_errors'];decls=[f for f in current.get('translated',current)['fun_decls'] if f is not None]
name=lambda f:'::'.join(x['Ident'][0] for x in f['item_meta']['name'] if 'Ident' in x)
owner='aspis_r1_cost_probe_program::r1_pool_adapter::deployment_ids::'
parent=next(f for f in decls if name(f)==owner+'deployment_id');assert parent['body']=='Opaque'
assert not [f for f in decls if name(f)==owner+'program_id']
oldpath=B/'NMX_registry_emitted/registry.llbc';old=json.loads(oldpath.read_text());oldfs=[f for f in old.get('translated',old)['fun_decls'] if f is not None]
op=next(f for f in oldfs if name(f)==owner+'deployment_id');oc=next(f for f in oldfs if name(f)==owner+'program_id')
assert S.sha((op['item_meta'].get('source_text') or '').encode())==S.sha((parent['item_meta'].get('source_text') or '').encode())=='97192085e5f3bf38ca687929f50b07f80982cc5f501caf008dfa03611f5bb8c5'
def calls(x):
 if isinstance(x,dict):
  if 'Call' in x:yield x['Call']['call']['func']
  for v in x.values():yield from calls(v)
 elif isinstance(x,list):
  for v in x:yield from calls(v)
assert any(f.get('Regular',{}).get('kind',{}).get('Fun',{}).get('Regular')==oc['def_id'] for f in calls(op['body']))
for suffix in ['deployment_id','program_id']:
 assert 'crate::r1_pool_adapter::deployment_ids::'+suffix in pins['charon_command']
witness=dict(parent_name=owner+'deployment_id',parent_current_body='Opaque',child_name=owner+'program_id',child_absent=True,previous_direct_call=True,previous_llbc_sha256=sha(oldpath),same_parent_source_sha256='97192085e5f3bf38ca687929f50b07f80982cc5f501caf008dfa03611f5bb8c5',both_explicit_opaque_flags=True)
# Strictly retain every other requested opacity check; no blanket missing-item exemption.
for boundary in pins['opacity']:
 selector=boundary.get('selector',boundary['path']).replace('crate::',pins['root_owner']+'::')
 hits=[f for f in decls if name(f)==selector]
 if selector==owner+'program_id':assert not hits;continue
 assert hits and all(f['body']=='Opaque' for f in hits),(boundary,[name(f) for f in hits])
shutil.copy2(src/'registry.llbc',out/'registry.llbc')
cmd=[str(out/'raw') if x==str(src/'raw') else str(out/'registry.llbc') if x==str(src/'registry.llbc') else x for x in pins['aeneas_command']]
pins.update(aeneas_command=cmd,validation_resume='NMX_E006: no Charon rerun; excluded-child reachability verified against prior pinned LLBC',opaque_exclusion_witness=witness)
(out/'NMX_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');shutil.copy2(src/'NMX_DECLARATIONS.json',out/'NMX_DECLARATIONS.json')
r=subprocess.run(cmd,cwd=B,env={**os.environ,'RUSTUP_TOOLCHAIN':'nightly-2026-09-17','RAYON_NUM_THREADS':'1'})
pins['aeneas_exit']=r.returncode;pins['outputs']={str(p.relative_to(out)):sha(p) for p in (out/'raw').rglob('*') if p.is_file()};pins['lock_after']=sha(B/'NMX_registry_r5_src/Cargo.lock');assert pins['lock_after']==pins['lock_before']
assert all(S.sha((B/'NMX_registry_r5_src'/p).read_bytes())==info['sha256'] for p,info in manifest['files'].items())
(out/'NMX_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');print(json.dumps(dict(exit_status=r.returncode,opaque_exclusion_witness=witness)))
raise SystemExit(r.returncode)
