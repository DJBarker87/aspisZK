from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(p.read_bytes())
def raw(p):return p.read_bytes()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
rows=[];pins=[];pairs=[]
kmx=H((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes());assert kmx=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
for folder,pre in J(E/'NJW_SPECS.json')[1:]:
 S=E.parent/folder;closed=J(S/f'{pre}_CLOSED.json');attempts={a for f in closed['functions']for pair in f['native_pairs']for a in pair if a.startswith(pre+'_')}
 # NJI Result-shape calibration includes both real/contract positives and three failing controls.
 if pre=='NJI':attempts.update(f'NJI_K{k:03}'for k in[50,51,52,53,54])
 for f in closed['functions']:
  for pair in f['native_pairs']:
   if not all(a.startswith(pre+'_') for a in pair):continue
   positive,negative=pair[:2];x=J(S/positive/'receipt.json');y=J(S/negative/'receipt.json')
   assert x['exit_status']==0 and y['exit_status']==1
   diffs=[k for k in set(x['source_hashes'])|set(y['source_hashes'])if x['source_hashes'].get(k)!=y['source_hashes'].get(k)]
   assert not diffs or (positive=='NJP_K008' and negative=='NJP_K009' and diffs==['NJP_CONTROLLER_SOURCE.json'])
   pairs.append(dict(positive=positive,negative=negative,common_input_differences=diffs,explanation='NJP K008/009 provenance manifest for explicit callback-name stability control; harness/source hash remains unchanged.'if diffs else'Identical complete receipt source hashes.'))
 for a in sorted(attempts):
  p=S/a/'receipt.json';r=J(p);log=raw(S/a/'stdout.log').decode();assert r['exit_status']in[0,1],a
  assert ('VERIFICATION:- SUCCESSFUL'in log if r['exit_status']==0 else 'VERIFICATION:- FAILED'in log),a
  assert 'CARGO_NET_OFFLINE'in str(r['env'])or pre=='NJP',a
  assert r['source_revision']and r['source_hashes']and str(r['swaps'])=='0'
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
  if pre=='NJP':
   v=S/(a+'_validation');g=J(v/'NHR_GRAPH_CHECK.json');lock=J(v/'NJP_LOCK.json');inp=J(v/'NJP_INPUTS.json');assert inp['KMX_patch_sha256']==kmx
   target=v/'NJP_TARGET_GRAPH.json'
   if target.exists():assert J(target)['packages_frozen']and J(target)['lock_unchanged'] and not J(target).get('edge_errors',[])
   fs=[v/'NHR_GRAPH_CHECK.json',v/'NJP_LOCK.json',v/'NJP_INPUTS.json']+([target]if target.exists()else[])
  else:
   gp=S/(a+'-graph-check.json');lp=S/(a+'-lock-check.json');g=J(gp);lock=J(lp);fs=[gp,lp]
   if pre=='NJL':assert H((S/'NJL_KMX.patch').read_bytes())==kmx
   if pre=='NJM':assert H((S/'NJM_KMX.patch').read_bytes())==kmx
   if pre=='NJI':
    inputs=J(S/'NJI_INPUTS.json');gatehash=r['source_hashes']['NIJ_gate.py'];gate=lzma.decompress((S/inputs['objects'][gatehash]['path']).read_bytes());assert H(gate)==gatehash
    assert b'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138' in gate and b'KMX exact patch mismatch' in gate
  assert g['graph_matches_frozen']and not g['edge_errors']and lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  for f in[p]+fs:pins.append(dict(path=str(f.relative_to(E.parents[1])),sha256=H(f.read_bytes())))
  rows.append(dict(attempt=a,exit=r['exit_status'],semantic_verification_reached=True,frozen_graph=True,unchanged_frozen_lock=True,kmx_sha256=kmx,source_revision=r['source_revision'],receipt_sha256=H(p.read_bytes()),features=g.get('selected_closure',g.get('features')),source_hashes=r['source_hashes'],quarantined_function_pointer_or_writable_static_credit=False))
(E/'NJW_NATIVE_REVALIDATION.json').write_text(json.dumps(dict(status='PASS_READ_ONLY_REVALIDATION',new_kani_runs=0,rows=rows,pairs=pairs,input_pins=pins,kmx_patch_sha256=kmx,retained_existing_native_packets='NIX/NJB/NIU/NGK/NJE/NJA/NJG native pairs reused with their committed pins; no duplicate proof or new credit. NJO complete closure and all source/root owner identities preserved.',trust='P6/D188 option A RECLASSIFICATION; no new trust'),indent=1)+'\n')
print(json.dumps(dict(stage='native_revalidation',attempts=len(rows),new_kani_runs=0)))
