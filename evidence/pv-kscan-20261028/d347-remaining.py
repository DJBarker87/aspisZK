from pathlib import Path
# Reuse preparation functions without executing their previously prepared plans.
exec(Path(__file__).with_name('d347-small-packages.py').read_text().split("package('D026'")[0])
for name,indices in [('D033',[130]),('D034',[132,134,136,137]),('D035',[133,135]),('D036',[149])]:
 p=next(p for p in ps if p['index']==indices[0]);r=rs[p['receipt_blob']];orig='/home/dombarker/project-offloads/codex-pv-'+('cb3-20261026/source-proof' if name=='D036' else 'cb-20261026/step-proof');overrides={Path(f).name:pinned(h['sha256']) for f,h in r['inputs'].items() if f.startswith(orig+'/') and f.endswith(('.rs','Cargo.toml','Cargo.lock'))};package(name,indices,orig,overrides,'Exact original per-run receipt inputs for selected proof package; native dependency pins in original receipt')
 # Check the native helper bytes that are directly pinned by the original receipt.
 plans[name]['source_checks'].update({f:h['sha256'] for f,h in r['inputs'].items() if '/source/crates/' in f and f in host and h['sha256']==host[f]['sha256']})
# Reuse the one private native workspace and cache, restoring the owner's frozen snapshot.
W=R+'/d347/workspace'
for name,indices,kind in [('D037',[151],'cb3'),('D038',[153,154],'cblib'),('D039',[156],'cblib'),('D040',[158],'cblib')]:
 p=next(p for p in ps if p['index']==indices[0]);r=rs[p['receipt_blob']];orig='/home/dombarker/project-offloads/codex-pv-'+('cb3-20261026/source' if kind=='cb3' else 'cblib-20261027/source');m={f[len(orig)+1:]:h['sha256'] for f,h in r['inputs'].items() if f.startswith(orig+'/')};updates={W+'/'+k:db[h]['text'] for k,h in m.items()};checks={W+'/'+k:h for k,h in m.items()};files=[]
 # Use that exact retained frozen source tree, with only receipt-pinned proof overlays.
 for f,v in host.items():
  if f.startswith(orig+'/'):
   rel=f[len(orig)+1:]
   if not rel.startswith(('crates/','programs/','docs/','tools/','xtask/','audit/')) and rel not in ['Cargo.toml','Cargo.lock']:continue
   if rel not in m:updates[W+'/'+rel]=v['text'];checks[W+'/'+rel]=v['sha256']
 for f,t in updates.items():files.append(dict(path=f,sha256=hashlib.sha256(t.encode()).hexdigest(),origin='exact receipt overlay' if f[len(W)+1:] in m else orig+'/'+f[len(W)+1:]))
 upath=R+'/d347/'+name+'/updates.json';payload[upath]=json.dumps(updates);pkg='aspis-core' if kind=='cb3' else 'aspis-r1-cost-probe';feature='r0,ct-host-prover' if kind=='cb3' else 'ct-host-prover';hpattern='all_carriers' if kind=='cb3' else ('pv_cblib_library_checks' if name=='D038' else 'op36_reject_small' if name=='D039' else 'pop_error_single')
 plans[name]=dict(command=['/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',W+'/crates/'+pkg+'/Cargo.toml','--features',feature,'--lib','--only-codegen','--keep-temps','--harness',hpattern,'-j','4','--output-format','terse'],cwd=W,metadata_dirs=[R+'/d347/cache'],harnesses=[p['harness'] for p in ps if p['index'] in indices],indices=indices,updates_file=upath,source_checks=checks,env={'CARGO_TARGET_DIR':R+'/d347/cache'})
 bindings.append(dict(run=name,indices=indices,basis='Exact original receipt native source hash, with original committed harness overlay; retained owner frozen dependency tree hashes',files=files))
(E/'d347-plans.json').write_text(json.dumps(plans,indent=2)+'\n');(E/'d347-source-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n');(C/'d347-remaining-payload.json').write_text(json.dumps(payload));print('Remaining plans prepared')
