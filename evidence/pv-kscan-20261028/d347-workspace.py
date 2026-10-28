from pathlib import Path
import json,collections,hashlib
E=Path(__file__).resolve().parent;C=Path('/private/tmp/pv-kscan-cache-20261028');R='/home/dombarker/project-offloads/codex-pv-kscan-20261028';W=R+'/d347/workspace'
host=json.loads((C/'d347-host-sources.json').read_text());db=json.loads((C/'d347-source-db.json').read_text());ps=json.loads((E/'d347-input.json').read_text())['passes'];rs=json.loads((C/'d347-receipts.json').read_text());plans=json.loads((E/'d347-plans.json').read_text());bindings=json.loads((E/'d347-source-bindings.json').read_text());payload={}
base='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/'
for p,v in host.items():
 if p.startswith(base) and (p[len(base):].startswith(('crates/','tools/')) or p[len(base):] in ['Cargo.toml','Cargo.lock']):payload[W+'/'+p[len(base):]]=v['text']
new=[];num=10
for fam in ['pv-rw-step-20261026','pv-rw18-20261026','pv-rw21-20261027','pv-runjoin8-20261026','pv-runjoin9-20261027','pv-runjoin10-20261027','pv-runjoin11-20261027','pv-srcid3-20261026']:
 groups={}
 for p in ps:
  if p['pass_output'].split('/')[1]!=fam:continue
  r=rs[p['receipt_blob']];m=r['source_sha256'];m={k:v for k,v in m.items() if k.endswith(('.rs','Cargo.toml','Cargo.lock')) and (k.startswith('crates/') or k.startswith('Cargo') or '/proof/' in k and fam.split('-2026')[0] in k)}
  sig=hashlib.sha256(json.dumps(m,sort_keys=True).encode()).hexdigest();groups.setdefault(sig,dict(m=m,ps=[]))['ps'].append(p)
 for g in groups.values():
  name=f'D{num:03}';num+=1;m=g['m'];subset=g['ps'];missing={k:h for k,h in m.items() if h not in db};assert not missing,(name,missing)
  updates={W+'/'+k:db[h]['text'] for k,h in m.items()};upath=R+'/d347/'+name+'/updates.json';payload[upath]=json.dumps(updates)
  if fam.startswith('pv-rw'):
   manifest=W+'/tools/prover-rw-20261023/'+fam.split('-2026')[0]+'/proof/Cargo.toml';extra=['--manifest-path',manifest]
  else:extra=['--manifest-path',W+'/Cargo.toml','-p','aspis-statement']
  cmd=['/home/dombarker/.cargo/bin/cargo','kani',*extra,'--lib','--only-codegen','--keep-temps','-j','4','--output-format','terse','-Z','stubbing','-Z','function-contracts','-Z','unstable-options']
  original=subset[0]['command']
  if '--no-overflow-checks' in original:cmd.append('--no-overflow-checks')
  plans[name]=dict(command=cmd,cwd=W,metadata_dirs=[R+'/d347/cache'],harnesses=[p['harness'] for p in subset],indices=[p['index'] for p in subset],updates_file=upath,source_checks={W+'/'+k:h for k,h in m.items()},env={'CARGO_TARGET_DIR':R+'/d347/cache','CARGO_PROFILE_DEV_OVERFLOW_CHECKS':'false'})
  bindings.append(dict(run=name,indices=plans[name]['indices'],basis='Exact original receipt source_sha256 maps for native crates, package inputs and Cargo.lock; each hash resolved before launch',files=[dict(path=W+'/'+k,sha256=h,origin=db[h]['origin'],kind=db[h]['kind']) for k,h in m.items()]));new.append(name)
(E/'d347-plans.json').write_text(json.dumps(plans,indent=2)+'\n');(E/'d347-source-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n');(C/'d347-workspace-payload.json').write_text(json.dumps(payload));print(new,'payload bytes',sum(len(v) for v in payload.values()))
