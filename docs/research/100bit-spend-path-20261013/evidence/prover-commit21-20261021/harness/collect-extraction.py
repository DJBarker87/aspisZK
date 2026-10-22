from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit21-20261021';host='dombarker@100.108.41.90'
for name,ns in [('sim-tail-owned-v1','AspisR1SimTail21'),('sim-tail-control-v1','AspisR1SimControl21')]:
 d=E/'extraction'/name;d.mkdir(parents=True,exist_ok=True)
 # Rejected templates remain inert .txt files, never imported or promoted.
 result=subprocess.check_output(['ssh',host,'ls '+H+'/extraction/generated-'+name+'/'+ns],text=True)
 for f in result.splitlines():
  if f.endswith('.lean'):subprocess.run(['scp',host+':'+H+'/extraction/generated-'+name+'/'+ns+'/'+f,str(d/(f+'.txt'))],check=True)
for name in ['transcript21-binding.json','control21-binding.json','sim-later-v1-llbc.json','sim-later-v2-llbc.json','sim-tail-owned-v1-llbc.json','sim-tail-control-v1-llbc.json','sim-tail-control-v2-llbc.json']:
 subprocess.run(['scp',host+':'+H+'/'+name,str(E/name)],check=True)
for f in ['transcript-owned21.rs','transcript-control21.rs','tail-control21.rs']:
 subprocess.run(['scp',host+':'+H+'/harness/'+f,str(E/'harness'/f)],check=True)
rows=[]
for f in ['sim.rs','r1_wire.rs','transcript.rs']:
 p=Path('crates/aspis-r1-cost-probe/src')/f
 original=p.read_bytes()
 remote=subprocess.check_output(['ssh',host,'cat '+H+'/src/'+str(p)])
 projected=remote
 inherited=b''
 if f=='sim.rs':
  start=remote.index(b'// Owned reference for exactly one source Coins::coin transition.')
  end=remote.index(b'// Proof-only owned references.',start)
  inherited=remote[start:end]
  assert b'#[cfg(any(kani,aeneas_ref))]' in inherited and b'#[cfg(kani)]' in inherited
  projected=remote[:start]+remote[end:]
 sha=hashlib.sha256(original).hexdigest();assert projected.startswith(original),f
 rows.append(dict(file=str(p),production_sha256=sha,production_size_bytes=len(original),full_sha256=hashlib.sha256(remote).hexdigest(),size_bytes=len(remote),source_body_matches_after_inherited_reference_projection=True,inherited_coin18_sha256=hashlib.sha256(inherited).hexdigest() if inherited else None,projection='Remove inherited proof-only coin_owned18/simcoin18 block before the shipped owned19 module; exact diff retained' if inherited else 'identity'))
(E/'source-prefix-binding.json').write_text(json.dumps(dict(base='ec5946193',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),files=rows,scope='Shipped bodies match after documented inherited coin18 projection; all new additions host-only under cfg(kani/aeneas_ref); no local shipped source modification'),indent=2)+'\n')
