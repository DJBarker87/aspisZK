from pathlib import Path
import subprocess,json,re,hashlib,os
p=Path(__file__).resolve().parent
cargo='/home/dombarker/.cargo/bin/cargo'
meta=json.loads(subprocess.check_output([cargo,'+1.94.1','metadata','--offline','--format-version','1'],cwd=p))
client=json.load(open(p.parent/'client-metadata.json'))
def zfeatures(m):
 z=next(v for v in m['packages'] if v['name']=='zeroize')
 return z,next(v['features'] for v in m['resolve']['nodes'] if v['id']==z['id'])
z,features=zfeatures(meta);cz,cf=zfeatures(client)
assert z['version']==cz['version']=='1.9.0' and features==cf,(features,cf)
commands=[[cargo,'+1.94.1','rustc','--offline','--locked','--release','-j','4','--lib','--','--emit=llvm-ir'],[cargo,'+1.94.1','test','--offline','--locked','--release','-j','4']]
for i,cmd in enumerate(commands):
 with (p/f'command-{i}.log').open('w') as out:
  r=subprocess.run(cmd,cwd=p,stdout=out,stderr=subprocess.STDOUT)
 assert r.returncode==0,(cmd,r.returncode)
q=next((p/'target/release/deps').glob('pv_rjdec_zeroize_probe-*.ll'));ir=q.read_text()
functions={}
for name in ['rjdec_zeroize_byte','rjdec_zeroize_array','rjdec_legacy_byte_control']:
 match=re.search(r'^define [^\n]*@'+name+r'\([^\n]*\).*?^}',ir,re.M|re.S);assert match,name
 body=match[0];(p/(name+'.ll.txt')).write_text(body+'\n')
 functions[name]=dict(volatile_stores=len(re.findall(r'store volatile',body)),compiler_fences=len(re.findall(r'\bfence\s+syncscope\("singlethread"\)\s+seq_cst',body)),asm_calls=len(re.findall(r'asm sideeffect',body)),sha256=hashlib.sha256(body.encode()).hexdigest())
assert functions['rjdec_zeroize_byte']['compiler_fences']==0
assert functions['rjdec_zeroize_byte']['volatile_stores']==1
assert functions['rjdec_zeroize_byte']['asm_calls']==1
assert functions['rjdec_legacy_byte_control']['compiler_fences']==1
assert functions['rjdec_legacy_byte_control']['volatile_stores']==1
src=Path(z['manifest_path']).parent/'src';sources={n:dict(path=str(src/n),sha256=hashlib.sha256((src/n).read_bytes()).hexdigest()) for n in ['lib.rs','barrier.rs']}
(p/'result.json').write_text(json.dumps(dict(evidence_class='deployed-helper source/LLVM diagnostic; finite value validation; no full native correspondence',toolchain=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-Vv'],text=True),target='x86_64-unknown-linux-gnu',zeroize_version=z['version'],zeroize_features=features,deployed_zeroize_features=cf,commands=commands,release=dict(opt_level=3,overflow_checks=False,debug_assertions=False),functions=functions,sources=sources,all_crate_features={n['id']:n['features'] for n in client['resolve']['nodes']},print_axioms='N/A native source/LLVM diagnostic; no Kani'),indent=2)+'\n')
print(json.dumps(functions))
