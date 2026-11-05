"""Reconstruct private frozen workspace and three reviewed scratch modules.
No writes outside NHA-owned evidence and host directory. All frozen inputs are Git objects.
"""
from pathlib import Path
import subprocess,json,re,hashlib,sys
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(p):return subprocess.check_output(['git','show',REV+':'+p],text=True)
def cut(s,name):
 m=re.search(r'(?:pub(?:\([^)]*\))?\s+)?fn '+name+r'\b',s);start=s.rfind('\n',0,m.start())+1;b=s.index('{',m.end());d=1;i=b+1
 while d:
  d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[start:i]
field=frozen('crates/aspis-core/src/field.rs');q=frozen('crates/aspis-core/src/r0_transcript.rs');cl=frozen('crates/aspis-r1-cost-probe/src/verifier.rs')
f=cut(field,'qm31_accumulate_product_channels');qq=cut(q,'queries_from_pairs');c=cut(cl,'prepared_claim')
# Keep originals unchanged in body; only wrapper visibility/name is added.
fs='use crate::field::QM31;\n'+f.replace('fn qm31_accumulate_product_channels','pub fn NHA_original_field',1)+'\n'
inner='''        for channel in 0..3 {
            sums[component][channel] += left_components[component][channel].0 as u64
                * right_components[component][channel].0 as u64;
        }'''
assert inner in f
helper='''fn NHA_channels(mut sums:[[u64;3];3],left_components:[[crate::field::M31;3];3],right_components:[[crate::field::M31;3];3],component:usize)->[[u64;3];3] {
'''+inner+'\n    sums\n}\n'
fo=f.replace('fn qm31_accumulate_product_channels','pub fn NHA_outlined_field',1).replace(inner,'        sums = NHA_channels(sums,left_components,right_components,component);')
fs+=helper+fo+'\n'
# Copy helpers byte-for-byte, no alternate implementation. query_words invokes block_rank.
qs='use crate::transcript::QuerySampleError;\ntype Rank = [u32;8];\nconst QUERY_COUNT:usize=22; const QUERY_BOUND:u32=1<<18; const QUERY_MAX_DRAWS:usize=64;\n'
qs+=cut(q,'block_rank')+'\n'+cut(q,'query_words')+'\n'
start=q.index('#[derive(Default)]\nstruct QueryScan');end=q.index('\nimpl Transcript {',start);qs+=q[start:end]+'\n'
qs+=qq.replace('pub fn queries_from_pairs','pub fn NHA_original_queries',1)+'\n'
# The outer block loop becomes one helper; its inner QueryScan::scan loop is separate already.
loop='''    for k in 0..8 {
        if scan.scan(&blocks[k]) {
            state = advances[k];
            break;
        }
    }'''
assert loop in qq
qs+='''fn NHA_blocks(mut scan:QueryScan,mut state:[u8;32],blocks:&[[u8;32];8],advances:&[[u8;32];8])->(QueryScan,[u8;32]) {
'''+loop+'\n    (scan,state)\n}\n'
qs+=qq.replace('pub fn queries_from_pairs','pub fn NHA_outlined_queries',1).replace(loop,'    (scan,state) = NHA_blocks(scan,state,blocks,advances);')+'\n'
cs='use aspis_core::{Digest32,field::WideExact as E};\nuse crate::{verifier::Error,weights::{powers,field}};\n'+c.replace('fn prepared_claim','pub fn NHA_original_claim',1)+'\n'
innerc='''            for l in 0..29 {
                let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
                dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
            }'''
assert innerc in c
cs+='''fn NHA_dot<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize)->Result<E,Error> {
            let mut dot=crate::fast_pairing::EbyKDot::new();
'''+innerc+'\n            Ok(dot.finish())\n}\n'
co=c.replace('fn prepared_claim','pub fn NHA_outlined_claim',1).replace('''            let mut dot=crate::fast_pairing::EbyKDot::new();
'''+innerc+'''
            parts[point+1]=dot.finish();''','''            parts[point+1]=NHA_dot(sem,y1,g,point)?;''')
assert 'NHA_dot(sem' in co
cs+=co+'\n'
# A second reference isolates the known weighted-sum loop as well.
last='''        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);'''
assert last in co
cs+='''fn NHA_sum(parts:[E;7],k:[E;7])->E {
'''+last+'\n        claim\n}\n'
cs+=co.replace('NHA_outlined_claim','NHA_fully_outlined_claim',1).replace(last,'        let claim=NHA_sum(parts,k);')+'\n'
mods={'crates/aspis-core/src/NHA_field.rs':fs,'crates/aspis-core/src/NHA_queries.rs':qs,'crates/aspis-r1-cost-probe/src/NHA_claim.rs':cs}
for p,s in mods.items():(E/(Path(p).stem+'.rs.txt')).write_text(s)
# Only members/dependencies necessary for the scratch extraction are retained.
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'--','crates','Cargo.toml','Cargo.lock'],text=True).splitlines()
files={p:frozen(p) for p in paths if not p.endswith(('.png','.pdf','.xlsx','.bin','.gz','.zip'))}
root=files['Cargo.toml'];a=root.index('members = [');b=root.index(']',a)+1
root=root[:a]+'''members = ["crates/aspis-core","crates/aspis-statement","crates/aspis-r1-cost-probe","crates/aspis-prover"]'''+root[b:]
files['Cargo.toml']=frozen('Cargo.toml')
for member in ['programs','audit/poseidon-pair-probe/program','xtask','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon','docs/research/v8-r0-zk-20261009/refine/diffharness']:
 for name in subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'--',member],text=True).splitlines():
  if name.endswith(('.rs','.toml','.lock')):files[name]=frozen(name)
# Reconstruct optional path dependencies even when their features are disabled.
import tomllib,posixpath
while True:
 additions=[]
 for name,text in list(files.items()):
  if not name.endswith('Cargo.toml'):continue
  try:doc=tomllib.loads(text)
  except Exception:continue
  def paths(v):
   if isinstance(v,dict):
    if isinstance(v.get('path'),str):yield v['path']
    for z in v.values():yield from paths(z)
   elif isinstance(v,list):
    for z in v:yield from paths(z)
  for rel in paths(doc):
   d=posixpath.normpath(posixpath.join(posixpath.dirname(name),rel))
   if d+'/Cargo.toml' in files:continue
   listing=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'--',d],text=True).splitlines()
   if d+'/Cargo.toml' in listing:additions+=listing
 if not additions:break
 for name in set(additions):
  if name.endswith(('.rs','.toml','.lock')):files[name]=frozen(name)

# Frozen crates may have optional path deps outside these members: preserve all crate sources.
files.update(mods)
files['crates/aspis-core/src/lib.rs']+='\n#[allow(non_snake_case)] pub mod NHA_field;\n#[cfg(feature="r0")] #[allow(non_snake_case)] pub mod NHA_queries;\n'
files['crates/aspis-r1-cost-probe/src/lib.rs']+='\n#[allow(non_snake_case)] pub mod NHA_claim;\n'
manifest={p:{'sha256':hashlib.sha256(t.encode()).hexdigest(),'origin':REV+':'+p if p not in mods else 'NHA scratch module','modified_in_scratch':p in mods or p in ['Cargo.toml','crates/aspis-core/src/lib.rs','crates/aspis-r1-cost-probe/src/lib.rs']} for p,t in files.items()}
(E/'NHA_SCRATCH_INPUTS.json').write_text(json.dumps(manifest,indent=2)+'\n')
if '--upload' in sys.argv:
 # Upload after a separate recorded admission by NHA_run, from its scoped setup command.
 raise RuntimeError('Use NHA_upload_scratch.py client; never execute Rust locally')
print(json.dumps(files))
