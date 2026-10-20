#!/usr/bin/env python3
"""Inverse audit the exact universally equal c5 source clients in finish frames."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['extract-canonical-field-stream.py','extract-canonical-dot-clients.py','extract-canonical-dot-partials.py']:
 subprocess.run(['python3',str(tool/name),'--check'],check=True,capture_output=True)
rev='e58b87665233febecc1b1a75c506eac1a8b72e00';parent='d11f9b2fcbddf68fd1ffec297f987de0aa95a6c0';frozen='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
def read(rev,path):return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
def item(raw,anchor):
 p=raw.index(anchor);i=raw.index(b'{',p);j=i+1;d=1
 while d:d+=(raw[j]==123)-(raw[j]==125);j+=1
 return raw[p:j]
plain=(tool/'canonical-field-stream-input/fragments/old-region.rs').read_bytes()
partials=(tool/'canonical-dot-clients-input/fragments/old-partials.rs').read_bytes()
high=(tool/'canonical-dot-clients-input/fragments/old-high.rs').read_bytes()
final=(tool/'canonical-dot-clients-input/fragments/old-final.rs').read_bytes()
records={}
for r in [parent,rev,frozen]:
 weights=read(r,'crates/aspis-r1-cost-probe/src/weights.rs');verifier=read(r,'crates/aspis-r1-cost-probe/src/verifier.rs')
 pair=item(weights,b'    pub fn pair(');start=pair.index(b'        let mut scratch=');end=pair.index(b'        if folds==1 {',start);point=pair[start:end]
 replacements=[(plain+b'                parts[kind]=scale.mul(pair.finish());',b'                let source_pair=SOURCE_PLAIN(f,&scratch,n)?;\n                parts[kind]=scale.mul(source_pair);'),(partials,b'            let (partials,SOURCE_HIGH)=SOURCE_SHARED(f,&common)?;\n'),(high,b'                let source_high=SOURCE_HIGH(&self.factors[k][4])?;\n')]
 factored=point
 for old,new in replacements:assert factored.count(old)==1,(r,'point source occurrence');factored=factored.replace(old,new)
 assert factored.count(b'scale.mul(high.finish())')==1
 factored=factored.replace(b'scale.mul(high.finish())',b'scale.mul(source_high)')
 inverse=factored.replace(b'scale.mul(source_high)',b'scale.mul(high.finish())')
 for old,new in reversed(replacements):inverse=inverse.replace(new,old)
 assert inverse==point
 assert b'for kind in [1usize,2,3,5,6]'in factored
 assert b'for (kind,k) in [(1usize,0usize),(3usize,2usize)]'in factored
 finish=item(verifier,b'pub fn finish_relation(');start=finish.index(b'    crate::trace::value(16,0,pair)');tail=finish[start:]
 piece=final+b'    let actual=dot.finish();';marker=b'    let actual=SOURCE_FINAL(v.final_message,&a.weights)?;'
 assert tail.count(piece)==1
 finalframe=tail.replace(piece,marker);assert finalframe.replace(marker,piece)==tail
 # High callback is used only on the same actual partial values it closes over;
 # source field tensors/scalars stay raw and retain all original checked-q work.
 assert b'common[j]'in partials and b'field(f,16*s+j)'in partials
 records[r]=dict(point_source_sha256=sha(point),point_factored_sha256=sha(factored),final_source_sha256=sha(tail),final_factored_sha256=sha(finalframe),whole_pair_sha256=sha(pair),whole_finish_relation_sha256=sha(finish),inverse_substitution_checked=True)
 out=tool/'retained-finish-dot-source'
 for n,b in [('point-'+r+'.source.rs',point),('point-'+r+'.factored.rs',factored),('final-'+r+'.source.rs',tail),('final-'+r+'.factored.rs',finalframe)]:
  p=out/n
  if a.check:assert p.read_bytes()==b,n
  else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
assert len({x['point_source_sha256']for x in records.values()})==1
assert len({x['final_source_sha256']for x in records.values()})==1
report=dict(candidate=rev,parent=parent,production=frozen,source_frames=records,clients=dict(plain='field_stream(f,&scratch,n)',shared='actual shared_partials(f,&common), then original two k=0/2 high calls on exactly those partials',final='final_stream(v.final_message,&a.weights)'),all_scalar_inputs_remain_raw=True,source_field_decoder='actual unchanged weights.field',shared_high_wide_origin='actual strict-field row dots finish; source_canonical +caller_context derive internally',fallback='Same globally equal source client dictionary plugs the identical non-S2 point/final source frames; no S2-only canonicality assumption.',scope='No re-extraction of unchanged enclosing loops: unconditional complete source-client function equality and kernel congruence for the exact inverse-audited computational source-call frames. Original row order, tensor/scale/storage operations, field and scalar indices, traces/marks/guards, errors and divergence remain in the source frames.')
p=ev/'RETAINED-FINISH-DOT-SOURCE.json';b=json.dumps(report,indent=2)+'\n'
if a.check:assert p.read_text()==b
else:p.write_text(b)
print(json.dumps(dict(check=a.check,point_and_final_frames=3,inverse_checked=True,field_origins_internal=True)))
