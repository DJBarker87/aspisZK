#!/usr/bin/env python3
"""Exact source frame pins for the finish-relation S2 source factoring."""
from pathlib import Path
import subprocess,json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;repo=tool.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest();rev='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
def source(path,r=rev):return subprocess.check_output(['git','-C',str(repo),'show',r+':'+path])
def item(src,mark):
 at=src.index(mark);j=src.index(b'{',at);depth=1;k=j+1
 while depth:
  if src[k:k+1]==b'{':depth+=1
  elif src[k:k+1]==b'}':depth-=1
  k+=1
 return src[at:k]
w=source('crates/aspis-r1-cost-probe/src/weights.rs');v=source('crates/aspis-r1-cost-probe/src/verifier.rs');pair=item(w,b'pub fn pair(');finish=item(v,b'pub fn finish_relation(');ctor=item(w,b'pub fn new(variant:')
assert ctor==item(source('crates/aspis-r1-cost-probe/src/weights.rs','f458169f705f25b04e1e29546c621e4665e0f64c'),b'pub fn new(variant:')
ap=pair.index(b'        let ap0=');point=pair.index(b'        let mut scratch=');one=pair.index(b'        if folds==1 {');two=pair.index(b'            // Two-fold 0/1 row:');low=pair.index(b'            let low:[E;16]=',two);inactive=pair.index(b'            parts[0]=grouped_inactive_pair',low);libra=pair.index(b'            let libra=',inactive);parts4=pair.index(b'            for j in 0..4 {parts[4]=',libra);post=pair.index(b'        #[cfg(feature="prover")]');sumat=pair.index(b'        let k=powers::<7>(kappa);')
segments={'pair_guard':pair[:ap],'actual_ap0_ap1':pair[ap:point],'pointPrefix':pair[point:one],'onefold_common_fallback':pair[one:two],'twofold_comment':pair[two:low],'actual_low':pair[low:inactive],'actual_inactive':pair[inactive:libra],'actual_libra':pair[libra:parts4],'parts4_tail':pair[parts4:post],'prover_only_unselected':pair[post:sumat],'kappa_sum_tail':pair[sumat:]}
assert b''.join(segments.values())==pair
assert b'.push(field(f,j),scratch[j])' in segments['pointPrefix']
assert b'high.push(partials[s]' in segments['pointPrefix']
assert b'let low:[E;16]=core::array::from_fn' in segments['actual_low']
assert b'self.extra' in segments['actual_libra']
assert b'parts[kind]'in segments['kappa_sum_tail']
# Source Weights::pair borrows self and alpha immutably; all writes are to
# owned scratch/parts/partial/dot state, never prepared/weight input fields.
import re
assert not re.search(rb'self\.[A-Za-z_0-9\[\]]+\s*=(?!=)',pair)
weight=finish.index(b'    let weights=Weights::new(');paircall=finish.index(b'    let pair=weights.pair(');tail=finish.index(b'    crate::trace::value(16,0,pair)')
finishparts={'claimPrefix':finish[:weight],'constructor_call':finish[weight:paircall],'pair_call':finish[paircall:tail],'finalTail':finish[tail:]};assert b''.join(finishparts.values())==finish
assert b'dot.push(field(v.final_message,j),*w)' in finishparts['finalTail']
assert b'mark(obs,Phase::Relation)'in finishparts['finalTail'] and b'mark(obs,Phase::Final)'in finishparts['finalTail']
output=dict(revision=rev,constructor_unchanged_from_reference=True,complete_pair_reassembly=True,complete_finish_reassembly=True,constructor_sha256=sha(ctor),pair_fragments={n:dict(sha256=sha(b),source=b.decode())for n,b in segments.items()},finish_fragments={n:dict(sha256=sha(b),source=b.decode())for n,b in finishparts.items()},source_boundaries=['S2 specialization: p.variant=S2 gives folds2; source caller borrows exactly its two-element alpha array. Non-S2 paths are the identical original fallback.','Fixed array alpha[0]/alpha[1] and semantic[8]/semantic[9] reads are always in bounds. Moving their pure checked projections through source structural packing does not change errors/effects.','Constructor storage projects original factors/points fields; actual variant/extra field writes are explicitly reconstructed. Standard owning-allocation/unsafe-field frame: private partially initialized storage never escapes on failure; the fixed private extra copy has no log/allocation/effect and is unread until construction succeeds. No unsafe allocator reproof is asserted.','Actual ap0/ap1 source powers execute before allocation/point-row prefix. Actual low16 executes after that prefix, then inactive helper then Libra helper then original parts4/kappa tail.','Unchanged transaction work has immutable Prepared input and returns only the updated Accumulator. Direct source finishRelation is invoked on work success; errors/divergence bypass it identically.','PointPrefix/finalTail select the exact pinned source fragments. Candidate5 replacement inside them must be separately instantiated from its concrete checked consumers; c3/c14 endpoints alone do not claim candidate5 closure.'],direct_full_finish_aeneas_emission=False,admission='Narrow source factoring/nominal-coordinate interpretation plus standard owning constructor/immutable frame. Common fields are identical computational source fragments, never old/new-equivalence or canonicality laws.',features=['pool-adapter','private-leaf-salts'],excluded_features=['cu-profiling','prover'])
p=tool/'retained-finish-source-admission.json';text=json.dumps(output,indent=2)+'\n'
if a.check:assert p.read_text()==text
else:p.write_text(text)
print(json.dumps(dict(status='PASS',check=a.check,pair_sha256=sha(pair),finish_sha256=sha(finish),explicit_source_factoring_boundary=True)))
