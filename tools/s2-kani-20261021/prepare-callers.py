#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2-kani-20261021'
out=Path(sys.argv[1]);(out/'src').mkdir(parents=True,exist_ok=True)
def item(s,marker):
 a=s.index(marker);b=s.index('{',a);d=1;e=b+1
 while d:
  d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
program='programs/r1-cost-probe/src/lib.rs';candidate='crates/aspis-r1-cost-probe/src/candidate.rs'
sources={p:(R/p).read_text() for p in [program,candidate]}
for p in sources:assert subprocess.check_output(['git','show','b2727acd3:'+p])==(R/p).read_bytes(),p
observer=item(sources[program],'fn observer()')
assert '#[cfg(not(feature="cu-profiling"))] {None}' in observer
# Exact cfg-off branch selection only. Other complete bodies remain unchanged.
selected='fn observer()->verifier::Observer {None}'
first=item(sources[program],'fn first_decoded(')
tx2=item(sources[candidate],'pub fn tx2<')
auth=item(sources[candidate],'pub fn tx2_authenticated<')
code=(R/'tools/s2-kani-20261021/caller-prelude.rs').read_text()+'\n'+selected+'\n'+first+'\n'+tx2+'\n'+auth+'\n'+(R/'tools/s2-kani-20261021/caller-harness.rs').read_text()
(out/'src/lib.rs').write_text(code);(out/'Cargo.toml').write_text('[package]\nname="aspis-s2-callers-kani"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
manifest=dict(schema='s2-caller-source-cut-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in sources},exact_bodies=dict(observer_before_cfg=observer,observer_off=selected,first_decoded=first,tx2=tx2,tx2_authenticated=auth),code_sha256=hashlib.sha256(code.encode()).hexdigest(),qualification='Universal success/failure controls at opaque child boundaries. Trace preserves exact slice addresses/lengths, semantic token, k and None observer. Not equality of child implementations or AccountInfo execution.')
(out/'source-cut.json').write_text(json.dumps(manifest,indent=2)+'\n');(E/'caller-source-cut.json').write_text(json.dumps(manifest,indent=2)+'\n')
