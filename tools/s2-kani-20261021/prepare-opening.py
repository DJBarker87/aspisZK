#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2-kani-20261021'
out=Path(sys.argv[1]);(out/'src').mkdir(parents=True,exist_ok=True)
def item(s,marker):
 a=s.index(marker);b=s.index('{',a);d=1;e=b+1
 while d:d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
p='crates/aspis-r1-cost-probe/src/verifier.rs';s=(R/p).read_text();assert subprocess.check_output(['git','show','b2727acd3:'+p])==(R/p).read_bytes()
struct=item(s,'pub struct Prepared {');body=item(s,'pub fn new<H:Digest32>(sem:')
code=(R/'tools/s2-kani-20261021/opening-prelude.rs').read_text()+'\n'+struct+'\nimpl Prepared {\n'+body+'\n}\n'+(R/'tools/s2-kani-20261021/opening-harness.rs').read_text()
(out/'src/lib.rs').write_text(code);(out/'Cargo.toml').write_text('[package]\nname="aspis-s2-opening-kani"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
manifest=dict(schema='s2-opening-source-cut-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources={p:hashlib.sha256((R/p).read_bytes()).hexdigest()},exact_bodies=dict(Prepared=struct,new=body),code_sha256=hashlib.sha256(code.encode()).hexdigest(),qualification='Complete Prepared::new shell, S2 only. Transcript/field/claim children are explicit abstract interpreters, not proved implementations. Arbitrary serializer bytes, challenges, query result, query failure and byte probe. Claims only order, payload identity and returned-field plumbing at that boundary; no hash/query/arithmetic refinement.')
(out/'source-cut.json').write_text(json.dumps(manifest,indent=2)+'\n');(E/'opening-source-cut.json').write_text(json.dumps(manifest,indent=2)+'\n')
