from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
base='crates/aspis-r1-cost-probe/src/'
source={n:(R/(base+n)).read_text() for n in ['candidate.rs','multiproof.rs','compact.rs']}
compact=lambda s:re.sub(r'\s+','',s)
rows=[('candidate.rs','let at = compact::OFF_OPENINGS + i * OPENING;'),('candidate.rs','&proof[at..at + OPENING]'),('multiproof.rs','if i + 1 < n && index_at(idx, i + 1) == index_at(idx, i) ^ 1 {'),('multiproof.rs','let d = occupied_binary_parent(hash, val, i);'),('multiproof.rs','let d = sibling_binary_parent(hash, val, i, sibling, index_at(idx, i) & 1 == 0);'),('multiproof.rs','idx[w] = parent;'),('multiproof.rs','val[w] = digest;'),('multiproof.rs','w += 1;')]
out=[]
for name,statement in rows:
 assert compact(statement) in compact(source[name]),(name,statement)
 out.append(dict(file=base+name,statement=statement,statement_sha256=hashlib.sha256(statement.encode()).hexdigest(),source_contains=True))
(E/'NBJ_SOURCE_CUTS.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_hashes={base+n:hashlib.sha256(s.encode()).hexdigest() for n,s in source.items()},cuts=out,arity_specialisation='Arity::Two: bits1,width2,levels18; binary lane only; n<=16; both transaction caller domains are inherited/derived, never n<=10',scope='Static exact-statement association only; not a whole-function equivalence proof. Mutations are checked per row/window, model frame/induction separate.'),indent=2)+'\n')
print('checked',len(out),'source statements')
