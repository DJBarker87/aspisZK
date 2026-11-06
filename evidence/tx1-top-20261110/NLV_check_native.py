from pathlib import Path
import re,hashlib,json,subprocess,difflib
E=Path(__file__).resolve().parent
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/candidate.rs'],text=True)
s=(E/'NLV_native.rs.txt').read_text()
def body(text,start):
 a=text.index('{',text.index(start));depth=1;i=a+1
 while depth:
  depth+=(text[i]=='{')-(text[i]=='}');i+=1
 return text[a+1:i-1]
old=body(frozen,'pub fn tx1<');new=body(s,'fn source(')
replacements={'parse_shape(':'log.parse(','canonical_scan(':'log.scan(','prepare(':'log.prepare(','Accumulator::new(':'log.accumulator(','batch_merkle(':'log.batch(','QueryGeometry::for_range(':'log.geometry(','BatchedWeights::new(':'log.pending(','query_loop(':'log.query(','pending.finish(&mut a.weights)':'log.finish(&pending,&mut a.weights)','checkpoint(':'log.checkpoint('}
expected=old
for a,b in replacements.items():expected=expected.replace(a,b)
new=re.sub(r'//[^\n]*','',new)
ghosts=['log.flush_other=acell(&a,1+log.tag%3,log.j);','assert_eq!(acell(&a,1+log.tag%3,log.j),log.flush_other);']
for g in ghosts:
 assert g in new,g;new=new.replace(g,'')
compact=lambda s:''.join(s.split())
ok=compact(new)==compact(expected)
(E/'NLV_NATIVE_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_body_sha256=hashlib.sha256(old.encode()).hexdigest(),native_input_sha256=hashlib.sha256(s.encode()).hexdigest(),child_replacements=replacements,ghost_statements=ghosts,erasure_matches=ok,scope='control body only; no physical producer or child law inferred'),indent=2))
if not ok:
 (E/'NLV_NATIVE_ERASURE.diff').write_text(''.join(difflib.unified_diff(expected.splitlines(True),new.splitlines(True))))
 raise SystemExit('Native erasure mismatch; no launch')
print('Native candidate control-body erasure matches frozen tx1')
