"""Reviewable fragment/footprint preflight; never a source-to-model proof."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
s=(E/'NIW_boundary.rs.txt').read_text()
assert 'scratch:&mut Vec<K>,parts:&mut [E;7]' in frozen
assert 'process_regular_kinds(self,shared_two_point,alpha,f,folds,n,&ap0,&ap1,&mut scratch,&mut parts)?;' in frozen
assert 'let partials=shared_partials(f,&common)?;' in frozen
assert 'shared_high(&partials,self,&ap0,&ap1,&mut parts)?;' in frozen

def check(t):
 body=t.split('fn boundary(',1)[1].split('#[kani::proof]',1)[0]
 assert 'regular(scratch,parts,l)?;' in body
 assert 'if shared{let common=common(l);let partials=partial(&common,i,l)?;high(&partials,parts,slot,power,l)?;}' in body
 assert '*scratch=l.scratch.take().unwrap();*parts=l.parts;l.regular' in t
 assert 'l.high_before=parts[slot];l.high_partial=partials[power];*parts=l.high_parts;l.high' in t
 assert 'None=>Ok(l.reply.take().unwrap())' in t
 assert 'static mut' not in t and 'stub_verified' not in t and 'Option<fn' not in t
 return True
check(s)
mutations=[('regular error discarded','regular(scratch,parts,l)?;','let _=regular(scratch,parts,l);'),('partial error discarded','partial(&common,i,l)?','partial(&common,i,l).unwrap()'),('high stale state','l.high_before=parts[slot]','l.high_before=l.high_parts[slot]'),('scratch write omitted','*scratch=l.scratch.take().unwrap();',''),('partial wrong common','partial(&common,i,l)?','partial(&l.common,i,l)?'),('NEW move absent','None=>Ok(l.reply.take().unwrap())','None=>Ok(l.reply.unwrap())')]
rejected=[]
for name,old,new in mutations:
 assert old in s
 try:check(s.replace(old,new))
 except AssertionError:rejected.append(name)
 else:raise AssertionError(name)
out=dict(status='PASS_FOOTPRINT_ONLY',frozen_revision='4bb3b3f',frozen_sha256=hashlib.sha256(frozen.encode()).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),rejected=rejected,scope='Two outlined source fragments and explicit log-write footprint; not a frozen whole-parent instrumentation equivalence proof',owner_window='all factor/point/extra words raw arbitrary, no canonicality assumption; factors/rest scopes are separate',setup='disjoint-field Box initialization replaces timed-out whole Weights construction; no memory/time cap change')
(E/'NIW_NATIVE_SHAPE.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],rejected=len(rejected))))
