"""Source-footprint check for the outlined parent stage, with negative mutations."""
from pathlib import Path
import re,json,hashlib,subprocess
E=Path(__file__).resolve().parent
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
def compact(s):return re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
source=frozen[frozen.index('        process_regular_kinds(self,shared_two_point,'):frozen.index('        if folds==1 {')]
expected='''process_regular_kinds(self,shared_two_point,alpha,f,folds,n,&ap0,&ap1,&mut scratch,&mut parts)?;
if shared_two_point {let mut common=[K::ZERO;16];for j in 0..16 {common[j]=self.factors[0][2][j&3].mul(self.factors[0][3][j>>2u32]);}
let partials=shared_partials(f,&common)?;shared_high(&partials,self,&ap0,&ap1,&mut parts)?;}'''
assert compact(source)==compact(expected),'frozen parent slice changed'
s=(E/'NJF_boundary.rs.txt').read_text()
def checked(s):
 required=[
 'regular(w,shared,alpha,f,2,64,ap0,ap1,scratch,parts,l)?;',
 'if shared{let common=common(w,l);let partials=partial(f,&common,i,l)?;high(&partials,w,ap0,ap1,parts,slot,power,l)?;}',
 'scratch[i].c0.a.0=l.scratch[i].c0.a.0;', 'scratch[i].c0.b.0=l.scratch[i].c0.b.0;',
 'scratch[i].c1.a.0=l.scratch[i].c1.a.0;', 'scratch[i].c1.b.0=l.scratch[i].c1.b.0;',
 '*parts=l.parts;l.regular','*parts=l.high_parts;l.high',
 'l.partial_message=f.as_ptr();l.partial_message_len=f.len();',
 'l.high_who=w;l.high_ap0=ap0[power];l.high_ap1=ap1[power];',
 'l.high_before=parts[slot];l.high_partial=partials[power];',
 'l.who=w;l.shared=shared;l.alpha=alpha.as_ptr();l.alpha_len=alpha.len();l.message=f.as_ptr();l.message_len=f.len();',
 ]
 return all(compact(x) in compact(s) for x in required) and not re.search(r'static\s+(mut|.*(?:Cell|Atomic|UnsafeCell))',s)
assert checked(s)
mutations=[('shared','regular(w,shared,alpha','regular(w,!shared,alpha'),('message','l.message=f.as_ptr()','l.message=alpha.as_ptr() as *const u8'),('scratch-frame','scratch[i].c1.b.0=l.scratch[i].c1.b.0;',''),('parts-frame','*parts=l.parts;l.regular','parts[2]=l.parts[2];l.regular'),('high','high(&partials,w,ap0,ap1','high(&partials,w,ap1,ap0'),('partial','partial(f,&common,i,l)?','partial(f,&common,i,l).unwrap()')]
rejected=[]
for name,a,b in mutations:
 assert a in s,a
 assert not checked(s.replace(a,b)),name
 rejected.append(name)
(E/'NJF_NATIVE_SHAPE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_source_sha256=hashlib.sha256(frozen.encode()).hexdigest(),outlined_source_sha256=hashlib.sha256(s.encode()).hexdigest(),stage_lines='weights.rs:279-288',rejected_mutations=rejected,full_regular_modifies=['scratch[0..64]','parts[0..7]'],full_high_modifies=['parts[0..7]'],common_loop_packet='NIT_CommonChain / NIW_AlignCommonSource.source',classification='projection check; not a native root proof'),indent=2)+'\n')
print(json.dumps(dict(shape='PASS',rejected_mutations=len(rejected))))
