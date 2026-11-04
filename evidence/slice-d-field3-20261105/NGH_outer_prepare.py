"""Add independently reviewable reference contracts to the inherited one-step cut."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
s=(E.parent/'slice-d-field2-20261104/NGA_outer.rs.txt').read_text()
assert 'fn step<const N:usize>' in s
attrs='''#[kani::requires(N>=2 && N<=4 && index<N && log.count==0 && canonical(left[index]) && canonical(right[index]))]
#[kani::ensures(|out| out.1==index+1 && log.count==1 && log.before==sums && log.left==left[index] && log.right==right[index] && if cfg!(NGH_invert) {out.0!=log.reply} else {out.0==log.reply})]
#[kani::modifies(log)]
'''
s=s.replace('mut index:usize,log:&mut Log)->','mut index:usize,log:&mut Log,oi:usize,oj:usize)->')
s=re.sub(r'(step(?:[ 	]*::<N>)?\([^;]*?&mut log)\)',r'\1,0,0)',s)
attrs=attrs.replace('N>=2 &&','oi<3 && oj<3 && N>=2 &&').replace('log.before==sums','log.before[oi][oj]==sums[oi][oj]').replace('out.0!=log.reply','out.0[oi][oj]!=log.reply[oi][oj]').replace('out.0==log.reply','out.0[oi][oj]==log.reply[oi][oj]')
s=s.replace('fn step<const N:usize>',attrs+'fn step<const N:usize>')
for n in [2,3,4]:
 # A new contract target, not a renamed rerun of the inherited assertion harness.
 s+=f'''\n#[kani::proof_for_contract(step::<{n}>)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn contract{n}() {{
 let sums=kani::any();let left=core::array::from_fn(|_|any_q());let right=core::array::from_fn(|_|any_q());
 let index=kani::any();let mut log=Log {{before:kani::any(),left:any_q(),right:any_q(),reply:kani::any(),count:0}};
 let oi=kani::any();let oj=kani::any();step::<{n}>(sums,left,right,index,&mut log,oi,oj);
}}
'''
def body(text,name):
 start=text.index('fn '+name);b=text.index('{',start);depth=1;j=b+1
 while depth:depth+=(text[j]=='{')-(text[j]=='}');j+=1
 return text[b+1:j-1]
inherited=(E.parent/'slice-d-field2-20261104/NGA_outer.rs.txt').read_text()
assert body(inherited,'step')==body(s,'step')
assert body(inherited,'cut')==body(s,'cut')
(E/'NGH_outer.rs.txt').write_text(s)
d=json.loads((E/'NGH_NATIVE_INPUTS.json').read_text());d['crates/aspis-core/src/field.rs']+='\n#[cfg(kani)]\n#[path="NGH_outer.rs"]\nmod NGH_outer;\n';d['crates/aspis-core/src/NGH_outer.rs']=s
(E/'NGH_OUTER_INPUTS.json').write_text(json.dumps(d));(E/'NGH_OUTER_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest() for n,t in d.items()},indent=1)+'\n')
(E/'NGH_OUTER_ASSOCIATION.json').write_text(json.dumps(dict(inherited_source_sha256=hashlib.sha256((E.parent/'slice-d-field2-20261104/NGA_outer.rs.txt').read_bytes()).hexdigest(),generated_sha256=hashlib.sha256(s.encode()).hexdigest(),body_change='step body unchanged; two unused observed-cell indices added to signature; projected contract only',added=['reference contract on one outer step','three proof_for_contract instantiations'],domain='2<=N<=4, index<N, fresh local observation count; arbitrary matrix/reply; includes all loop-invariant states',child='accumulation is an arbitrary reply at a named source cut; its semantics remain OPEN'),indent=1)+'\n')
print('Prepared outer-step contracts; inherited cut body unchanged; source suppressed.')
