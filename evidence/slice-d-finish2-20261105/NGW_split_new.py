from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';x=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text());s=x[C+'NGW_new.rs']
a=s.index('fn regular_exercise(');b=s.index('\nstruct CircleLog',a)
s=s[:a]+r'''
fn row(a:K,b:K,log:&mut Products)->[K;4]{[product(K::ONE.sub(a),K::ONE.sub(b),log),product(a,K::ONE.sub(b),log),product(K::ONE.sub(a),b,log),product(a,b,log)]}
fn regular_exercise(g:u8){let a=anyq();let b=anyq();let replies=core::array::from_fn(|_|anyq());let mut log=Products{replies,left:[K::ZERO;4],right:[K::ZERO;4],calls:0};let out=row(a,b,&mut log);let limb:usize=kani::any();kani::assume(limb<4);let term:usize=kani::any();kani::assume(term<4);let left=[K::ONE.sub(a),a,K::ONE.sub(a),a];let right=[K::ONE.sub(b),K::ONE.sub(b),b,b];
 if cfg!(NGW_invert){match g{0..=3=>{let mut w=words(log.left[g as usize]);w[limb]^=1;log.left[g as usize]=q(w)},4=>log.calls+=1,_=>{let mut w=words(log.replies[term]);w[limb]^=1;log.replies[term]=q(w)}}}
 assert!(match g{0..=3=>words(log.left[g as usize])[limb]==words(left[g as usize])[limb]&&words(log.right[g as usize])[limb]==words(right[g as usize])[limb],4=>log.calls==4,_=>words(out[term])[limb]==words(log.replies[term])[limb]});}
fn frame(g:u8){let mut factors=arbitrary();let row:[K;4]=core::array::from_fn(|_|q(kani::any()));let k:usize=kani::any();kani::assume(k<5);let d:usize=kani::any();kani::assume(d<5);let kind:usize=kani::any();kani::assume(kind<5);let dim:usize=kani::any();kani::assume(dim<5);let term:usize=kani::any();kani::assume(term<4);let limb:usize=kani::any();kani::assume(limb<4);let old=words(factors[kind][dim][term])[limb];factors[k][d]=row;let mut expected=if kind==k&&dim==d{words(row[term])[limb]}else{old};if cfg!(NGW_invert){expected^=1;}assert!(words(factors[kind][dim][term])[limb]==expected);let _=g;}
fn lookup(g:u8){let points=core::array::from_fn::<_,3,_>(|_|core::array::from_fn::<_,10,_>(|_|q(kani::any())));let k:usize=kani::any();kani::assume(k<3);let d:usize=kani::any();kani::assume(d<5);let limb:usize=kani::any();kani::assume(limb<4);let a=points[k][9-2*TAU[d]];let b=points[k][8-2*TAU[d]];let t=match d{0=>3,1=>4,2=>2,3=>0,_=>1};let mut expected=words(points[k][9-2*t])[limb];if cfg!(NGW_invert){expected^=1;}assert!(words(a)[limb]==expected&&words(b)[limb]==words(points[k][8-2*t])[limb]);let _=g;}
''' +s[b:]
a=s.index('fn circle_exercise(');b=s.index('fn initial(',a)
circle=s[a:b]
start=circle.index('let mut factors=arbitrary();');end=circle.index('let mut a=anyq();',start)
circle=circle[:start]+'let term:usize=kani::any();kani::assume(term<4);let limb:usize=kani::any();kani::assume(limb<4);'+circle[end:]
circle=circle.replace('circle(&mut factors,k,d,&mut a,&mut log);','let y=dbl(a,&mut log);let out=[K::ONE,a,y,cmul(a,y,&mut log)];a=dbl(y,&mut log);').replace('let mut frame=if kind==3+k&&dim==d{words(expected[term])[limb]}else{old};','let mut frame=words(expected[term])[limb];').replace('factors[3+k][d][term]','out[term]').replace('let out=[K::ONE,a,y,cmul(a,y,&mut log)]','let mut out=[K::ONE,a,y,cmul(a,y,&mut log)]').replace('words(factors[kind][dim][term])[limb]','words(out[term])[limb]')
s=s[:a]+circle+s[b:]
a=s.index('fn initial_exercise(');b=s.index('fn controls(',a)
initial=s[a:b];start=initial.index('let mut factors=arbitrary();');end=initial.index('let p=anyq();',start)
initial=initial[:start]+'let zx=anyq();let zy=anyq();let term:usize=kani::any();kani::assume(term<4);let limb:usize=kani::any();kani::assume(limb<4);'+initial[end:]
initial=initial.replace('let x=initial(&mut factors,k,&z,&mut log);','let mut out=[K::ONE,zy,zx,cmul(zx,zy,&mut log)];let x=dbl(zx,&mut log);').replace('z[k].x','zx').replace('z[k].y','zy').replace('let mut frame=if kind==3+k&&dim==0{words(expected[term])[limb]}else{old};','let mut frame=words(expected[term])[limb];').replace('factors[3+k][0][term]','out[term]').replace('words(factors[kind][dim][term])[limb]','words(out[term])[limb]')
s=s[:a]+initial+s[b:]
s+='gate!(write_frame,frame,0);\ngate!(point_lookup,lookup,0);\n'
x[C+'NGW_new.rs']=s;(E/'NGW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NGW_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()});(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
