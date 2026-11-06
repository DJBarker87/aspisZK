from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/state_only_poseidon.rs'],text=True)
a=s.index('fn interpolated_full_pair_packed(');b=s.index('\nfn interpolated_internal_pair(',a);body=s[a:b]
body=body.replace('fn interpolated_full_pair_packed(', 'fn NKG_full_pair(').replace('    local: &[QM31; 16],','    local: &[QM31; 16], log: &mut NKG_FullLog,').replace('interpolate_three_constant_columns(', 'NKG_columns(log,').replace('full_round_packed(full_round(state, even), odd)','{let middle=NKG_full(log,state,even);NKG_full_packed(log,middle,odd)}')
h='''
struct NKG_FullLog { weights:[[QM31;3];2],columns:[[[u32;16];3];2],replies:[[QM31;16];2],calls:usize,states:[[QM31;16];2],constants:[[QM31;16];2],middle:[QM31;16],packed:[QM31;4],round_calls:usize }
fn NKG_columns(log:&mut NKG_FullLog,w:[QM31;3],a:[u32;16],b:[u32;16],c:[u32;16])->[QM31;16]{let k=log.calls;assert!(k<2);log.weights[k]=w;log.columns[k]=[a,b,c];log.calls+=1;log.replies[k]}
fn NKG_full(log:&mut NKG_FullLog,s:[QM31;16],c:[QM31;16])->[QM31;16]{assert_eq!(log.round_calls,0);log.states[0]=s;log.constants[0]=c;log.round_calls=1;log.middle}
fn NKG_full_packed(log:&mut NKG_FullLog,s:[QM31;16],c:[QM31;16])->[QM31;4]{assert_eq!(log.round_calls,1);log.states[1]=s;log.constants[1]=c;log.round_calls=2;log.packed}
'''+body+'''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn NKG_full_calls(){
 let s:[QM31;16]=core::array::from_fn(|_|NKG_q());let l:[QM31;16]=core::array::from_fn(|_|NKG_q());
 let replies:[[QM31;16];2]=core::array::from_fn(|_|core::array::from_fn(|_|NKG_q()));let middle:[QM31;16]=core::array::from_fn(|_|NKG_q());let packed:[QM31;4]=core::array::from_fn(|_|NKG_q());
 let mut log=NKG_FullLog{weights:[[QM31::ZERO;3];2],columns:[[[0;16];3];2],replies,calls:0,states:[[QM31::ZERO;16];2],constants:[[QM31::ZERO;16];2],middle,packed,round_calls:0};
 let call:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let g:usize=kani::any();kani::assume(call<2&&j<3&&k<16&&g<4);
 let mut out=NKG_full_pair(s,&l,&mut log);
 if cfg!(NKG_bad_output){out[g].c0.a.0^=1;}
 if cfg!(NKG_bad_argument){log.weights[call][j].c0.a.0^=1;}
 assert_eq!(log.calls,2);assert_eq!(log.round_calls,2);
 assert_eq!(NKG_words(log.weights[call][j]),NKG_words(l[[1,9,10][j]]));
 assert_eq!(log.columns[call][j][k],if j==0{EXTERNAL_INITIAL[2+call][k]}else{EXTERNAL_FINAL[2*(j-1)+call][k]});
 assert_eq!(NKG_words(log.states[0][k]),NKG_words(s[k]));assert_eq!(NKG_words(log.states[1][k]),NKG_words(middle[k]));
 assert_eq!(NKG_words(log.constants[call][k]),NKG_words(replies[call][k]));assert_eq!(NKG_words(out[g]),NKG_words(packed[g]));
}
'''
(E/'NKG_full_native.rs').write_text(h)
p=E/'NKG_build_native.py';t=p.read_text();needle="p+=(E/'NKG_internal_native.rs').read_text()";t=t.replace(needle,needle+"\np+=(E/'NKG_full_native.rs').read_text()") if 'NKG_full_native.rs' not in t else t;p.write_text(t)
base=json.loads((E/'NKG_K001.json').read_text())
for n,cfg in [(14,None),(15,'NKG_bad_output'),(16,'NKG_bad_argument')]:
 x=json.loads(json.dumps(base).replace('NKG_K001',f'NKG_K{n:03}'));x['module']='NKG_full_calls';x['native_command'][x['native_command'].index('--harness')+1]='state_only_poseidon::NKG_native::NKG_full_calls';x['expected_failure']=cfg is not None
 if cfg:x['env']['RUSTFLAGS']+=' --cfg '+cfg
 x['expected_time']='Full-pair source-ordered interpolation/round call arguments and complete return, no arithmetic';(E/(x['attempt']+'.json')).write_text(json.dumps(x,indent=2)+'\n')
