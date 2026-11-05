from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/state_only_poseidon.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
body=src[src.index('fn external_linear_lazy('):src.index('// Every row of the four-lane external matrix',src.index('fn external_linear_lazy('))]
# All arithmetic closures/steps are literal source windows. The group-loop cut
# substitutes only the already certified inner row loop at its exact boundary.
start=body.index('                let a =');end=body.index('\n            });',start);matrix=body[start:end]
start=body.index('            let raw =');end=body.index('\n        }',start);row=body[start:end]
start=body.index('        let start =');end=body.index('\n        group += 1;',start)+len('\n        group += 1;');group=body[start:end]
innerstart=group.index('        let mut output = 0usize;');inner=group[innerstart:group.index('\n        group += 1;',innerstart)]
groupcut=group.replace(inner,'        NIH_matrix_rows(state,start,input,log);')
assert groupcut.replace('        NIH_matrix_rows(state,start,input,log);',inner)==group
start=body.index('            u64::from(extension_limbs(state[column])[limb])');end=body.index('\n        })',start);sumexpr=body[start:end]
start=body.index('        let limbs = extension_limbs(state[index]);');end=body.index('\n    }',start);tail=body[start:end]
out='''
fn NIH_matrix_cell(input:[[u32;4];4],output:usize,limb:usize)->u64{
'''+matrix+'''
}
fn NIH_matrix_row(state:&mut[QM31;16],start:usize,input:[[u32;4];4],mut output:usize)->usize{if output<4{
'''+row+'''
}output}
struct NIH_MatrixLog{input:[[u32;4];4],start:usize,reply:[QM31;4],calls:usize}
fn NIH_matrix_rows(state:&mut[QM31;16],start:usize,input:[[u32;4];4],log:&mut NIH_MatrixLog){log.input=input;log.start=start;log.calls+=1;state[start]=log.reply[0];state[start+1]=log.reply[1];state[start+2]=log.reply[2];state[start+3]=log.reply[3];}
fn NIH_matrix_group(state:&mut[QM31;16],mut group:usize,log:&mut NIH_MatrixLog)->usize{if group<4{
'''+groupcut+'''
}group}
fn NIH_column_sum(state:&[QM31;16],column:usize,limb:usize)->u64{
'''+sumexpr+'''
}
fn NIH_external_tail(state:&mut[QM31;16],sums:[[u64;4];4],mut index:usize)->usize{if index<POSEIDON2_WIDTH{
'''+tail+'''
}index}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_lazy_matrix(){let input:[QM31;4]=core::array::from_fn(|_|canonical());let raw=input.map(words);let row:usize=kani::any();let j:usize=kani::any();kani::assume(row<4&&j<4);let out=NIH_matrix_cell(raw,row,j);let a=u64::from(raw[0][j]);let b=u64::from(raw[1][j]);let c=u64::from(raw[2][j]);let d=u64::from(raw[3][j]);let expected=match row{0=>2*a+3*b+c+d,1=>a+2*b+3*c+d,2=>a+b+2*c+3*d,3=>3*a+b+c+2*d,_=>unreachable!()};assert_eq!(out,expected ^ if cfg!(NIH_invert){1}else{0});assert!(out<7*u64::from(P));}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_lazy_row(){let mut state:[QM31;16]=core::array::from_fn(|_|q(kani::any()));let before=state;let input:[QM31;4]=core::array::from_fn(|_|canonical());let raw=input.map(words);let group:usize=kani::any();let output:usize=kani::any();kani::assume(group<4&&output<=4);let next=NIH_matrix_row(&mut state,4*group,raw,output);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);let expected=if output<4&&j==4*group+output{let x=NIH_matrix_cell(raw,output,k);(x%u64::from(P)) as u32}else{words(before[j])[k]};assert_eq!(next,if output<4{output+1}else{4});assert_eq!(words(state[j])[k],expected ^ if cfg!(NIH_invert){1}else{0});}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_lazy_group(){let mut state:[QM31;16]=core::array::from_fn(|_|canonical());let before=state;let reply:[QM31;4]=core::array::from_fn(|_|canonical());let group:usize=kani::any();kani::assume(group<=4);let mut log=NIH_MatrixLog{input:kani::any(),start:kani::any(),reply,calls:0};let next=NIH_matrix_group(&mut state,group,&mut log);let j:usize=kani::any();let k:usize=kani::any();let r:usize=kani::any();kani::assume(j<16&&k<4&&r<4);assert_eq!(next,if group<4{group+1}else{4});assert_eq!(log.calls,if group<4{1}else{0});if group<4{assert_eq!(log.start,4*group);assert_eq!(log.input[r][k],words(before[4*group+r])[k]);}let expected=if group<4&&j>=4*group&&j<4*group+4{words(reply[j-4*group])[k]}else{words(before[j])[k]};assert_eq!(words(state[j])[k],expected ^ if cfg!(NIH_invert){1}else{0});}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_lazy_sum(){let state:[QM31;16]=core::array::from_fn(|_|canonical());let column:usize=kani::any();let limb:usize=kani::any();kani::assume(column<4&&limb<4);let out=NIH_column_sum(&state,column,limb);let expected=u64::from(words(state[column])[limb])+u64::from(words(state[4+column])[limb])+u64::from(words(state[8+column])[limb])+u64::from(words(state[12+column])[limb]);assert_eq!(out,expected ^ if cfg!(NIH_invert){1}else{0});assert!(out<4*u64::from(P));}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_lazy_tail(){let mut state:[QM31;16]=core::array::from_fn(|_|canonical());let before=state;let sums:[[u64;4];4]=core::array::from_fn(|_|core::array::from_fn(|_|{let w:u64=kani::any();kani::assume(w<(1u64<<34));w}));let index:usize=kani::any();kani::assume(index<=16);let next=NIH_external_tail(&mut state,sums,index);let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<4);let expected=if index<16&&j==index{((u64::from(words(before[index])[k])+sums[index&3][k])%u64::from(P)) as u32}else{words(before[j])[k]};assert_eq!(next,if index<16{index+1}else{16});assert_eq!(words(state[j])[k],expected ^ if cfg!(NIH_invert){1}else{0});}
'''
p=E/'NIH_internal.rs.txt';assert 'fn NIH_lazy_matrix'not in p.read_text();p.write_text(p.read_text()+out)
(E/'NIH_EXTERNAL_LAZY_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),matrix=matrix,row=row,group=group,group_cut=groupcut,inner=inner,sum_expression=sumexpr,tail=tail,reverse_erasure=True,modifies='one selected row/lane and cursor; group four local row cells only plus local call log; scalar sum/matrix pure',domains='canonical input operands; group<=4; output<=4; index<=16; column/limb<4; sums<2^34 exactly FJb_ColumnBound caller invariant',stub='NIH_matrix_rows substitutes the SAME four-row inner loop proven by NIH_lazy_row one iteration + JGj_MatrixLoopTotal source induction; native full-group write frame retained, no field product'),indent=2)+'\n')
x=json.loads((E/'NIH_L058.json').read_text());x['sources'].append('NIH_EXTERNAL_LAZY_ERASURE.json');x['module']='external packed/internal round/external lazy source windows';(E/'NIH_L058.json').write_text(json.dumps(x,indent=2)+'\n')
