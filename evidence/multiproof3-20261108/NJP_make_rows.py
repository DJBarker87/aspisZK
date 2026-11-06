from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
old=E.parent/'multiproof2-20261107/NJE_harness.rs'
s=old.read_text();start=s.index('struct NJE_RowLog');end=s.index('#[kani::proof]',start)
body=s[start:end].replace('NJE_','NJP_')
body=body.replace('observed:u8}', 'observed:u8,first:u8,second:u8}')
body=body.replace('log.calls+=1;log.kind=1;', 'log.first=val[i][log.byte];log.second=val[i+1][log.byte];log.calls+=1;log.kind=1;')
body=body.replace('log.calls+=1;log.kind=2;', 'log.first=val[i][log.byte];log.second=sibling[log.byte];log.calls+=1;log.kind=2;')
body=body.replace('second:u8}', 'second:u8,write_calls:usize,write_index:usize,write_byte:u8}')
body=body.replace('val[*w]=digest;', 'if cfg!(NJP_write_stage){NJP_digest_write_record(log,val,*w,digest);}else{val[*w]=digest;}')
body+='\nfn NJP_digest_write_record(log:&mut NJP_RowLog,val:&mut[[u8;32];16],w:usize,digest:[u8;32]) {\n assert_eq!(val[log.coordinate][log.byte],log.observed);\n log.write_calls+=1;log.write_index=w;log.write_byte=digest[log.byte];\n}\n'

proof='''
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJP_binary_row_window(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let nodes:[u8;9216]=kani::any();
 let n:usize=kani::any();let mut i:usize=kani::any();let mut w:usize=kani::any();let mut at:usize=kani::any();let len:usize=kani::any();let k:usize=kani::any();let h:usize=kani::any();
 kani::assume(0<n&&n<=16&&i<n&&w<=i&&at<=9216&&len<=9216&&k<16&&h<32);
 let paired=i+1<n&&idx[i+1]==idx[i]^1;
 if cfg!(NJP_pair_class){kani::assume(paired);}else{kani::assume(!paired&&at+32<=len);}
 let oldi=i;let oldw=w;let oldat=at;let beforeidx=idx[k];let beforeval=val[k][h];let parent=idx[i]>>1;let left=idx[i]&1==0;
 let first=val[i][h];let second=if paired{val[i+1][h]}else{nodes[at+h]};
 let reply:[u8;32]=kani::any();let expectedreply=reply[h];let base=nodes.as_ptr();let valuebase=val.as_ptr() as *const u8;
 let mut log=NJP_RowLog{reply,calls:0,kind:0,left:false,i:0,len:0,ptr:core::ptr::null(),coordinate:k,byte:h,observed:beforeval,first:0,second:0,write_calls:0,write_index:0,write_byte:0};
 let theorem:usize=if cfg!(NJP_row_0){0}else if cfg!(NJP_row_1){1}else if cfg!(NJP_row_2){2}else if cfg!(NJP_row_3){3}else if cfg!(NJP_row_4){4}else if cfg!(NJP_row_5){5}else if cfg!(NJP_row_6){6}else if cfg!(NJP_row_7){7}else if cfg!(NJP_row_8){8}else{9};
 if theorem==8{kani::assume(k==oldw);}
 if theorem==9{kani::assume(k!=oldw);}
 let succeeded=NJP_binary_row(&mut log,&mut idx,&mut val,n,&nodes[..len],&mut i,&mut w,&mut at);
 macro_rules! assert_eq {($a:expr,$b:expr)=>{assert!(if cfg!(NJP_bad_argument){$a!=$b}else{$a==$b})}}
 if theorem==0{assert_eq!(succeeded,true);}
 if theorem==1{assert_eq!(log.calls,1);}
 if theorem==2{assert_eq!(log.kind,if paired{1}else{2});assert_eq!(log.i,oldi);assert_eq!(log.ptr,if paired{valuebase}else{unsafe{base.add(oldat)}});assert_eq!(log.len,if paired{16}else{32});}
 if theorem==3{assert_eq!(log.first,first);assert_eq!(log.second,second);if !paired{assert_eq!(log.left,left);}}
 if theorem==4{assert_eq!(i,oldi+if paired{2}else{1});}
 if theorem==5{assert_eq!(w,oldw+1);}
 if theorem==6{assert_eq!(at,oldat+if paired{0}else{32});}
 if theorem==7{assert_eq!(idx[k],if k==oldw{parent}else{beforeidx});}
 if theorem==8{assert_eq!(log.write_calls,1);assert_eq!(log.write_index,oldw);assert_eq!(log.write_byte,expectedreply);}
 if theorem==9{assert_eq!(val[k][h],beforeval);}
}
'''
proof+='\n#[kani::proof]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::unwind(40)]\nfn NJP_digest_write_window() {\n let mut val:[[u8;32];16]=kani::any();let digest:[u8;32]=kani::any();\n let w:usize=kani::any();let k:usize=kani::any();let h:usize=kani::any();\n kani::assume(w<16&&k<16&&h<32);\n if cfg!(NJP_write_inside){kani::assume(k==w);}else{kani::assume(k!=w);}\n let before=val[k][h];let expected=if k==w{digest[h]}else{before};\n val[w]=digest;\n if cfg!(NJP_bad_argument){assert_eq!(val[k][h],expected^1)}else{assert_eq!(val[k][h],expected)}\n}\n'
# Payload at the child boundary is already universally observed by coordinate/byte.
# Full first/second read products timed out K023 and are not repeated.
body=body.replace('log.first=val[i][log.byte];log.second=val[i+1][log.byte];','').replace('log.first=val[i][log.byte];log.second=sibling[log.byte];','').replace(',first:u8,second:u8','')
proof=proof.replace(' let first=val[i][h];let second=if paired{val[i+1][h]}else{nodes[at+h]};','').replace(',first:0,second:0','')
proof=proof.replace('if theorem==3{assert_eq!(log.first,first);assert_eq!(log.second,second);if !paired{assert_eq!(log.left,left);}}','if theorem==3{assert_eq!(log.left,left);}')
proof=proof.replace('macro_rules! assert_eq {', 'if cfg!(NJP_bad_argument)&&theorem==8{log.write_byte^=1;}\n macro_rules! assert_eq {').replace('if cfg!(NJP_bad_argument){$a!=$b}', 'if cfg!(NJP_bad_argument)&&theorem!=8{$a!=$b}')
p=E/'NJP_multiproof.rs';text=p.read_text();marker='\n// Full-range branch cuts imported'
text=text.split(marker)[0]+marker+' from NJE, revalidated on full-range buffers.\n'+body+proof;p.write_text(text)
(E/'NJP_ROW_PROVENANCE.json').write_text(json.dumps({'source':str(old),'source_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),'changes':['full arbitrary node array 96 -> 9216','paired and available sibling branch guards split','selected digest write and disjoint frame split','exact first/second payload bytes logged independently'],'source_body':'NJE_binary_row byte-identical modulo NJP prefix; original frozen one-iteration source erasure reused and checked separately','new_credit':'requires own controls and Lean whole-array/loop composition'},indent=2)+'\n')
for c in range(2):
 for family in range(10):
  for bad in range(2):
   n=17+c*20+family*2+bad;a=f'NJP_K{n:03}';x=json.loads((E/'NJP_K013.json').read_text());x.update(attempt=a,module='NJP_binary_row_window',collect=[a+'_validation'],expected_failure=bool(bad),expected_time=f'ONE full-range arbitrary-prestate {"paired" if c==0 else "sibling"} branch, assertion family {family}; no whole-buffer loop')
   x['command'][-1]=a+'.json';x['native_command'][x['native_command'].index('--harness')+1]='multiproof::NJP_native::NJP_binary_row_window'
   x['env']['RUSTFLAGS']=f'--cfg NJP_write_stage --cfg NJP_row_{family} --cfg '+('NJP_pair_class' if c==0 else 'NJP_sibling_class')+' --cfg '+('NJP_bad_argument' if bad else 'NJP_good_argument')
   if family>=8 and c==0:
    x['module']='NJP_digest_write_window';x['native_command'][x['native_command'].index('--harness')+1]='multiproof::NJP_native::NJP_digest_write_window'
    x['env']['RUSTFLAGS']='--cfg '+('NJP_write_inside' if family==8 else 'NJP_write_outside')+' --cfg '+('NJP_bad_argument' if bad else 'NJP_good_argument')
   if c==1 and family>=8:
    x['module']='NJP_binary_row_window';x['native_command'][x['native_command'].index('--harness')+1]='multiproof::NJP_native::NJP_binary_row_window'
    x['env']['RUSTFLAGS']='--cfg NJP_write_stage --cfg NJP_row_8 --cfg '+('NJP_pair_class' if family==8 else 'NJP_sibling_class')+' --cfg '+('NJP_bad_argument' if bad else 'NJP_good_argument')
   if n>=25:(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
