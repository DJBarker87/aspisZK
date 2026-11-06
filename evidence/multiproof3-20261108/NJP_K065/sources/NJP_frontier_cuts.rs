// Remaining native prefixes/control cuts; included only by the owned scratch harness.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJP_rejection_prefix() {
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let nodes:[u8;9216]=kani::any();
 let n:usize=kani::any();let mut i:usize=kani::any();let mut w:usize=kani::any();let mut at:usize=kani::any();let len:usize=kani::any();let k:usize=kani::any();let h:usize=kani::any();
 kani::assume(0<n&&n<=16&&i<=n&&w<=i&&at<=9216&&len<=9216&&k<16&&h<32);
 if cfg!(NJP_exit_class){kani::assume(i==n);}else{kani::assume(i<n&&!(i+1<n&&idx[i+1]==idx[i]^1)&&len<at+32);}
 let oldi=i;let oldw=w;let oldat=at;let oldidx=idx[k];let oldval=val[k][h];
 let mut log=NJP_RowLog{reply:kani::any(),calls:0,kind:0,left:false,i:0,len:0,ptr:core::ptr::null(),coordinate:k,byte:h,observed:oldval,write_calls:0,write_index:0,write_byte:0};
 let result=NJP_binary_row(&mut log,&mut idx,&mut val,n,&nodes[..len],&mut i,&mut w,&mut at);
 if cfg!(NJP_bad_argument){idx[k]^=1;}
 assert_eq!(result,cfg!(NJP_exit_class));assert_eq!(log.calls,0);assert_eq!(log.write_calls,0);
 assert_eq!(i,oldi);assert_eq!(w,oldw);assert_eq!(at,oldat);assert_eq!(idx[k],oldidx);assert_eq!(val[k][h],oldval);
}

struct NJP_LevelControl { before:[usize;18],after:[usize;18],count:usize,stop:usize }
fn NJP_level_boundary(log:&mut NJP_LevelControl,n:usize,i:usize,w:usize)->Option<usize>{
 assert_eq!(i,0);assert_eq!(w,0);assert!(log.count<18);
 let step=log.count;log.before[step]=n;log.count+=1;
 if step==log.stop{return None;}
 let next:usize=kani::any();kani::assume(0<next&&next<=n);log.after[step]=next;Some(next)
}
// The 18-height source controller, with the data-dependent inner loop at its
// staged boundary. Values and inner iterations are NOT certified here.
fn NJP_height_control(log:&mut NJP_LevelControl,mut n:usize)->(bool,usize){
 for _ in 0..super::Arity::Two.levels(){
  let mut w=0;let i=0;
  let Some(next)=NJP_level_boundary(log,n,i,w)else{return(false,n)};
  w=next;n=w;
 }
 (true,n)
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(24)]
fn NJP_height_controller(){
 let n:usize=kani::any();let stop:usize=kani::any();let selected:usize=kani::any();kani::assume(0<n&&n<=16&&stop<=18&&selected<core::cmp::min(stop+1,18));
 let mut log=NJP_LevelControl{before:[0;18],after:[0;18],count:0,stop};
 let (result,final_n)=NJP_height_control(&mut log,n);
 if cfg!(NJP_bad_argument){log.before[selected]^=1;}
 assert_eq!(result,stop==18);assert_eq!(log.count,core::cmp::min(stop+1,18));
 assert_eq!(log.before[selected],if selected==0{n}else{log.after[selected-1]});
 if stop==18{assert_eq!(final_n,log.after[17]);}else{assert_eq!(final_n,log.before[stop]);}
}
struct NJP_EntryControl {calls:usize,n:usize,ptr:*const u32,reply:bool}
fn NJP_well_boundary(log:&mut NJP_EntryControl,idx:&[u32])->bool{log.calls+=1;log.n=idx.len();log.ptr=idx.as_ptr();log.reply}
fn NJP_entry_control(log:&mut NJP_EntryControl,idx:&[u32;16],n:usize,length:usize)->bool{
 if n==0||n>16||!NJP_well_boundary(log,&idx[..n])||length%32!=0{return false;}true
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJP_entry_prefix(){
 let idx:[u32;16]=kani::any();let n:usize=kani::any();let length:usize=kani::any();let reply:bool=kani::any();
 let mut log=NJP_EntryControl{calls:0,n:0,ptr:core::ptr::null(),reply};
 let result=NJP_entry_control(&mut log,&idx,n,length);
 if cfg!(NJP_bad_argument){log.calls^=1;}
 assert_eq!(result,0<n&&n<=16&&reply&&length%32==0);
 assert_eq!(log.calls,usize::from(0<n&&n<=16));
 if log.calls==1{assert_eq!(log.n,n);assert_eq!(log.ptr,idx.as_ptr());}
}
struct NJP_TerminalControl {calls:usize,val_ptr:*const [u8;32],root_ptr:*const u8,reply:bool}
fn NJP_root_boundary(log:&mut NJP_TerminalControl,val:&[[u8;32];16],root:&[u8;32])->bool{
 log.calls+=1;log.val_ptr=val.as_ptr();log.root_ptr=root.as_ptr();log.reply
}
fn NJP_terminal_control(log:&mut NJP_TerminalControl,idx:&[u32;16],val:&[[u8;32];16],root:&[u8;32],n:usize,at:usize,length:usize)->bool{
 n==1&&super::index_at(idx,0)==0&&NJP_root_boundary(log,val,root)&&at==length
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJP_terminal_prefix(){
 let idx:[u32;16]=kani::any();let val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();
 let n:usize=kani::any();let at:usize=kani::any();let length:usize=kani::any();let reply:bool=kani::any();
 let mut log=NJP_TerminalControl{calls:0,val_ptr:core::ptr::null(),root_ptr:core::ptr::null(),reply};
 let mut result=NJP_terminal_control(&mut log,&idx,&val,&root,n,at,length);
 if cfg!(NJP_bad_argument){result=!result;}
 assert_eq!(result,n==1&&idx[0]==0&&reply&&at==length);assert_eq!(log.calls,usize::from(n==1&&idx[0]==0));
 if log.calls==1{assert_eq!(log.val_ptr,val.as_ptr());assert_eq!(log.root_ptr,root.as_ptr());}
}
// Prefix of the frozen sibling arm, ending AT the digest boundary. Runtime
// termination/no suffix is (an); this does not fabricate a Rust Err result.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJP_pending_digest_frame(){
 let mut idx:[u32;16]=kani::any();let val:[[u8;32];16]=kani::any();let nodes:[u8;9216]=kani::any();
 let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let mut at:usize=kani::any();let length:usize=kani::any();let k:usize=kani::any();let h:usize=kani::any();
 kani::assume(0<n&&n<=16&&i<n&&w<=i&&at<=9216&&length<=9216&&at+32<=length&&k<16&&h<32);
 kani::assume(!(i+1<n&&idx[i+1]==idx[i]^1));let old_at=at;let old_idx=idx[k];let old_val=val[k][h];
 let parent=super::index_at(&idx,i)>>super::Arity::Two.bits();
 let sibling=nodes[..length].get(at..at+32).unwrap();at+=32;
 let left=super::index_at(&idx,i)&1==0;
 if cfg!(NJP_bad_argument){idx[k]^=1;}
 assert_eq!(at,old_at+32);assert_eq!(parent,idx[i]>>1);assert_eq!(left,idx[i]&1==0);
 assert_eq!(sibling.as_ptr(),unsafe{nodes.as_ptr().add(old_at)});assert_eq!(sibling.len(),32);
 assert_eq!(idx[k],old_idx);assert_eq!(val[k][h],old_val);
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJP_index_scalar_domain(){
 let x:u32=kani::any();let y:u32=kani::any();kani::assume(x<y&&y<262144);
 let mut parent=x>>1;if cfg!(NJP_bad_argument){parent^=1;}
 assert_eq!(parent as u64,(x as u64)/2);assert_eq!(x&1==0,x%2==0);assert_eq!(y==x^1,x/2==y/2);
}
