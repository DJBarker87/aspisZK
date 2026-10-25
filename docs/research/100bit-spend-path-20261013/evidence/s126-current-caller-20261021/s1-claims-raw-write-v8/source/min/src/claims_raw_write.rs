use aspis_core::field::{QM31,CM31,M31};
type Row=[QM31;29];
type Claims=[Row;3];
fn row()->Row{
 let mut out=[QM31::ZERO;29];let mut i=0;
 while i<29{out[i]=QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}};i+=1;}out
}
fn equal(a:&Row,b:&Row){let mut i=0;while i<29{
 assert!(a[i].c0.a==b[i].c0.a);assert!(a[i].c0.b==b[i].c0.b);
 assert!(a[i].c1.a==b[i].c1.a);assert!(a[i].c1.b==b[i].c1.b);i+=1;}}
// The exact row-pointer cast/add/write chain used by the frozen Claims loop,
// starting at an allocated raw Claims pointer. The MaybeUninit Box's pointer
// projection, allocator errors, decoder and ownership transfer are NOT here.
unsafe fn write_row(out:*mut Claims,p:usize,value:Row){unsafe{
 out.cast::<[QM31;29]>().add(p).write(value);
}}
#[kani::proof]
#[kani::unwind(32)]
fn raw_row_initializes(){
 let value=row();let p=(kani::any::<u8>()%3)as usize;
 let layout=alloc::alloc::Layout::new::<Claims>();
 let raw=unsafe{alloc::alloc::alloc(layout)};
 if raw.is_null(){return;}
 unsafe{let out=raw.cast::<Claims>();write_row(out,p,value);
  // Reading only the written row must pass uninitialized-memory checking.
  let actual=out.cast::<Row>().add(p).read();equal(&actual,&value);
  alloc::alloc::dealloc(raw,layout);}
 kani::cover!(p==0,"first raw row initialized");
 kani::cover!(p==1,"middle raw row initialized");
 kani::cover!(p==2,"last raw row initialized");
}
#[kani::proof]
#[kani::unwind(32)]
fn raw_row_frame(){
 let before=[row(),row(),row()];let value=row();let p=(kani::any::<u8>()%3)as usize;
 let layout=alloc::alloc::Layout::new::<Claims>();let raw=unsafe{alloc::alloc::alloc(layout)};
 if raw.is_null(){return;}
 unsafe{let out=raw.cast::<Claims>();out.write(before);write_row(out,p,value);
  let actual=out.read();let mut k=0;while k<3{
   if k==p{equal(&actual[k],&value);}else{equal(&actual[k],&before[k]);}k+=1;}
  alloc::alloc::dealloc(raw,layout);}
 kani::cover!(p==1,"one actual raw store preserves both neighboring rows");
}
#[kani::proof]
#[kani::unwind(32)]
fn raw_three_rows_initialize(){
 let rows=[row(),row(),row()];let layout=alloc::alloc::Layout::new::<Claims>();
 let raw=unsafe{alloc::alloc::alloc(layout)};if raw.is_null(){return;}
 unsafe{let out=raw.cast::<Claims>();let mut p=0;while p<3{write_row(out,p,rows[p]);p+=1;}
  let actual=out.read();let mut k=0;while k<3{equal(&actual[k],&rows[k]);k+=1;}
  alloc::alloc::dealloc(raw,layout);}
 kani::cover!(true,"all raw Claims words initialized before typed read");
}
#[kani::proof]
#[kani::unwind(32)]
fn raw_missing_write_negative(){
 let layout=alloc::alloc::Layout::new::<Claims>();let raw=unsafe{alloc::alloc::alloc(layout)};
 if raw.is_null(){return;}
 unsafe{let out=raw.cast::<Claims>();
  // Deliberately missing write: automatic uninit check must reject this read.
  let actual=out.cast::<Row>().read();assert!(actual[0].c0.a.0==0);
  alloc::alloc::dealloc(raw,layout);}
}
// Narrowed after v2's 2GiB aggregate watchdog: no symbolic row-pointer offset
// over a three-row object, and one arbitrary QM31 read instead of 29 reads.
#[kani::proof]
#[kani::unwind(32)]
fn single_row_arbitrary_cell_initializes(){
 let value=row();let i=(kani::any::<u8>()%29)as usize;
 let layout=alloc::alloc::Layout::new::<Row>();
 assert!(layout.size()==464);assert!(layout.align()==4);
 assert!(core::mem::size_of::<QM31>()==16);
 assert!(core::mem::size_of::<CM31>()==8);assert!(core::mem::size_of::<M31>()==4);
 assert!(core::mem::offset_of!(QM31,c0)==0);assert!(core::mem::offset_of!(QM31,c1)==8);
 assert!(core::mem::offset_of!(CM31,a)==0);assert!(core::mem::offset_of!(CM31,b)==4);
 let raw=unsafe{alloc::alloc::alloc(layout)};if raw.is_null(){return;}
 unsafe{let out=raw.cast::<Row>();out.write(value);
  let actual=out.cast::<QM31>().add(i).read();
  assert!(actual.c0.a==value[i].c0.a);assert!(actual.c0.b==value[i].c0.b);
  assert!(actual.c1.a==value[i].c1.a);assert!(actual.c1.b==value[i].c1.b);
  alloc::alloc::dealloc(raw,layout);}
 kani::cover!(i==0,"first QM31 initialized");kani::cover!(i==28,"last QM31 initialized");
}
#[kani::proof]
#[kani::unwind(32)]
fn three_rows_arbitrary_cell_initializes(){
 let rows=[row(),row(),row()];let j=(kani::any::<u8>()%87)as usize;
 let layout=alloc::alloc::Layout::new::<Claims>();assert!(layout.size()==1392);assert!(layout.align()==4);
 let raw=unsafe{alloc::alloc::alloc(layout)};if raw.is_null(){return;}
 unsafe{let out=raw.cast::<Claims>();
  // Finite expansion of the original p=0,1,2 schedule. No zero initialization.
  write_row(out,0,rows[0]);write_row(out,1,rows[1]);write_row(out,2,rows[2]);
  let actual=out.cast::<QM31>().add(j).read();let expected=rows[j/29][j%29];
  assert!(actual.c0.a==expected.c0.a);assert!(actual.c0.b==expected.c0.b);
  assert!(actual.c1.a==expected.c1.a);assert!(actual.c1.b==expected.c1.b);
  alloc::alloc::dealloc(raw,layout);}
 kani::cover!(j==0,"first Claims cell initialized");
 kani::cover!(j==86,"last Claims cell initialized");
}
