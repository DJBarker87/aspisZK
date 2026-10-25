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
