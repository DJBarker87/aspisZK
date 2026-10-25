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
// Default-check pointer/owner coupling only. This run does not establish
// initialization; that is checked by the separate uninit-enabled raw loop.
#[kani::proof]
#[kani::unwind(32)]
fn box_projection_transfer(){
 let rows=[row(),row(),row()];let j=(kani::any::<u8>()%87)as usize;
 let layout=alloc::alloc::Layout::new::<Claims>();assert!(layout.size()==1392);assert!(layout.align()==4);
 let raw=unsafe{alloc::alloc::alloc(layout)};if raw.is_null(){return;}
 unsafe{
  let mut out=alloc::boxed::Box::from_raw(raw.cast::<core::mem::MaybeUninit<Claims>>());
  let base=out.as_mut_ptr();assert!(base.cast::<u8>()==raw);
  for p in 0..3 {out.as_mut_ptr().cast::<[QM31;29]>().add(p).write(rows[p]);}
  let initialized=out.assume_init();
  let owner=(&*initialized as *const Claims).cast::<u8>();assert!(owner==raw);
  let actual=owner.cast::<QM31>().add(j).read();let expected=rows[j/29][j%29];
  assert!(actual.c0.a==expected.c0.a);assert!(actual.c0.b==expected.c0.b);
  assert!(actual.c1.a==expected.c1.a);assert!(actual.c1.b==expected.c1.b);
  drop(initialized);
 }
 kani::cover!(j==0,"first cell with real Box projection/transfer");
 kani::cover!(j==86,"last cell with real Box projection/transfer");
}
