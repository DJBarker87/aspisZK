const PU: u32 = 0x7fff_ffff;
const PM: u64 = 0x7fff_ffff;
#[inline(always)]
fn red(x: u64) -> u32 {
    let x = (x & PM) + (x >> 31);
    let x = (x & PM) + (x >> 31);
    let x = x as u32;
    if x >= PU { x - PU } else { x }
}
#[inline(always)]
fn mulm(a: u32, b: u32) -> u32 {
    red(a as u64 * b as u64)
}
#[inline(always)]
fn addm(a: u32, b: u32) -> u32 {
    let s = a + b;
    if s >= PU { s - PU } else { s }
}
#[inline(always)]
fn subm(a: u32, b: u32) -> u32 {
    if a >= b { a - b } else { a + PU - b }
}
#[inline(always)]
fn negm(a: u32) -> u32 {
    if a == 0 { 0 } else { PU - a }
}
fn invm(a: u32) -> u32 {
    let mut e=PU-2;let mut b=a;let mut out=1;
    while e>0 {if e&1!=0 {out=mulm(out,b);}b=mulm(b,b);e>>=1;}out
}
/// Lazy-accumulated dot product: each term folded to < 2^32, one reduction.
#[inline]
fn dot(a: &[u32], b: &[u32]) -> u32 {
    debug_assert_eq!(a.len(), b.len());
    let mut s = [0u64; 4];
    let n4 = a.len() / 4 * 4;
    let (a4, ar) = a.split_at(n4);
    let (b4, br) = b.split_at(n4);
    for (x, y) in a4.chunks_exact(4).zip(b4.chunks_exact(4)) {
        for k in 0..4 {
            let p = x[k] as u64 * y[k] as u64;
            s[k] += (p & PM) + (p >> 31);
        }
    }
    let mut t = s[0] % PM + s[1] % PM + s[2] % PM + s[3] % PM;
    for (x, y) in ar.iter().zip(br) {
        let p = *x as u64 * *y as u64;
        t += (p & PM) + (p >> 31);
    }
    red(t)
}
/// v -= s * b  (elementwise, from index `from`).
#[inline]
fn axpy_sub(v: &mut [u32], s: u32, b: &[u32]) {
    let n = core::cmp::min(v.len(), b.len());
    let tiled = n / 8 * 8;
    for (x,y) in v[..tiled].chunks_exact_mut(8).zip(b[..tiled].chunks_exact(8)) {
        for k in 0..8 { x[k] = aspis_r1_cert_check::native_m31::sub_product(x[k],s,y[k]); }
    }
    for (x,y) in v[tiled..n].iter_mut().zip(&b[tiled..n]) {
        *x = aspis_r1_cert_check::native_m31::sub_product(*x,s,*y);
    }
}
fn scale_in(v: &mut [u32], s: u32) {
    for x in v.iter_mut() {
        *x = mulm(*x, s);
    }
}
#[derive(Clone,Debug,PartialEq)]
struct TagEch {
    piv: Vec<Option<usize>>, // column -> row
    rows: Vec<(Vec<u32>, Vec<u32>)>,
    cols: Vec<usize>, // row -> pivot column
}
#[derive(Debug,PartialEq)]
enum Ins {
    Pivot,
    /// The vector reduced to zero: v + sum_p t_p (pivot vector p) = 0.
    Zero(Vec<u32>),
}
impl TagEch {
    fn new(width: usize) -> Self {
        TagEch { piv: vec![None; width], rows: vec![], cols: vec![] }
    }
    fn rank(&self) -> usize {
        self.rows.len()
    }
    /// Insert v (tag = unit on itself). Pivot rows keep tags over pivot indices;
    /// a new pivot takes the next pivot index.
    fn insert(&mut self, v: Vec<u32>) -> Ins {
        if v.len()>=1024 && self.rows.len()>=64 && self.cols.windows(2).all(|w|w[0]<w[1]) {
            self.insert_fixed(v)
        } else {self.insert_serial(v)}
    }
    // Snapshot scalars in increasing pivot-column order. Parallel coordinate
    // blocks replay that exact sequence; no scheduling-dependent arithmetic.
    fn insert_fixed(&mut self, v: Vec<u32>) -> Ins {
        let rank = self.rows.len();
        let mut at: Vec<u32> = self.cols.iter().map(|&c| v[c]).collect();
        let mut factors = vec![0u32; rank];
        for k in 0..rank {
            let s = at[k]; factors[k] = s;
            if s != 0 {
                for j in k..rank {
                    at[j] = subm(at[j], mulm(s,self.rows[k].0[self.cols[j]]));
                }
            }
        }
        let total = v.len()+rank+1;
        let run = |worker: usize| {
            let a=total/4*worker+std::cmp::min(worker,total%4);
            let b=a+total/4+(worker<total%4)as usize;
            let mut out=vec![0u32;b-a];
            for (j,x) in out.iter_mut().enumerate() {
                let i=a+j;
                *x=if i<v.len(){v[i]}else{(i==v.len()+rank)as u32};
            }
            for (k,&s) in factors.iter().enumerate() {
                if s==0 {continue;}
                let (row,tag)=&self.rows[k];
                let va=std::cmp::max(a,self.cols[k]);
                let vb=std::cmp::min(b,v.len());
                if va<vb {axpy_sub(&mut out[va-a..vb-a],s,&row[va..vb]);}
                let ta=std::cmp::max(a,v.len());
                let tb=std::cmp::min(b,v.len()+tag.len());
                if ta<tb {axpy_sub(&mut out[ta-a..tb-a],s,&tag[ta-v.len()..tb-v.len()]);}
            }
            out
        };
        let chunks=std::thread::scope(|scope| {
            let f=&run;
            let h1=scope.spawn(move||f(1));
            let h2=scope.spawn(move||f(2));
            let h3=scope.spawn(move||f(3));
            let c0=run(0);
            [c0,h1.join().unwrap(),h2.join().unwrap(),h3.join().unwrap()]
        });
        let mut combined:Vec<u32>=chunks.into_iter().flatten().collect();
        let mut t=combined.split_off(v.len());
        let mut reduced=combined;
        let next=reduced.iter().position(|&x|x!=0);
        // A pivot before an existing pivot would interleave the original
        // sequence. Re-run the untouched serial algorithm in that case.
        if next.is_some_and(|i|i<*self.cols.last().unwrap()) {
            return self.insert_serial(v);
        }
        if let Some(i)=next {
            let inv=invm(reduced[i]);
            scale_in(&mut reduced[i..],inv);scale_in(&mut t,inv);
            self.piv[i]=Some(rank);self.rows.push((reduced,t));self.cols.push(i);
            Ins::Pivot
        } else {t.truncate(rank);Ins::Zero(t)}
    }
    fn insert_serial(&mut self, mut v: Vec<u32>) -> Ins {
        let mut t = vec![0u32; self.rows.len() + 1];
        let me = self.rows.len();
        t[me] = 1;
        for i in 0..v.len() {
            if v[i] == 0 {
                continue;
            }
            if let Some(k) = self.piv[i] {
                let s = v[i];
                let (b, bt) = &self.rows[k];
                axpy_sub(&mut v[i..], s, &b[i..]);
                axpy_sub(&mut t[..bt.len()], s, bt);
            } else {
                let inv = invm(v[i]);
                scale_in(&mut v[i..], inv);
                scale_in(&mut t, inv);
                self.piv[i] = Some(me);
                self.rows.push((v, t));
                self.cols.push(i);
                return Ins::Pivot;
            }
        }
        // v reduced to 0: t[me] = 1 and 0 = v + sum_{p<me} t_p row-sources.
        t.truncate(me);
        Ins::Zero(t)
    }
    /// Reduce v; Some(y) with v = sum_k y_k (inserted pivot vector k) if v is in the span.
    fn express(&self, mut v: Vec<u32>) -> Option<Vec<u32>> {
        let mut y = vec![0u32; self.rows.len()];
        for i in 0..v.len() {
            if v[i] == 0 {
                continue;
            }
            let k = self.piv[i]?;
            let s = v[i];
            let (b, bt) = &self.rows[k];
            axpy_sub(&mut v[i..], s, &b[i..]);
            // v_old = s * row_k + v_new, row_k = sum bt_e src_e
            for (e, x) in bt.iter().enumerate() {
                y[e] = addm(y[e], mulm(s, *x));
            }
        }
        Some(y)
    }
}
