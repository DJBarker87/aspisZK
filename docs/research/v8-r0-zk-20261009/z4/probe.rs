//! Z4a exact computational probe. No Lean and no proof certificate claim.
//! rustc --edition=2021 -C opt-level=3 -C overflow-checks=yes probe.rs -o probe
#![allow(dead_code)]
use field::{CM31, M31, P, QM31};
use r0::{
    basis::natural,
    domain::{child_index, stored_point, FibreIndex, Point, SlotIndex},
    CodeField,
};
use std::time::Instant;
use z4_core::{field, r0};
const N: usize = 1024;
const EXP: [usize; 10] = [1, 3, 5, 7, 9, 11, 15, 17, 19, 21];
const ACTIVE: [u16; 64] = [
    6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6144, 4097, 2048, 6145, 2049, 2048, 6145,
    2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 4097, 6145, 6145, 4097, 26214, 26214, 26214, 26214, 26214, 26214,
    1749,
];
fn inactive(r: usize) -> bool {
    ACTIVE[r / 16] & (1 << (r % 16)) == 0
}
fn eligible(c: usize, r: usize) -> bool {
    if r < 912 {
        return r % 16 >= 13;
    }
    if r < 1008 {
        return !(0..24).any(|l| {
            let b = 912 + 16 * (l / 4) + 1 + 4 * (l % 4);
            (r == b && c <= 8) || r == b + 1
        });
    }
    let r = r - 48;
    !((0..21).any(|l| {
        let b = 864 + 16 * (l / 4) + 1 + 2 * (l % 4);
        (r == b && c <= 8) || r == b + 1 || (r == (b ^ 12) && c < 8)
    }) || (0..3).any(|v| {
        let b = 960 + 2 * v;
        (r == b || r == b + 1 || r == (b ^ 12)) && c <= 10
    }) || (r == 966 && c < 3)
        || (r == 967 && c < 2)
        || (r == 969 && c <= 10)
        || (r == 970 && c < 10))
}
fn q(n: u32) -> QM31 {
    QM31::from_cm31(CM31::from_m31(M31(n)))
}
fn limbs(x: QM31) -> [M31; 4] {
    [x.c0.a, x.c0.b, x.c1.a, x.c1.b]
}
fn tower(k: usize) -> QM31 {
    let mut a = [M31::ZERO; 4];
    a[k] = M31::ONE;
    QM31 {
        c0: CM31::new(a[0], a[1]),
        c1: CM31::new(a[2], a[3]),
    }
}
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0 = self.0.wrapping_mul(0x2545f4914f6cdd1d);
        self.0
    }
    fn m(&mut self) -> M31 {
        M31((self.next() % P as u64) as u32)
    }
    fn q(&mut self) -> QM31 {
        QM31 {
            c0: CM31::new(self.m(), self.m()),
            c1: CM31::new(self.m(), self.m()),
        }
    }
}
fn eq(a: &[QM31; 10], r: usize) -> QM31 {
    a.iter().enumerate().fold(QM31::ONE, |v, (i, x)| {
        v.mul(if r >> (9 - i) & 1 == 1 {
            *x
        } else {
            QM31::ONE.sub(*x)
        })
    })
}
fn points(a: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let mut b = *a;
    let mut carry = QM31::ONE;
    for i in (0..10).rev() {
        let ac = a[i].mul(carry);
        b[i] = a[i].add(carry).sub(ac.add(ac));
        carry = ac;
    }
    let mut c = *a;
    c[6] = QM31::ONE.sub(c[6]);
    c[7] = QM31::ONE.sub(c[7]);
    [*a, b, c]
}
fn circle(t: QM31) -> Point<QM31> {
    let den = QM31::ONE.add(t.mul(t)).try_inv().unwrap();
    Point {
        x: QM31::ONE.sub(t.mul(t)).mul(den),
        y: t.add(t).mul(den),
    }
}
fn evalrow<E: CodeField>(r: usize, z: Point<E>) -> E {
    let v = natural(r / 2, z.x);
    if r % 2 == 0 {
        v
    } else {
        v.mul(z.y)
    }
}
// Streaming elimination, the same pivot convention as ColumnEchelon/CarryEchelon.
struct Ech<E: CodeField> {
    p: Vec<Option<Vec<E>>>,
    rank: usize,
}
impl<E: CodeField> Ech<E> {
    fn new(n: usize) -> Self {
        Self {
            p: vec![None; n],
            rank: 0,
        }
    }
    fn insert(&mut self, mut v: Vec<E>) -> Option<usize> {
        for i in 0..v.len() {
            if v[i] == E::ZERO {
                continue;
            }
            if let Some(b) = &self.p[i] {
                let s = v[i];
                for j in i..v.len() {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
            } else {
                let inv = v[i].try_inv().unwrap();
                for x in &mut v[i..] {
                    *x = x.mul(inv)
                }
                self.p[i] = Some(v);
                self.rank += 1;
                return Some(i);
            }
        }
        None
    }
}
// Return circuits in the raw observation kernel as sparse (row,coefficient) tapes.
fn circuits<E: CodeField>(cols: &[Vec<E>]) -> (usize, Vec<Vec<(usize, E)>>) {
    let n = cols[0].len();
    let mut p: Vec<Option<(Vec<E>, Vec<E>)>> = vec![None; n];
    let mut rank = 0;
    let mut out = vec![];
    for (r, col) in cols.iter().enumerate() {
        let mut v = col.clone();
        let mut tape = vec![E::ZERO; N];
        tape[r] = E::ONE;
        let mut pivot = false;
        for i in 0..n {
            if v[i] == E::ZERO {
                continue;
            }
            if let Some((b, t)) = &p[i] {
                let s = v[i];
                for j in i..n {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
                for j in 0..=r {
                    tape[j] = tape[j].sub(s.mul(t[j]));
                }
            } else {
                let inv = v[i].try_inv().unwrap();
                for x in &mut v[i..] {
                    *x = x.mul(inv)
                }
                for x in &mut tape[..=r] {
                    *x = x.mul(inv)
                }
                p[i] = Some((v, std::mem::take(&mut tape)));
                rank += 1;
                pivot = true;
                break;
            }
        }
        if !pivot {
            out.push(
                tape.into_iter()
                    .enumerate()
                    .filter(|(_, x)| *x != E::ZERO)
                    .collect(),
            );
        }
    }
    (rank, out)
}
fn base_raw(a: &[QM31; 10], z: &[Point<QM31>; 2], queries: &[usize], ood: bool) -> Vec<Vec<M31>> {
    let pts = points(a);
    (0..N)
        .map(|r| {
            let mut v = vec![if inactive(r) { M31::ONE } else { M31::ZERO }];
            for p in pts {
                v.extend(limbs(eq(&p, r)));
            }
            if ood {
                for p in z {
                    v.extend(limbs(evalrow(r, *p)));
                }
            }
            for &u in queries {
                for s in 0..4 {
                    v.push(evalrow(
                        r,
                        stored_point::<M31>(child_index(
                            FibreIndex::new(u).unwrap(),
                            SlotIndex::new(s).unwrap(),
                        )),
                    ));
                }
            }
            v
        })
        .collect()
}
fn ext_raw(a: &[QM31; 10], z: &[Point<QM31>; 2], queries: &[usize], ood: bool) -> Vec<Vec<QM31>> {
    let pts = points(a);
    (0..N)
        .map(|r| {
            let mut v = vec![if inactive(r) { QM31::ONE } else { QM31::ZERO }];
            for p in pts {
                v.push(eq(&p, r));
            }
            if ood {
                for p in z {
                    v.push(evalrow(r, *p));
                }
            }
            for &u in queries {
                for s in 0..4 {
                    v.push(QM31::from_m31(evalrow(
                        r,
                        stored_point::<M31>(child_index(
                            FibreIndex::new(u).unwrap(),
                            SlotIndex::new(s).unwrap(),
                        )),
                    )));
                }
            }
            v
        })
        .collect()
}
// Exact coefficients of f_c(alpha_prefix,X,Boolean_suffix)*eq(prefix,row)*(X or 1-X).
fn round_row(a: &[QM31; 10], r: usize, c: usize) -> Vec<QM31> {
    let family = if c == 10 { 16 } else { 0 };
    let e = if c == 10 { 26 } else { EXP[c] };
    let rot = if c == 10 { QM31::ONE } else { tower(c % 4) };
    let w: Vec<M31> = (0..10)
        .map(|i| M31((3 + 22 * i + family * (17 + 8 * i)) as u32))
        .collect();
    let mut boolean = M31::ZERO;
    for i in 0..10 {
        if r >> (9 - i) & 1 == 1 {
            boolean = boolean.add(w[i])
        }
    }
    let initial = rot.mul_m31(boolean.pow(e as u64));
    let initial = if c == 10 {
        initial.add(QM31::ONE)
    } else {
        initial
    };
    let mut out = vec![initial];
    let mut pref = QM31::ONE;
    for j in 0..10 {
        let mut b = QM31::ZERO;
        for i in 0..j {
            b = b.add(a[i].mul_m31(w[i]))
        }
        for i in j + 1..10 {
            if r >> (9 - i) & 1 == 1 {
                b = b.add(QM31::from_m31(w[i]))
            }
        }
        let mut p = vec![QM31::ONE];
        for _ in 0..e {
            let mut t = vec![QM31::ZERO; p.len() + 1];
            for d in 0..p.len() {
                t[d] = t[d].add(p[d].mul(b));
                t[d + 1] = t[d + 1].add(p[d].mul_m31(w[j]));
            }
            p = t;
        }
        if c == 10 {
            p[0] = p[0].add(QM31::ONE)
        }
        let mut full = vec![QM31::ZERO; 28];
        let bit = r >> (9 - j) & 1;
        for d in 0..p.len() {
            let v = p[d].mul(pref).mul(rot);
            if bit == 1 {
                full[d + 1] = full[d + 1].add(v)
            } else {
                full[d] = full[d].add(v);
                full[d + 1] = full[d + 1].sub(v)
            }
        }
        out.push(full[0]);
        out.extend(&full[2..]);
        pref = pref.mul(if bit == 1 { a[j] } else { QM31::ONE.sub(a[j]) });
    }
    out
}
fn flatten(v: &[QM31]) -> Vec<M31> {
    v.iter().flat_map(|x| limbs(*x)).collect()
}
fn query_sets(rng: &mut Rng) -> Vec<(&'static str, Vec<usize>)> {
    let mut rand = vec![];
    while rand.len() < 22 {
        let n = (rng.next() % (1 << 18)) as usize;
        if !rand.contains(&n) {
            rand.push(n)
        }
    }
    rand.sort_unstable();
    vec![
        ("random", rand),
        ("consecutive", (0..22).collect()),
        ("spaced", (0..22).map(|i| i * 8192).collect()),
        ("paired", (0..11).flat_map(|i| [i, i + (1 << 17)]).collect()),
    ]
}
fn c1(a: &[QM31; 10], z: &[Point<QM31>; 2], sets: &[(&str, Vec<usize>)]) {
    for (name, qs) in sets {
        let raw = base_raw(a, z, qs, true);
        let mut total = 0;
        for c in 0..16 {
            let rows: Vec<usize> = (0..N).filter(|&r| eligible(c, r)).collect();
            let mut e = Ech::new(raw[0].len() - 1);
            let mut open = Ech::new(88);
            for &r in &rows {
                if r == 1023 {
                    continue;
                }
                let v: Vec<M31> = raw[r][1..]
                    .iter()
                    .zip(&raw[1023][1..])
                    .map(|(a, b)| if inactive(r) { a.sub(*b) } else { *a })
                    .collect();
                open.insert(v[20..].to_vec());
                e.insert(v);
            }
            total += e.rank;
            println!("C1 pattern={name} column={c} eligible={} effective={} opened_rank={} rank={} want=108",rows.len(),rows.len()-1,open.rank,e.rank);
        }
        println!("C1_TOTAL pattern={name} rank={total} want=1728 queries={qs:?}");
    }
}
fn check_dimensions(a: &[QM31; 10]) {
    let mut e = Ech::new(1120);
    for j in 0..10 {
        for k in 0..4 {
            let mut v = vec![M31::ZERO; 1120];
            v[(j * 28) * 4 + k] = M31(2);
            for d in 1..28 {
                v[(j * 28 + d) * 4 + k] = M31::ONE
            }
            if j > 0 {
                let mut pow = QM31::ONE;
                for d in 0..28 {
                    for l in 0..4 {
                        let co = limbs(tower(l).mul(pow));
                        v[((j - 1) * 28 + d) * 4 + l] = v[((j - 1) * 28 + d) * 4 + l].sub(co[k]);
                    }
                    pow = pow.mul(a[j - 1]);
                }
            }
            e.insert(v);
        }
    }
    println!(
        "DIM round_ambient=1120 initial_zero_chain_constraints={} displacement_ambient={}",
        e.rank,
        1120 - e.rank
    );
}
fn masks(a: &[QM31; 10], z: &[Point<QM31>; 2], qs: &[usize]) {
    for ood in [false, true] {
        let t = Instant::now();
        let (br, bc) = circuits(&base_raw(a, z, qs, ood));
        let (gr, gc) = circuits(&ext_raw(a, z, qs, ood));
        println!("RAW ood={ood} base_with_balance_rank={br} base_kernel={} g_with_balance_rank_K={gr} g_kernel_K={} base_support={:?} g_support={:?}",bc.len(),gc.len(),(bc.iter().map(|x|x.len()).min(),bc.iter().map(|x|x.len()).max()),(gc.iter().map(|x|x.len()).min(),gc.iter().map(|x|x.len()).max()));
        let mut global = Ech::new(1084);
        let mut initial = Ech::new(4);
        let mut last = Ech::new(108);
        let mut per = vec![];
        for c in 0..11 {
            let rows: Vec<Vec<QM31>> = (0..N).map(|r| round_row(a, r, c)).collect();
            let mut local = Ech::new(1084);
            let before = global.rank;
            let tapes: Vec<Vec<(usize, QM31)>> = if c == 10 {
                gc.clone()
            } else {
                bc.iter()
                    .map(|v| v.iter().map(|&(r, x)| (r, QM31::from_m31(x))).collect())
                    .collect()
            };
            for tape in &tapes {
                let mut v = vec![QM31::ZERO; 271];
                for &(r, s) in tape {
                    for (v, x) in v.iter_mut().zip(&rows[r]) {
                        *v = v.add(x.mul(s));
                    }
                }
                for k in 0..if c == 10 { 4 } else { 1 } {
                    let f = flatten(&v.iter().map(|x| x.mul(tower(k))).collect::<Vec<_>>());
                    initial.insert(f[..4].to_vec());
                    last.insert(f[976..].to_vec());
                    local.insert(f.clone());
                    global.insert(f);
                }
            }
            println!(
                "ROUND_LANE ood={ood} c={c} rank={} new_global={} global={} elapsed={:.3}",
                local.rank,
                global.rank - before,
                global.rank,
                t.elapsed().as_secs_f64()
            );
            per.push(local.rank);
        }
        println!("ROUND_RESULT ood={ood} raw_conditioned_with_initial_rank={} initial_rank={} initial_zero_rank={} last_round_free_coeff_rank={} lanes={per:?} elapsed={:.3}",global.rank,initial.rank,global.rank-initial.rank,last.rank,t.elapsed().as_secs_f64());
        let mut piv = vec![0; 11];
        for (i, v) in global.p.iter().enumerate() {
            if v.is_some() {
                let j = if i < 4 { 0 } else { 1 + (i - 4) / 108 };
                piv[j] += 1;
            }
        }
        println!("ROUND_PIVOTS ood={ood} initial_then_rounds={piv:?}");
    }
}

fn restricted_circuits<E: CodeField>(raw: &[Vec<E>], bits: usize) -> Vec<Vec<(usize, E)>> {
    let mut out = vec![];
    for suffix in 0..1 << bits {
        let rows: Vec<usize> = (suffix..N).step_by(1 << bits).collect();
        let cols: Vec<Vec<E>> = rows.iter().map(|&r| raw[r].clone()).collect();
        let (_, circs) = circuits(&cols);
        for circ in circs {
            out.push(circ.into_iter().map(|(r, x)| (rows[r], x)).collect());
        }
    }
    out
}
fn verify_circuits<E: CodeField>(raw: &[Vec<E>], cs: &[Vec<(usize, E)>]) {
    for c in cs {
        let mut v = vec![E::ZERO; raw[0].len()];
        for &(r, s) in c {
            for (v, x) in v.iter_mut().zip(&raw[r]) {
                *v = v.add(x.mul(s));
            }
        }
        assert!(v.iter().all(|x| *x == E::ZERO));
    }
}
fn h1_target(a: &[QM31; 10]) -> Vec<QM31> {
    // theta=0, mu=eta=1. Only H1 changes: Delta F=(2-activeMLE)*(eq_1-eq_0).
    let f = |p: &[QM31; 10]| {
        let active = (0..N)
            .filter(|&r| !inactive(r))
            .fold(QM31::ZERO, |v, r| v.add(eq(p, r)));
        q(2).sub(active).mul(eq(p, 1).sub(eq(p, 0)))
    };
    assert!(inactive(0) && inactive(1));
    let terminal = f(a);
    assert_ne!(terminal, QM31::ZERO);
    println!(
        "H1_COUNTEREXAMPLE theta=0 mu=1 eta=1 rows=[0,1] terminal={:?}",
        limbs(terminal).map(|x| x.0)
    );
    let mut out = vec![QM31::ZERO];
    let mut previous = QM31::ZERO;
    for j in 0..10 {
        let values: Vec<QM31> = (0..3)
            .map(|x| {
                (0..1 << (9 - j)).fold(QM31::ZERO, |sum, tail| {
                    let p = std::array::from_fn(|i| {
                        if i < j {
                            a[i]
                        } else if i == j {
                            q(x)
                        } else {
                            q(((tail >> (9 - i)) & 1) as u32)
                        }
                    });
                    sum.add(f(&p))
                })
            })
            .collect();
        let c0 = values[0];
        let c2 = values[2]
            .sub(values[1].add(values[1]))
            .add(c0)
            .mul_m31(M31(2).inv());
        let c1 = values[1].sub(c0).sub(c2);
        assert_eq!(c0.add(values[1]), previous);
        previous = c0.add(c1.mul(a[j])).add(c2.mul(a[j].mul(a[j])));
        out.push(c0);
        out.push(c2);
        out.extend(vec![QM31::ZERO; 25]);
    }
    assert_eq!(previous, terminal);
    out
}
fn structured(a: &[QM31; 10], z: &[Point<QM31>; 2], qs: &[usize]) {
    let t = Instant::now();
    let base = base_raw(a, z, qs, true);
    let ext = ext_raw(a, z, qs, true);
    let rows: Vec<Vec<Vec<QM31>>> = (0..11)
        .map(|c| (0..N).map(|r| round_row(a, r, c)).collect())
        .collect();
    let mut global = Ech::new(1084);
    let mut selected = std::collections::BTreeMap::<usize, usize>::new();
    for bits in (0..=6).rev() {
        let before = global.rank;
        let mut ranges = vec![];
        for c in 0..11 {
            let tapes = if c == 10 {
                let raw: Vec<Vec<QM31>> = ext
                    .iter()
                    .enumerate()
                    .map(|(r, v)| {
                        let mut v = v.clone();
                        v.push(rows[c][r][0]);
                        v
                    })
                    .collect();
                let cs = restricted_circuits(&raw, bits);
                verify_circuits(&raw, &cs);
                cs
            } else {
                let raw: Vec<Vec<M31>> = base
                    .iter()
                    .enumerate()
                    .map(|(r, v)| {
                        let mut v = v.clone();
                        v.push(limbs(rows[c][r][0])[c % 4]);
                        v
                    })
                    .collect();
                let cs = restricted_circuits(&raw, bits);
                verify_circuits(&raw, &cs);
                cs.into_iter()
                    .map(|v| v.into_iter().map(|(r, x)| (r, QM31::from_m31(x))).collect())
                    .collect()
            };
            ranges.push((
                c,
                tapes.len(),
                tapes.iter().map(|x| x.len()).min().unwrap_or(0),
                tapes.iter().map(|x| x.len()).max().unwrap_or(0),
            ));
            for tape in &tapes {
                let mut v = vec![QM31::ZERO; 271];
                for &(r, s) in tape {
                    for (v, x) in v.iter_mut().zip(&rows[c][r]) {
                        *v = v.add(x.mul(s));
                    }
                }
                assert_eq!(v[0], QM31::ZERO);
                if bits > 0 {
                    assert!(v[1 + 27 * (10 - bits)..].iter().all(|x| *x == QM31::ZERO));
                }
                for k in 0..if c == 10 { 4 } else { 1 } {
                    let f = flatten(&v.iter().map(|x| x.mul(tower(k))).collect::<Vec<_>>());
                    if global.insert(f).is_some() {
                        *selected.entry(tape.len()).or_default() += 1;
                    }
                }
            }
        }
        println!("STRUCT bits={bits} rank={} added={} candidates_c_count_min_max={ranges:?} elapsed={:.3}",global.rank,global.rank-before,t.elapsed().as_secs_f64());
    }
    println!("STRUCT_SELECTED circuit_support_histogram={selected:?}");
    let mut pivot_counts = vec![0; 10];
    for i in 4..1084 {
        if global.p[i].is_some() {
            pivot_counts[(i - 4) / 108] += 1;
        }
    }
    println!("STRUCT_PIVOTS rounds={pivot_counts:?}");
    let before = global.rank;
    let target = h1_target(a);
    for k in 0..4 {
        global.insert(flatten(
            &target.iter().map(|x| x.mul(tower(k))).collect::<Vec<_>>(),
        ));
    }
    println!(
        "H1_AUGMENT mask_rank={before} plus_four_H1_target_limb_rank={}",
        global.rank
    );
}

fn c1_details(a: &[QM31; 10], z: &[Point<QM31>; 2], qs: &[usize]) {
    let raw = base_raw(a, z, qs, true);
    for c in 0..16 {
        let mut piv: Vec<Option<(Vec<M31>, Vec<M31>)>> = vec![None; 108];
        let mut source = vec![];
        let mut diagonal = vec![];
        for r in (0..N).filter(|&r| r != 1023 && eligible(c, r)) {
            let mut v: Vec<M31> = raw[r][1..]
                .iter()
                .zip(&raw[1023][1..])
                .map(|(x, y)| if inactive(r) { x.sub(*y) } else { *x })
                .collect();
            let mut t = vec![M31::ZERO; N];
            t[r] = M31::ONE;
            if inactive(r) {
                t[1023] = M31::ONE.neg()
            }
            for j in 0..108 {
                if v[j] == M31::ZERO {
                    continue;
                }
                if let Some((b, bt)) = &piv[j] {
                    let scale = v[j];
                    for i in j..108 {
                        v[i] = v[i].sub(scale.mul(b[i]));
                    }
                    for i in 0..N {
                        t[i] = t[i].sub(scale.mul(bt[i]));
                    }
                } else {
                    let inv = v[j].inv();
                    diagonal.push(v[j].0);
                    source.push(r);
                    for x in &mut v[j..] {
                        *x = x.mul(inv)
                    }
                    for x in &mut t {
                        *x = x.mul(inv)
                    }
                    piv[j] = Some((v, t));
                    break;
                }
            }
            if source.len() == 108 {
                break;
            }
        }
        assert_eq!(source.len(), 108);
        let mut supports = vec![];
        for target in 0..108 {
            let mut v = vec![M31::ZERO; 108];
            v[target] = M31::ONE;
            let mut tape = vec![M31::ZERO; N];
            for j in 0..108 {
                if v[j] == M31::ZERO {
                    continue;
                }
                let (b, bt) = piv[j].as_ref().unwrap();
                let scale = v[j];
                for i in j..108 {
                    v[i] = v[i].sub(scale.mul(b[i]));
                }
                for i in 0..N {
                    tape[i] = tape[i].add(scale.mul(bt[i]));
                }
            }
            assert!(v.iter().all(|x| *x == M31::ZERO));
            let mut actual = vec![M31::ZERO; 108];
            let mut balance = M31::ZERO;
            for r in 0..N {
                if tape[r] == M31::ZERO {
                    continue;
                }
                assert!(eligible(c, r));
                if inactive(r) {
                    balance = balance.add(tape[r]);
                }
                for i in 0..108 {
                    actual[i] = actual[i].add(tape[r].mul(raw[r][i + 1]));
                }
            }
            assert_eq!(balance, M31::ZERO);
            assert_eq!(
                actual,
                (0..108)
                    .map(|i| if i == target { M31::ONE } else { M31::ZERO })
                    .collect::<Vec<_>>()
            );
            supports.push(tape.iter().filter(|x| **x != M31::ZERO).count());
        }
        println!("C1_PREIMAGES c={c} identity_checked=108 physical_support_min={} max={} pivot_rows={source:?} pivot_diagonal={diagonal:?}",supports.iter().min().unwrap(),supports.iter().max().unwrap());
    }
    let bad: Vec<usize> = (0..22).collect();
    let raw = base_raw(a, z, &bad, true);
    let eligible_rows: Vec<usize> = (0..N).filter(|&r| r != 1023 && eligible(0, r)).collect();
    let obs_rows: Vec<Vec<M31>> = (21..109)
        .map(|i| {
            eligible_rows
                .iter()
                .map(|&r| {
                    if inactive(r) {
                        raw[r][i].sub(raw[1023][i])
                    } else {
                        raw[r][i]
                    }
                })
                .collect()
        })
        .collect();
    let (rank, cs) = circuits(&obs_rows);
    verify_circuits(&obs_rows, &cs);
    let relation = cs.iter().min_by_key(|x| x.len()).unwrap();
    let exposed = (0..N)
        .filter(|&r| !eligible(0, r))
        .find_map(|r| {
            let v = relation.iter().fold(M31::ZERO, |v, &(i, w)| {
                v.add(w.mul(if inactive(r) {
                    raw[r][21 + i].sub(raw[1023][21 + i])
                } else {
                    raw[r][21 + i]
                }))
            });
            if v != M31::ZERO {
                Some((r, v.0))
            } else {
                None
            }
        })
        .unwrap();
    println!("C1_BAD_RELATION column=0 opened_rank={rank} terms_index_weight={:?} exposed_noneligible_balanced_row_value={exposed:?}",relation.iter().map(|&(i,w)|(i,w.0)).collect::<Vec<_>>());
    let mut nodes = std::collections::BTreeSet::new();
    for &u in &bad {
        let t = r0::domain::line_node::<M31>(FibreIndex::new(u).unwrap());
        nodes.insert(r0::basis::doubled_factor(2, t).0);
    }
    println!(
        "C1_BAD_D2_LINE_NODES distinct={} values={nodes:?}",
        nodes.len()
    );
    for c in [0, 3, 9, 10, 11] {
        let mut ranks = vec![];
        for residue in 0..4 {
            let mut e = Ech::new(22);
            for r in (residue..N).step_by(4).filter(|&r| eligible(c, r)) {
                e.insert(
                    bad.iter()
                        .map(|&u| {
                            natural(
                                r / 4,
                                r0::domain::line_node::<M31>(FibreIndex::new(u).unwrap()),
                            )
                        })
                        .collect(),
                );
            }
            ranks.push(e.rank);
        }
        println!("C1_BAD_RESIDUE_RANKS c={c} ranks={ranks:?}");
    }
}
fn formula_checks(a: &[QM31; 10]) {
    assert!(a.iter().all(|x| *x != QM31::ZERO && *x != QM31::ONE));
    for c in 0..11 {
        for r in [0, 1, 13, 511, 1023] {
            let vals = round_row(a, r, c);
            let mut prev = vals[0];
            let e = if c == 10 { 26 } else { EXP[c] };
            let family = if c == 10 { 16 } else { 0 };
            for j in 0..10 {
                let mut co = vec![QM31::ZERO; 28];
                co[0] = vals[1 + 27 * j];
                co[2..].copy_from_slice(&vals[2 + 27 * j..28 + 27 * j]);
                co[1] = prev
                    .sub(co[0].add(co[0]))
                    .sub(co[2..].iter().fold(QM31::ZERO, |s, x| s.add(*x)));
                for x in [0, 1, 2, 27, 31] {
                    let p = std::array::from_fn(|i| {
                        if i < j {
                            a[i]
                        } else if i == j {
                            q(x)
                        } else {
                            q(((r >> (9 - i)) & 1) as u32)
                        }
                    });
                    let linear = p.iter().enumerate().fold(QM31::ZERO, |v, (i, x)| {
                        v.add(x.mul_m31(M31((3 + 22 * i + family * (17 + 8 * i)) as u32)))
                    });
                    let fac = if c == 10 {
                        QM31::ONE.add(linear.pow(26))
                    } else {
                        tower(c % 4).mul(linear.pow(e as u64))
                    };
                    let got = co.iter().rev().fold(QM31::ZERO, |v, d| v.mul(q(x)).add(*d));
                    assert_eq!(got, eq(&p, r).mul(fac));
                }
                assert_ne!(co[e + 1], QM31::ZERO);
                prev = co.iter().rev().fold(QM31::ZERO, |v, d| v.mul(a[j]).add(*d));
            }
        }
        let slope = if c == 10 { 1625 } else { 201 };
        let value = M31(slope).pow(if c == 10 { 26 } else { EXP[c] } as u64);
        println!(
            "LAST_LEADING c={c} degree={} base_scalar={} tower_rotation={}",
            if c == 10 { 27 } else { EXP[c] + 1 },
            value.0,
            if c == 10 { 0 } else { c % 4 }
        );
    }
    println!("FORMULA_CHECKS 55 cells x 10 rounds x 5 evaluations passed; all 550 leading coefficients nonzero");
}
fn main() {
    let mut rng = Rng(0x5a346120261009);
    let a = std::array::from_fn(|_| rng.q());
    let z = [circle(rng.q()), circle(rng.q())];
    let sets = query_sets(&mut rng);
    println!("SEED 0x5a346120261009 M31={P}");
    println!("ALPHA {:?}", a.map(|x| limbs(x).map(|x| x.0)));
    println!(
        "CIRCLE {:?}",
        z.map(|z| [limbs(z.x).map(|x| x.0), limbs(z.y).map(|x| x.0)])
    );
    check_dimensions(&a);
    c1(&a, &z, &sets);
    if std::env::args().any(|x| x == "--all") {
        masks(&a, &z, &sets[0].1);
        structured(&a, &z, &sets[0].1);
        c1_details(&a, &z, &sets[0].1);
        formula_checks(&a);
    } else if std::env::args().any(|x| x == "--details") {
        c1_details(&a, &z, &sets[0].1);
        formula_checks(&a);
    } else if std::env::args().any(|x| x == "--structured") {
        structured(&a, &z, &sets[0].1);
    } else if !std::env::args().any(|x| x == "--c1-only") {
        masks(&a, &z, &sets[0].1);
    }
}
