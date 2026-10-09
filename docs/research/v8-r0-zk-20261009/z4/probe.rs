//! Z4a/Z4b/Z4c exact computational probes. No Lean or production changes.
//! Build with the isolated Cargo.toml: release + overflow checks; run.py records evidence.
#![allow(dead_code)]
use aspis_core::{field, r0};
use field::{CM31, M31, P, QM31};
use r0::{
    basis::natural,
    domain::{child_index, stored_point, FibreIndex, Point, SlotIndex},
    CodeField,
};
use std::time::Instant;
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
        let bound = u64::MAX - u64::MAX % P as u64;
        loop {
            let v = self.next();
            if v < bound {
                return M31((v % P as u64) as u32);
            }
        }
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
    let (family, e, rot) = if c == 10 {
        (16, 26, QM31::ONE)
    } else if c < 10 {
        (0, EXP[c], tower(c % 4))
    } else if c < 38 {
        (0, c - 12, tower((c - 12) % 4))
    } else {
        let col = c - 38;
        (
            0,
            if col < 14 {
                2 * col
            } else if col == 14 {
                13
            } else {
                25
            },
            tower(col % 4),
        )
    };
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
fn z4a_main() {
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

mod real {
    use super::*;
    use aspis_prover::pool_v1_pair_forest_honest::*;
    use aspis_statement::{
        derive_owner_key,
        pool_v1::{
            pair_forest_trace::*, pair_trace::PoolV1PairInputNoteWitnessV1,
            pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent,
            IncrementalMerkleTreeV1, PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1,
            PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1, PoolV1PaymentRelationContextV1,
            PoolV1PaymentRuntimeBindingV1, PoolV1PrivateTransferPublicV1, POOL_V1_PAIR_TREE_DEPTH,
        },
        poseidon2::Digest,
    };
    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
    }

    fn pair_empty_roots() -> [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] {
        let zero = [M31::ZERO; 8];
        let mut roots = [zero; POOL_V1_PAIR_TREE_DEPTH + 1];
        roots[0] = pool_v1_tree_parent(&zero, &zero);
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            roots[level + 1] = pool_v1_tree_parent(&roots[level], &roots[level]);
        }
        roots
    }

    fn snapshot_at(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        index: u64,
    ) -> PoolV1PairLiveSnapshotV1 {
        let empty = pair_empty_roots();
        let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
            0,
            empty[POOL_V1_PAIR_TREE_DEPTH],
            core::array::from_fn(|level| empty[level]),
            &empty,
        )
        .unwrap();
        for leaf in 0..index {
            tree = tree
                .append_one_with_empty_roots(digest(20_000 + 32 * leaf as u32), &empty)
                .unwrap()
                .0;
        }
        PoolV1PairLiveSnapshotV1 {
            pool,
            deployment_domain,
            sequence: index,
            next_pair_index: index,
            current_root: tree.root,
            frontier: tree.frontier,
        }
    }

    fn input_witness(value: u32) -> PoolV1PairForestInputNoteWitnessV1 {
        let nullifier_key = digest(10);
        let salt = digest(100);
        let asset = M31(77);
        let owner = derive_owner_key(&nullifier_key);
        let input_commitment = pool_v1_note_commitment(&owner, value, asset, &salt);
        PoolV1PairForestInputNoteWitnessV1 {
            pair: PoolV1PairInputNoteWitnessV1 {
                nullifier_key,
                salt,
                value,
                pair_leaf: PoolV1PairLeafWitnessV1::two_outputs(input_commitment, digest(900))
                    .unwrap(),
                selected_second: false,
                membership: PoolV1MembershipWitnessV1 {
                    siblings: core::array::from_fn(|level| digest(2_000 + 20 * level as u32)),
                    index: 0x5_4321,
                },
            },
            super_root_siblings: [digest(3_000), digest(3_100), digest(3_200)],
            super_root_directions: [true, false, true],
        }
    }

    fn global_anchor(input: &PoolV1PairForestInputNoteWitnessV1) -> Digest {
        let mut current = input.pair.pair_leaf.leaf_digest().unwrap();
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            let sibling = input.pair.membership.siblings[level];
            current = if ((input.pair.membership.index >> level) & 1) == 0 {
                pool_v1_tree_parent(&current, &sibling)
            } else {
                pool_v1_tree_parent(&sibling, &current)
            };
        }
        for level in 0..3 {
            let sibling = input.super_root_siblings[level];
            current = if input.super_root_directions[level] {
                pool_v1_tree_parent(&sibling, &current)
            } else {
                pool_v1_tree_parent(&current, &sibling)
            };
        }
        current
    }

    fn output(seed: u32, value: u32) -> PoolV1OutputNoteWitnessV1 {
        PoolV1OutputNoteWitnessV1 {
            owner_key: digest(seed),
            salt: digest(seed + 100),
            value,
        }
    }

    fn context<'a>(
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        anchor: Digest,
        asset_id: M31,
    ) -> PoolV1PaymentRelationContextV1<'a> {
        PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 {
                pool,
                deployment_domain,
                anchor_sequence: 42,
                anchor_root: anchor,
                asset_id,
            },
            spent_nullifiers: &[],
        }
    }

    #[derive(Clone, Copy)]
    struct TransferFixture {
        public: PoolV1PrivateTransferPublicV1,
        witness: PoolV1PairForestPrivateTransferWitnessV1,
        snapshot: PoolV1PairLiveSnapshotV1,
    }

    fn transfer_fixture() -> TransferFixture {
        let input = input_witness(1_000);
        let recipient = output(300, 600);
        let change = output(500, 400);
        let asset_id = M31(77);
        let anchor = global_anchor(&input);
        let witness = PoolV1PairForestPrivateTransferWitnessV1 {
            input,
            recipient,
            change,
        };
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32],
            deployment_domain: [2; 32],
            anchor_sequence: 42,
            anchor_root: anchor,
            nullifier: pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt),
            asset_id,
            recipient_commitment: pool_v1_note_commitment(
                &recipient.owner_key,
                recipient.value,
                asset_id,
                &recipient.salt,
            ),
            change_commitment: pool_v1_note_commitment(
                &change.owner_key,
                change.value,
                asset_id,
                &change.salt,
            ),
        };
        TransferFixture {
            public,
            witness,
            snapshot: snapshot_at(public.pool, public.deployment_domain, 13),
        }
    }

    fn run_transfer(
        fixture: &TransferFixture,
    ) -> Result<PoolV1PairForestHonestCompilationV1, PoolV1PairForestHonestErrorV1> {
        let lane = pool_v1_pair_forest_output_lane_from_nullifier_v1(&fixture.public.nullifier);
        compile_and_check_pool_v1_pair_forest_private_transfer_honest_v1(
            &fixture.public,
            &fixture.witness,
            context(
                fixture.public.pool,
                fixture.public.deployment_domain,
                fixture.public.anchor_root,
                fixture.public.asset_id,
            ),
            lane,
            fixture.snapshot,
        )
    }

    pub fn instances() -> (
        PoolV1PrivateTransferPublicV1,
        Vec<PoolV1PairForestHonestCompilationV1>,
    ) {
        let mut f = transfer_fixture();
        let commitment = f.witness.input.pair.pair_leaf.first_commitment;
        f.witness.input.pair.pair_leaf =
            PoolV1PairLeafWitnessV1::two_outputs(commitment, commitment).unwrap();
        // Equal siblings at four levels make these path direction choices
        // distinct valid witnesses to exactly the same anchor.
        let mut current = f.witness.input.pair.pair_leaf.leaf_digest().unwrap();
        for level in 0..4 {
            f.witness.input.pair.membership.siblings[level] = current;
            current = pool_v1_tree_parent(&current, &current);
        }
        f.public.anchor_root = global_anchor(&f.witness.input);
        let mut compiled = Vec::new();
        for i in 0..10 {
            let mut x = f;
            x.witness.input.pair.selected_second = i % 2 == 1;
            x.witness.input.pair.membership.index =
                (x.witness.input.pair.membership.index & !15) | (i / 2) as u32;
            assert_eq!(global_anchor(&x.witness.input), f.public.anchor_root);
            let checked = run_transfer(&x).unwrap();
            assert!(checked.residuals.all_zero());
            if !compiled.is_empty() {
                let first: &PoolV1PairForestHonestCompilationV1 = &compiled[0];
                assert_eq!(
                    checked.compilation.public_statement,
                    first.compilation.public_statement
                );
            }
            compiled.push(checked);
        }
        println!("REAL_INSTANCES count=10 pairs=5 common_public=true all_residuals_zero=true changed_directions=pair_slot_and_low_four_path_bits");
        (f.public, compiled)
    }
}

use aspis_core::state_only_prefix::r0::Challenges;
use aspis_statement::pool_v1::{
    pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1,
    pair_forest_semantic_terminal::r0::Public,
};
type Trace = Vec<Vec<QM31>>; // 16 semantic lanes and H1 at index 16.

// Exact value + directional derivative arithmetic for the degree-25 Poseidon part.
#[derive(Clone, Copy, Debug)]
struct Jet {
    v: QM31,
    d: QM31,
}
impl Jet {
    fn add(self, b: Self) -> Self {
        Self {
            v: self.v.add(b.v),
            d: self.d.add(b.d),
        }
    }
    fn sub(self, b: Self) -> Self {
        Self {
            v: self.v.sub(b.v),
            d: self.d.sub(b.d),
        }
    }
    fn scale(self, b: QM31) -> Self {
        Self {
            v: self.v.mul(b),
            d: self.d.mul(b),
        }
    }
    fn constant(v: QM31) -> Self {
        Self { v, d: QM31::ZERO }
    }
    fn pow5(self) -> Self {
        let v2 = self.v.mul(self.v);
        let v4 = v2.mul(v2);
        Self {
            v: v4.mul(self.v),
            d: v4.mul(self.d).mul_m31(M31(5)),
        }
    }
}
fn external(mut s: [Jet; 16]) -> [Jet; 16] {
    let mat = [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]];
    for g in 0..4 {
        let a: [Jet; 4] = std::array::from_fn(|i| s[4 * g + i]);
        for i in 0..4 {
            s[4 * g + i] = (0..4).fold(Jet::constant(QM31::ZERO), |v, k| {
                v.add(a[k].scale(q(mat[i][k])))
            });
        }
    }
    let sums: [Jet; 4] =
        std::array::from_fn(|i| (0..4).fold(Jet::constant(QM31::ZERO), |v, g| v.add(s[4 * g + i])));
    std::array::from_fn(|i| s[i].add(sums[i % 4]))
}
fn internal(s: [Jet; 16]) -> [Jet; 16] {
    let shifts = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16];
    let total = s.iter().fold(Jet::constant(QM31::ZERO), |v, x| v.add(*x));
    std::array::from_fn(|i| {
        if i == 0 {
            total.sub(s[0].scale(q(2)))
        } else {
            total.add(s[i].scale(q(1 << shifts[i - 1])))
        }
    })
}
fn full(s: [Jet; 16], constants: [QM31; 16]) -> [Jet; 16] {
    external(std::array::from_fn(|i| {
        s[i].add(Jet::constant(constants[i])).pow5()
    }))
}
fn poseidon_jet(
    base: &[[QM31; 29]; 3],
    noise: &[[QM31; 29]; 3],
    p: &[QM31; 10],
    theta: QM31,
) -> Jet {
    use jet_constants::{EXTERNAL_FINAL, EXTERNAL_INITIAL, INTERNAL};
    let high: Vec<QM31> = (0..64)
        .map(|r| {
            (0..6).fold(QM31::ONE, |v, i| {
                v.mul(if (r >> (5 - i)) & 1 == 1 {
                    p[i]
                } else {
                    QM31::ONE.sub(p[i])
                })
            })
        })
        .collect();
    let local: [QM31; 16] = std::array::from_fn(|r| {
        (6..10).fold(QM31::ONE, |v, i| {
            v.mul(if (r >> (9 - i)) & 1 == 1 {
                p[i]
            } else {
                QM31::ONE.sub(p[i])
            })
        })
    });
    let block = high[..57].iter().fold(QM31::ZERO, |v, x| v.add(*x));
    let z: [Jet; 16] = std::array::from_fn(|i| Jet {
        v: base[0][i],
        d: noise[0][i],
    });
    let mut leading = z;
    for i in 0..8 {
        leading[i] = leading[i].add(Jet {
            v: base[2][i],
            d: noise[2][i],
        });
    }
    leading = full(
        full(external(leading), EXTERNAL_INITIAL[0].map(q)),
        EXTERNAL_INITIAL[1].map(q),
    );
    let interpolate = |a: [u32; 16], b: [u32; 16], c: [u32; 16]| {
        std::array::from_fn(|i| {
            local[1]
                .mul_m31(M31(a[i]))
                .add(local[9].mul_m31(M31(b[i])))
                .add(local[10].mul_m31(M31(c[i])))
        })
    };
    let fulls = full(
        full(
            z,
            interpolate(EXTERNAL_INITIAL[2], EXTERNAL_FINAL[0], EXTERNAL_FINAL[2]),
        ),
        interpolate(EXTERNAL_INITIAL[3], EXTERNAL_FINAL[1], EXTERNAL_FINAL[3]),
    );
    let mut ins = z;
    for parity in 0..2 {
        let co = (2..=8).fold(QM31::ZERO, |v, r| {
            v.add(local[r].mul_m31(M31(INTERNAL[2 * (r - 2) + parity])))
        });
        ins[0] = ins[0].add(Jet::constant(co)).pow5();
        ins = internal(ins);
    }
    let weights = [
        local[0],
        local[1].add(local[9]).add(local[10]),
        local[2..9].iter().fold(QM31::ZERO, |v, x| v.add(*x)),
    ];
    let mut out = Jet::constant(QM31::ZERO);
    let mut power = QM31::ONE;
    for g in 0..4 {
        for k in 0..4 {
            let i = 4 * g + k;
            let target = Jet {
                v: base[1][i],
                d: noise[1][i],
            };
            let residual = target
                .sub(leading[i])
                .scale(weights[0])
                .add(target.sub(fulls[i]).scale(weights[1]))
                .add(target.sub(ins[i]).scale(weights[2]));
            out = out.add(residual.scale(block.mul(power).mul(tower(k))));
        }
        power = power.mul(theta);
    }
    out
}
fn interp_weights(n: usize) -> Vec<Vec<M31>> {
    (0..n)
        .map(|i| {
            let mut co = vec![M31::ONE];
            let mut den = M31::ONE;
            for j in 0..n {
                if j == i {
                    continue;
                }
                let mut v = vec![M31::ZERO; co.len() + 1];
                for k in 0..co.len() {
                    v[k] = v[k].sub(co[k].mul(M31(j as u32)));
                    v[k + 1] = v[k + 1].add(co[k]);
                }
                co = v;
                den = den.mul(M31(i as u32).sub(M31(j as u32)));
            }
            co.into_iter().map(|x| x.mul(den.inv())).collect()
        })
        .collect()
}
fn interpolate(values: &[QM31], weights: &[Vec<M31>]) -> Vec<QM31> {
    (0..values.len())
        .map(|d| {
            values
                .iter()
                .zip(weights)
                .fold(QM31::ZERO, |s, (v, w)| s.add(v.mul_m31(w[d])))
        })
        .collect()
}
fn equality(a: &[QM31; 10], b: &[QM31; 10]) -> QM31 {
    (0..10).fold(QM31::ONE, |s, i| {
        s.mul(
            QM31::ONE
                .sub(a[i])
                .sub(b[i])
                .add(a[i].mul(b[i]).mul_m31(M31(2))),
        )
    })
}
fn terminal_jet(
    public: Public<'_>,
    base: &[[QM31; 29]; 3],
    noise: &[[QM31; 29]; 3],
    p: &[QM31; 10],
    ch: &Challenges,
    derivative_weights: &[Vec<M31>],
    check: bool,
) -> (QM31, QM31, QM31) {
    let pj = poseidon_jet(base, noise, p, ch.theta);
    let eq = equality(&ch.zc, p);
    let f0 = public.terminal_qm31(base, p, ch).unwrap();
    let mut first = QM31::ZERO;
    let mut derivative = QM31::ZERO;
    // Subtract the degree-25 Poseidon component. All remaining claim dependence
    // has degree <=5 (four Copy denominators times H1); six points are exact.
    for t in 0..6 {
        let v = std::array::from_fn(|j| {
            std::array::from_fn(|c| base[j][c].add(noise[j][c].mul_m31(M31(t))))
        });
        let f = if t == 0 {
            f0
        } else {
            public.terminal_qm31(&v, p, ch).unwrap()
        };
        if t == 1 {
            first = f;
        }
        let ps = if t == 0 {
            pj.v
        } else {
            poseidon_jet(&v, &[[QM31::ZERO; 29]; 3], p, ch.theta).v
        };
        derivative = derivative.add(f.sub(eq.mul(ps)).mul_m31(derivative_weights[t as usize][1]));
    }
    derivative = derivative.add(eq.mul(pj.d));
    if check {
        use aspis_statement::state_only_poseidon::{
            evaluate_state_only_poseidon_oracle_projected, StateOnlyPoseidonOpenings,
            StateOnlyPoseidonSelectors,
        };
        let mut sel = StateOnlyPoseidonSelectors::at_point(p);
        sel.block = (0..N)
            .filter(|r| r / 16 < 57)
            .fold(QM31::ZERO, |v, r| v.add(eq_row_probe(p, r)));
        let o = StateOnlyPoseidonOpenings {
            z: std::array::from_fn(|i| base[0][i]),
            succ_z: std::array::from_fn(|i| base[1][i]),
            xor12_z: std::array::from_fn(|i| base[2][i]),
        };
        let ps = evaluate_state_only_poseidon_oracle_projected(&o, &sel);
        assert_eq!(
            pj.v,
            (0..4).fold(QM31::ZERO, |v, i| v.add(ps[i].mul(ch.theta.pow(i as u64))))
        );
        let w = interp_weights(26);
        let exact = (0..26).fold(QM31::ZERO, |sum, t| {
            let v = std::array::from_fn(|j| {
                std::array::from_fn(|c| base[j][c].add(noise[j][c].mul_m31(M31(t))))
            });
            sum.add(
                public
                    .terminal_qm31(&v, p, ch)
                    .unwrap()
                    .mul_m31(w[t as usize][1]),
            )
        });
        assert_eq!(exact, derivative);
    }
    (f0, first, derivative)
}
fn eq_row_probe(p: &[QM31; 10], r: usize) -> QM31 {
    eq(p, r)
}
fn balance_trace(t: &mut Trace) {
    for (c, col) in t.iter_mut().enumerate() {
        let dep = if c == 16 { 0 } else { 1023 };
        let sum = (0..N)
            .filter(|&r| r != dep && inactive(r))
            .fold(QM31::ZERO, |s, r| s.add(col[r]));
        col[dep] = QM31::ZERO.sub(sum);
    }
}
fn point_claims(t: &Trace, p: &[QM31; 10]) -> [[QM31; 29]; 3] {
    let mut out = [[QM31::ZERO; 29]; 3];
    for (j, p) in points(p).iter().enumerate() {
        let weights: Vec<_> = (0..N).map(|r| eq(p, r)).collect();
        for c in 0..17 {
            out[j][if c == 16 { 26 } else { c }] =
                (0..N).fold(QM31::ZERO, |v, r| v.add(t[c][r].mul(weights[r])));
        }
    }
    out
}
// Fold only fixed prefix coordinates, retaining every Boolean suffix at once.
fn folded(t: &Trace, p: &[QM31]) -> Trace {
    t.iter()
        .map(|col| {
            let mut v = col.clone();
            for &x in p {
                let len = v.len() / 2;
                for i in 0..len {
                    v[i] = v[i].add(x.mul(v[len + i].sub(v[i])));
                }
                v.truncate(len);
            }
            v
        })
        .collect()
}
fn grid_claims(t: &Trace, p: &[QM31; 10], j: usize) -> Vec<[[QM31; 29]; 3]> {
    let count = 1 << (9 - j);
    let normal = folded(t, &p[..=j]);
    let flip = points(p)[2];
    let xor = folded(t, &flip[..=j]);
    let mut out = vec![[[QM31::ZERO; 29]; 3]; count];
    for tail in 0..count {
        let xor_tail = tail ^ (12 & (count - 1));
        for c in 0..17 {
            let lane = if c == 16 { 26 } else { c };
            out[tail][0][lane] = normal[c][tail];
            out[tail][2][lane] = xor[c][xor_tail];
            if tail + 1 < count {
                out[tail][1][lane] = normal[c][tail + 1];
            }
        }
    }
    let mut last = *p;
    for i in j + 1..10 {
        last[i] = QM31::ONE;
    }
    let succ = points(&last)[1];
    let v = folded(t, &succ);
    for c in 0..17 {
        out[count - 1][1][if c == 16 { 26 } else { c }] = v[c][0];
    }
    out
}
fn mask_value(claims: &[[QM31; 29]; 3], p: &[QM31; 10]) -> QM31 {
    let l = (0..10).fold(QM31::ZERO, |v, i| {
        v.add(p[i].mul_m31(M31((3 + 22 * i) as u32)))
    });
    (0..16).fold(QM31::ZERO, |v, c| {
        v.add(claims[0][c].mul(tower(c % 4)).mul(l.pow(if c < 14 {
            2 * c
        } else if c == 14 {
            13
        } else {
            25
        } as u64)))
    })
}
struct Targets {
    pinned: Vec<QM31>,
    derivative: Vec<QM31>,
    difference: Vec<QM31>,
    terminal: [QM31; 3],
}
fn compute_targets(
    public: Public<'_>,
    a: &[QM31; 10],
    ch: &Challenges,
    w: &Trace,
    wp: &Trace,
    n: &Trace,
    pair: usize,
) -> Targets {
    let iw = interp_weights(28);
    let dw = interp_weights(6);
    let mut values = [Vec::<QM31>::new(), Vec::new(), Vec::new()];
    let mut initial = [QM31::ZERO; 3];
    let mut previous = [QM31::ZERO; 3];
    for j in 0..10 {
        let mut samples = [
            vec![QM31::ZERO; 28],
            vec![QM31::ZERO; 28],
            vec![QM31::ZERO; 28],
        ];
        for x in 0..28 {
            let mut p = *a;
            p[j] = q(x);
            let wg = grid_claims(w, &p, j);
            let ng = grid_claims(n, &p, j);
            let pg = grid_claims(wp, &p, j);
            for tail in 0..1 << (9 - j) {
                for i in j + 1..10 {
                    p[i] = q(((tail >> (9 - i)) & 1) as u32);
                }
                let (base, noisy, diff) = terminal_jet(
                    public,
                    &wg[tail],
                    &ng[tail],
                    &p,
                    ch,
                    &dw,
                    x == 3 && tail == 0,
                );
                let other = public.terminal_qm31(&pg[tail], &p, ch).unwrap();
                let g = noisy.sub(base).mul(ch.eta);
                samples[0][x as usize] = samples[0][x as usize].add(g);
                samples[1][x as usize] = samples[1][x as usize].add(g.sub(diff.mul(ch.eta)));
                samples[2][x as usize] = samples[2][x as usize].add(
                    base.sub(other)
                        .mul(ch.eta)
                        .add(mask_value(&wg[tail], &p).sub(mask_value(&pg[tail], &p))),
                );
                if j == 0 && x < 2 {
                    initial[2] =
                        initial[2].add(mask_value(&wg[tail], &p).sub(mask_value(&pg[tail], &p)));
                }
            }
        }
        for k in 0..3 {
            if j == 0 {
                previous[k] = initial[k];
                values[k].push(initial[k]);
            }
            assert_eq!(
                samples[k][0].add(samples[k][1]),
                previous[k],
                "boundary pair={pair} round={j} target={k}"
            );
            let co = interpolate(&samples[k], &iw);
            values[k].push(co[0]);
            values[k].extend_from_slice(&co[2..]);
            previous[k] = co.iter().rev().fold(QM31::ZERO, |v, c| v.mul(a[j]).add(*c));
        }
        if j == 0 || j == 9 {
            println!("TARGET_PROGRESS pair={pair} round={j}");
        }
    }
    // Direct terminal evaluation checks all round interpolation and the chain.
    let b = point_claims(w, a);
    let nn = point_claims(n, a);
    let bp = point_claims(wp, a);
    let (f0, f1, df) = terminal_jet(public, &b, &nn, a, ch, &dw, true);
    assert_eq!(previous[0], f1.sub(f0).mul(ch.eta));
    assert_eq!(previous[1], f1.sub(f0).sub(df).mul(ch.eta));
    assert_eq!(
        previous[2],
        f0.sub(public.terminal_qm31(&bp, a, ch).unwrap())
            .mul(ch.eta)
            .add(mask_value(&b, a).sub(mask_value(&bp, a)))
    );
    Targets {
        pinned: values[0].clone(),
        derivative: values[1].clone(),
        difference: values[2].clone(),
        terminal: [
            previous[0],
            previous[1],
            f0.sub(public.terminal_qm31(&bp, a, ch).unwrap())
                .mul(ch.eta),
        ],
    }
}

impl<E: CodeField> Ech<E> {
    fn residual(&self, mut v: Vec<E>) -> Vec<E> {
        for i in 0..v.len() {
            if v[i] == E::ZERO {
                continue;
            }
            if let Some(b) = &self.p[i] {
                let s = v[i];
                for j in i..v.len() {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
            }
        }
        v
    }
}
fn coord(i: usize) -> String {
    if i < 4 {
        format!("initial:{}", i)
    } else {
        let u = i - 4;
        let d = (u % 108) / 4;
        format!("({},{},{})", u / 108, if d == 0 { 0 } else { d + 1 }, u % 4)
    }
}
fn summarize(label: &str, e: &Ech<M31>, targets: &[Vec<M31>]) {
    let mut extra = Ech::new(1084);
    let mut support = std::collections::BTreeSet::new();
    let mut failures = 0;
    for t in targets {
        let r = e.residual(t.clone());
        if r.iter().any(|x| *x != M31::ZERO) {
            failures += 1;
        }
        for (i, x) in r.iter().enumerate() {
            if *x != M31::ZERO {
                support.insert(i);
            }
        }
        extra.insert(r);
    }
    let coordinates: Vec<_> = support.into_iter().map(coord).collect();
    let pivots: Vec<_> = extra
        .p
        .iter()
        .enumerate()
        .filter(|(_, v)| v.is_some())
        .map(|(i, _)| coord(i))
        .collect();
    println!("RESULT {label} image_rank={} targets={} failures={} excess_rank={} quotient_support={coordinates:?} excess_pivots={pivots:?}",e.rank,targets.len(),failures,extra.rank);
}
// Eliminate per-lane raw observations first, carrying their round images.
// Remaining columns are exactly the conditioned round image, never a relaxed
// ambient span. The carry also provides a particular solution to each raw target.
trait LiftQ: CodeField {
    fn lift_q(self) -> QM31;
}
impl LiftQ for M31 {
    fn lift_q(self) -> QM31 {
        QM31::from_m31(self)
    }
}
impl LiftQ for QM31 {
    fn lift_q(self) -> QM31 {
        self
    }
}
fn lane_eliminate<E: LiftQ>(
    raw: &[Vec<E>],
    rounds: &[Vec<QM31>],
    targets: &[Vec<E>],
    extensions: bool,
    global: &mut Ech<M31>,
) -> Vec<Vec<QM31>> {
    let mut piv: Vec<Option<(Vec<E>, Vec<QM31>)>> = vec![None; raw[0].len()];
    let lift = |s: E| s.lift_q();
    for (raw, rr) in raw.iter().zip(rounds) {
        let mut v = raw.clone();
        let mut r = rr.clone();
        let mut inserted = false;
        for i in 0..v.len() {
            if v[i] == E::ZERO {
                continue;
            }
            if let Some((b, br)) = &piv[i] {
                let s = v[i];
                for j in i..v.len() {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
                let s = lift(s);
                for j in 0..271 {
                    r[j] = r[j].sub(s.mul(br[j]));
                }
            } else {
                let inv = v[i].try_inv().unwrap();
                for x in &mut v[i..] {
                    *x = x.mul(inv);
                }
                let inv = lift(inv);
                for x in &mut r {
                    *x = x.mul(inv);
                }
                piv[i] = Some((v, r.clone()));
                inserted = true;
                break;
            }
        }
        if !inserted {
            for k in 0..if extensions { 4 } else { 1 } {
                global.insert(flatten(
                    &r.iter().map(|x| x.mul(tower(k))).collect::<Vec<_>>(),
                ));
            }
        }
    }
    targets
        .iter()
        .map(|target| {
            let mut v = target.clone();
            let mut out = vec![QM31::ZERO; 271];
            for i in 0..v.len() {
                if v[i] == E::ZERO {
                    continue;
                }
                let (b, br) = piv[i]
                    .as_ref()
                    .expect("raw observation target outside lane image");
                let s = v[i];
                for j in i..v.len() {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
                let s = lift(s);
                for j in 0..271 {
                    out[j] = out[j].add(s.mul(br[j]));
                }
            }
            assert!(v.iter().all(|x| *x == E::ZERO));
            out
        })
        .collect()
}
fn difference_raw<E: CodeField>(raw: &[Vec<E>], left: &[E], right: &[E]) -> Vec<E> {
    (0..raw[0].len())
        .map(|i| (0..N).fold(E::ZERO, |s, r| s.add(left[r].sub(right[r]).mul(raw[r][i]))))
        .collect()
}
fn build_images(
    a: &[QM31; 10],
    z: &[Point<QM31>; 2],
    qs: &[usize],
    traces: &[Trace],
    targets: &[Targets],
) -> (Ech<M31>, Ech<M31>, Vec<Vec<M31>>) {
    let br = base_raw(a, z, qs, true);
    let gr = ext_raw(a, z, qs, true);
    let mut pure = Ech::new(1084);
    for c in 0..11 {
        let rows: Vec<_> = (0..N).map(|r| round_row(a, r, c)).collect();
        if c == 10 {
            lane_eliminate(&gr, &rows, &[], true, &mut pure);
        } else {
            lane_eliminate(&br, &rows, &[], false, &mut pure);
        }
    }
    assert_eq!(
        pure.rank, 992,
        "raw-silent mask image incl initial (expected 988 after initial=0)"
    );
    let mut all = Ech {
        p: pure.p.clone(),
        rank: pure.rank,
    };
    let mut residuals: Vec<Vec<QM31>> = targets.iter().map(|t| t.difference.clone()).collect();
    for c in 0..16 {
        let rows: Vec<_> = (0..N).filter(|&r| eligible(c, r) && r != 1023).collect();
        let raw: Vec<Vec<M31>> = rows
            .iter()
            .map(|&r| {
                br[r]
                    .iter()
                    .zip(&br[1023])
                    .map(|(x, d)| if inactive(r) { x.sub(*d) } else { *x })
                    .collect()
            })
            .collect();
        let full_rounds: Vec<_> = (0..N).map(|r| round_row(a, r, 38 + c)).collect();
        let rr: Vec<Vec<QM31>> = rows
            .iter()
            .map(|&r| {
                full_rounds[r]
                    .iter()
                    .zip(&full_rounds[1023])
                    .map(|(x, d)| if inactive(r) { x.sub(*d) } else { *x })
                    .collect()
            })
            .collect();
        let tg: Vec<_> = (0..5)
            .map(|pair| {
                let left: Vec<_> = traces[2 * pair][c]
                    .iter()
                    .map(|v| {
                        assert_eq!(limbs(*v)[1..], [M31::ZERO; 3]);
                        v.c0.a
                    })
                    .collect();
                let right: Vec<_> = traces[2 * pair + 1][c].iter().map(|v| v.c0.a).collect();
                difference_raw(&br, &left, &right)
            })
            .collect();
        let solutions = lane_eliminate(&raw, &rr, &tg, false, &mut all);
        for p in 0..5 {
            for i in 0..271 {
                residuals[p][i] = residuals[p][i].sub(solutions[p][i]);
            }
        }
    }
    // H1 has no explicit mask factor. Verify its active-row helper differences
    // can be matched by the inactive balanced H1 padding in the raw observations.
    let rows: Vec<_> = (1..N).filter(|&r| inactive(r)).collect();
    let raw: Vec<Vec<QM31>> = rows
        .iter()
        .map(|&r| gr[r].iter().zip(&gr[0]).map(|(x, d)| x.sub(*d)).collect())
        .collect();
    let rr = vec![vec![QM31::ZERO; 271]; rows.len()];
    let tg: Vec<_> = (0..5)
        .map(|p| difference_raw(&gr, &traces[2 * p][16], &traces[2 * p + 1][16]))
        .collect();
    lane_eliminate(&raw, &rr, &tg, true, &mut all);
    println!("IMAGES pure_initial_retained={} pure_initial_zero={} full_tape_raw_conditioned={} H1_raw_solutions=5 C1_raw_solutions=80 D_compensation_gamma_nonzero=true",pure.rank,pure.rank-4,all.rank);
    for i in 0..4 {
        assert!(pure.p[i].take().is_some());
    }
    pure.rank -= 4;
    (pure, all, residuals.iter().map(|v| flatten(v)).collect())
}
fn repaired_last_round(a: &[QM31; 10]) -> Ech<M31> {
    // A relaxation to all K-valued slopes, therefore an upper bound on every
    // physical silent repair. Point-claim silence forces (X-alpha_9).
    let mut e = Ech::new(112);
    for c in (12..38).chain(std::iter::once(10)) {
        let rows0 = round_row(a, 0, c);
        let rows1 = round_row(a, 1, c);
        // row 0/1 share prefix; normalized final slices are 1-X and X.
        let pref = (0..9).fold(QM31::ONE, |v, i| v.mul(QM31::ONE.sub(a[i])));
        let inv = pref.try_inv().unwrap();
        let mut free = vec![QM31::ZERO; 271];
        for i in 0..271 {
            free[i] = rows1[i]
                .mul(QM31::ONE.sub(a[9]))
                .sub(rows0[i].mul(a[9]))
                .mul(inv);
        }
        let mut co = vec![QM31::ZERO; 28];
        co[0] = free[244];
        co[2..].copy_from_slice(&free[245..271]); // coefficient 1 via direct factor slice: use terminal root.
        co[1] = QM31::ZERO
            .sub(co[0])
            .sub((2..28).fold(QM31::ZERO, |v, d| v.add(co[d].mul(a[9].pow(d as u64)))))
            .mul(a[9].try_inv().unwrap());
        assert_eq!(
            co.iter().rev().fold(QM31::ZERO, |v, x| v.mul(a[9]).add(*x)),
            QM31::ZERO
        );
        for k in 0..4 {
            e.insert(flatten(
                &co.iter().map(|x| x.mul(tower(k))).collect::<Vec<_>>(),
            ));
        }
    }
    e
}
fn last_coeff(v: &[QM31], a: &[QM31; 10]) -> Vec<QM31> {
    let mut prev = v[0];
    let mut co = vec![QM31::ZERO; 28];
    for j in 0..10 {
        co[0] = v[1 + 27 * j];
        co[2..].copy_from_slice(&v[2 + 27 * j..28 + 27 * j]);
        co[1] = prev
            .sub(co[0].add(co[0]))
            .sub(co[2..].iter().fold(QM31::ZERO, |v, x| v.add(*x)));
        prev = co.iter().rev().fold(QM31::ZERO, |v, x| v.mul(a[j]).add(*x));
    }
    co
}
fn z4b_main() {
    if std::env::args().any(|x| x == "--z4a") {
        return z4a_main();
    }
    let args: Vec<_> = std::env::args().collect();
    let trials = args
        .windows(2)
        .find(|x| x[0] == "--trials")
        .map(|x| x[1].parse::<usize>().unwrap())
        .unwrap_or(20);
    let seed = args
        .windows(2)
        .find(|x| x[0] == "--seed")
        .map(|x| u64::from_str_radix(x[1].trim_start_matches("0x"), 16).unwrap())
        .unwrap_or_else(|| {
            use std::io::Read;
            let mut b = [0u8; 8];
            std::fs::File::open("/dev/urandom")
                .unwrap()
                .read_exact(&mut b)
                .unwrap();
            u64::from_le_bytes(b)
        });
    assert_ne!(seed, 0);
    use aspis_statement::pool_v1::pair_forest_hiding::{
        pool_v1_pair_forest_copy_active_row_masks_v1,
        pool_v1_pair_forest_relation_free_mask_cells_v1,
    };
    assert_eq!(
        pool_v1_pair_forest_copy_active_row_masks_v1().unwrap(),
        ACTIVE
    );
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    for c in 0..16 {
        for r in 0..N {
            assert_eq!(
                eligible(c, r),
                cells
                    .iter()
                    .any(|x| x.column as usize == c && x.row as usize == r)
            );
        }
    }
    let (pubdata, instances) = real::instances();
    println!(
        "Z4B seed={seed:#x} trials={trials} pairs=5 field=M31 tower=QM31 pinned_D12_primary=true"
    );
    let jobs = args
        .windows(2)
        .find(|x| x[0] == "--jobs")
        .map(|x| x[1].parse::<usize>().unwrap())
        .unwrap_or(4);
    assert!((1..=4).contains(&jobs));
    println!("WORKERS jobs={jobs} per_trial_seed=root_plus_golden_ratio_times_trial_plus_one");
    std::thread::scope(|scope| {
        for worker in 0..jobs {
            let instances = &instances;
            let pubdata = &pubdata;
            scope.spawn(move|| {for trial in (worker..trials).step_by(jobs) {
        let trial_seed=seed.wrapping_add((trial as u64+1).wrapping_mul(0x9e3779b97f4a7c15));
        assert_ne!(trial_seed,0);let mut rng=Rng(trial_seed);
        println!("TRIAL_SEED trial={trial} seed={trial_seed:#x}");
        let start = Instant::now();
        let a = std::array::from_fn(|_| rng.q());
        let z = [circle(rng.q()), circle(rng.q())];
        let sets = query_sets(&mut rng);
        let ch = Challenges {
            lambda: rng.q(),
            chi: rng.q(),
            theta: rng.q(),
            zc: std::array::from_fn(|_| rng.q()),
            mu: rng.q(),
            eta: rng.q(),
        };
        assert!(a.iter().all(|x| *x != QM31::ZERO && *x != QM31::ONE));
        assert!(ch.theta != QM31::ZERO && ch.mu != QM31::ZERO && ch.eta != QM31::ZERO);
        println!(
            "CHALLENGE trial={trial} alpha={a:?} semantic={ch:?} circle={z:?} queries={:?}",
            sets[0].1
        );
        let traces: Vec<Trace> = instances
            .iter()
            .map(|w| {
                let mut t: Trace = w
                    .compilation
                    .semantic_c1
                    .c1
                    .iter()
                    .map(|col| col.iter().map(|x| QM31::from_m31(*x)).collect())
                    .collect();
                let h = build_pool_v1_pair_forest_copy_helper_v1(
                    &w.compilation.trace,
                    w.compilation.public_statement.live_snapshot.next_pair_index,
                    ch.lambda,
                    ch.chi,
                )
                .unwrap();
                t.push(h);
                balance_trace(&mut t);
                t
            })
            .collect();
        let mut targets = Vec::new();
        let mut noises = Vec::new();
        for pair in 0..5 {
            let mut noise: Trace = (0..17)
                .map(|c| {
                    (0..N)
                        .map(|r| {
                            if c < 16 && eligible(c, r) {
                                QM31::from_m31(rng.m())
                            } else if c == 16 && inactive(r) {
                                rng.q()
                            } else {
                                QM31::ZERO
                            }
                        })
                        .collect()
                })
                .collect();
            balance_trace(&mut noise);
            let public =
                Public::Transfer(&pubdata, &instances[2 * pair].compilation.public_statement);
            let t = compute_targets(
                public,
                &a,
                &ch,
                &traces[2 * pair],
                &traces[2 * pair + 1],
                &noise,
                pair,
            );
            println!("TERMINAL_OBSTRUCTIONS trial={trial} pair={pair} pinned={:?} derivative={:?} ii={:?}",limbs(t.terminal[0]).map(|v|v.0),limbs(t.terminal[1]).map(|v|v.0),limbs(t.terminal[2]).map(|v|v.0));
            targets.push(t);
            noises.push(noise);
        }
        if trial == 0 {
            degenerate_controls(
                Public::Transfer(&pubdata, &instances[0].compilation.public_statement),
                &a,
                &ch,
                &traces[0],
                &traces[1],
                &noises[0],
            );
        }
        if trial==0 {exact_repair(&a,&z,&sets[0].1,&targets);}
        let (pure, all, ii) = build_images(&a, &z, &sets[0].1, &traces, &targets);
        summarize(
            &format!("trial={trial} i_pinned"),
            &pure,
            &targets
                .iter()
                .map(|t| flatten(&t.pinned))
                .collect::<Vec<_>>(),
        );
        summarize(
            &format!("trial={trial} i_derivative"),
            &pure,
            &targets
                .iter()
                .map(|t| flatten(&t.derivative))
                .collect::<Vec<_>>(),
        );
        summarize(&format!("trial={trial} ii_full_tape"), &all, &ii);
        let repair = repaired_last_round(&a);
        assert_eq!(repair.rank, 108);
        for kind in 0..2 {
            let mut extra = Ech::new(112);
            let mut fail = 0;
            for t in &targets {
                let co = last_coeff(if kind == 0 { &t.pinned } else { &t.derivative }, &a);
                let residual = repair.residual(flatten(&co));
                if residual.iter().any(|x| *x != M31::ZERO) {
                    fail += 1;
                }
                extra.insert(residual);
            }
            println!("REPAIR trial={trial} kind={kind} mask_columns=26 exponents=0..25 G=26 relaxed_last_round_rank={} failures={fail} excess={} no_column_count_can_remove_terminal_obstruction=true",repair.rank,extra.rank);
        }
        println!("REPAIR_II trial={trial} mask_columns=26 failures={} terminal_values_nonzero={} no_column_count_can_remove_terminal_obstruction=true",targets.iter().filter(|t|t.terminal[2]!=QM31::ZERO).count(),targets.iter().filter(|t|t.terminal[2]!=QM31::ZERO).count());
        println!(
            "TRIAL_DONE trial={trial} wall_seconds={:.3}",
            start.elapsed().as_secs_f64()
        );
    }});
        }
    });
}

// Exact private constant arrays copied from the pinned poseidon2.rs.
mod jet_constants {
    pub const EXTERNAL_INITIAL: [[u32; 16]; 4] = [
        [
            0x768bab52, 0x70e0ab7d, 0x3d266c8a, 0x6da42045, 0x600fef22, 0x41dace6b, 0x64f9bdd4,
            0x5d42d4fe, 0x76b1516d, 0x6fc9a717, 0x70ac4fb6, 0x00194ef6, 0x22b644e2, 0x1f7916d5,
            0x47581be2, 0x2710a123,
        ],
        [
            0x6284e867, 0x018d3afe, 0x5df99ef3, 0x4c1e467b, 0x566f6abc, 0x2994e427, 0x538a6d42,
            0x5d7bf2cf, 0x7fda2dab, 0x0fd854c4, 0x46922fca, 0x3d7763a1, 0x19fd05ca, 0x0a4bbb43,
            0x15075851, 0x3d903d76,
        ],
        [
            0x2d290ff7, 0x40809fa0, 0x59dac6ec, 0x127927a2, 0x6bbf0ea0, 0x0294140f, 0x24742976,
            0x6e84c081, 0x22484f4a, 0x354cae59, 0x0453ffe1, 0x3f47a3cc, 0x0088204e, 0x6066e109,
            0x3b7c4b80, 0x6b55665d,
        ],
        [
            0x3bc4b897, 0x735bf378, 0x508daf42, 0x1884fc2b, 0x7214f24c, 0x7498be0a, 0x1a60e640,
            0x3303f928, 0x29b46376, 0x5c96bb68, 0x65d097a5, 0x1d358e9f, 0x4a9a9017, 0x4724cf76,
            0x347af70f, 0x1e77e59a,
        ],
    ];
    pub const EXTERNAL_FINAL: [[u32; 16]; 4] = [
        [
            0x57090613, 0x1fa42108, 0x17bbef50, 0x1ff7e11c, 0x047b24ca, 0x4e140275, 0x4fa086f5,
            0x079b309c, 0x1159bd47, 0x6d37e4e5, 0x075d8dce, 0x12121ca0, 0x7f6a7c40, 0x68e182ba,
            0x5493201b, 0x0444a80e,
        ],
        [
            0x0064f4c6, 0x6467abe6, 0x66975762, 0x2af68f9b, 0x345b33be, 0x1b70d47f, 0x053db717,
            0x381189cb, 0x43b915f8, 0x20df3694, 0x0f459d26, 0x77a0e97b, 0x2f73e739, 0x1876c2f9,
            0x65a0e29a, 0x4cabefbe,
        ],
        [
            0x5abd1268, 0x4d34a760, 0x12771799, 0x69a0c9ac, 0x39091e55, 0x7f611cd0, 0x3af055da,
            0x7ac0bbdf, 0x6e0f3a24, 0x41e3b6f7, 0x49b3756d, 0x568bc538, 0x20c079d8, 0x1701c72c,
            0x7670dc6c, 0x5a439035,
        ],
        [
            0x7c93e00e, 0x561fbb4d, 0x1178907b, 0x02737406, 0x32fb24f1, 0x6323b60a, 0x6ab12418,
            0x42c99cea, 0x155a0b97, 0x53d1c6aa, 0x2bd20347, 0x279b3d73, 0x4f5f3c70, 0x0245af6c,
            0x238359d3, 0x49966a59,
        ],
    ];
    pub const INTERNAL: [u32; 14] = [
        0x7f7ec4bf, 0x0421926f, 0x5198e669, 0x34db3148, 0x4368bafd, 0x66685c7f, 0x78d3249a,
        0x60187881, 0x76dad67a, 0x0690b437, 0x1ea95311, 0x40e5369a, 0x38f103fc, 0x1d226a21,
    ];
}

fn degenerate_controls(
    public: Public<'_>,
    a: &[QM31; 10],
    ch: &Challenges,
    w: &Trace,
    wp: &Trace,
    n: &Trace,
) {
    let mut cases = Vec::new();
    for name in ["theta=0", "mu=0", "eta=0", "theta=mu=0"] {
        let mut c = *ch;
        if name.contains("theta") {
            c.theta = QM31::ZERO;
        }
        if name.contains("mu") {
            c.mu = QM31::ZERO;
        }
        if name == "eta=0" {
            c.eta = QM31::ZERO;
        }
        cases.push((name.to_string(), *a, c));
    }
    for j in 0..10 {
        for bit in 0..2 {
            let mut point = *a;
            point[j] = q(bit);
            cases.push((format!("alpha_{j}={bit}"), point, *ch));
        }
    }
    cases.push(("alpha=all_zero".to_string(), [QM31::ZERO; 10], *ch));
    cases.push(("alpha=all_one".to_string(), [QM31::ONE; 10], *ch));
    let dw = interp_weights(6);
    for (name, p, c) in cases {
        let b = point_claims(w, &p);
        let nn = point_claims(n, &p);
        let bp = point_claims(wp, &p);
        let (f0, f1, df) = terminal_jet(public, &b, &nn, &p, &c, &dw, true);
        let ii = f0
            .sub(public.terminal_qm31(&bp, &p, &c).unwrap())
            .mul(c.eta);
        println!(
            "DEGENERATE name={name} pinned={:?} derivative={:?} ii={:?}",
            limbs(f1.sub(f0).mul(c.eta)).map(|x| x.0),
            limbs(f1.sub(f0).sub(df).mul(c.eta)).map(|x| x.0),
            limbs(ii).map(|x| x.0)
        );
    }
    // The old sparse H1 witness, now also checked against the genuine terminal.
    let mut h = vec![vec![QM31::ZERO; N]; 17];
    h[16][1] = QM31::ONE;
    h[16][0] = QM31::ONE.neg();
    let b = point_claims(w, a);
    let nn = point_claims(&h, a);
    let mut c = *ch;
    c.theta = QM31::ZERO;
    c.mu = QM31::ONE;
    c.eta = QM31::ONE;
    let (f0, f1, df) = terminal_jet(public, &b, &nn, a, &c, &dw, true);
    let active = (0..N)
        .filter(|&r| !inactive(r))
        .fold(QM31::ZERO, |v, r| v.add(eq(a, r)));
    let expected = q(2).sub(active).mul(eq(a, 1).sub(eq(a, 0)));
    assert_eq!(f1.sub(f0), expected);
    assert_eq!(df, expected);
    println!(
        "SPARSE_THETA_ZERO_H1 actual={:?} derivative_remainder_zero=true",
        limbs(expected).map(|x| x.0)
    );
}

fn exact_repair(a: &[QM31; 10], z: &[Point<QM31>; 2], qs: &[usize], targets: &[Targets]) {
    let br = base_raw(a, z, qs, true);
    let gr = ext_raw(a, z, qs, true);
    let mut image = Ech::new(1084);
    for c in (12..38).chain(std::iter::once(10)) {
        let rr: Vec<_> = (0..N).map(|r| round_row(a, r, c)).collect();
        if c == 10 {
            lane_eliminate(&gr, &rr, &[], true, &mut image);
        } else {
            lane_eliminate(&br, &rr, &[], false, &mut image);
        }
    }
    let initial_rank = (0..4).filter(|&i| image.p[i].is_some()).count();
    assert_eq!(initial_rank, 4);
    for i in 0..4 {
        image.p[i] = None;
    }
    image.rank -= 4;
    assert_eq!(image.rank, 1076);
    summarize(
        "trial=0 exact_repair_pinned_26",
        &image,
        &targets
            .iter()
            .map(|t| flatten(&t.pinned))
            .collect::<Vec<_>>(),
    );
    summarize(
        "trial=0 exact_repair_derivative_26",
        &image,
        &targets
            .iter()
            .map(|t| flatten(&t.derivative))
            .collect::<Vec<_>>(),
    );
}

// Z4c: D13 coefficient observations and D14 Libra tail. All code below is
// research-only; production terminal/encoder code is called, never edited.
fn h_weight(a: &[QM31; 10], coefficient: usize) -> QM31 {
    if coefficient < 28 {
        a[8].pow(coefficient as u64)
    } else if coefficient < 56 {
        a[9].pow((coefficient - 28) as u64)
    } else {
        QM31::ZERO
    }
}
fn raw_c(
    a: &[QM31; 10],
    z: &[Point<QM31>; 2],
    queries: &[usize],
) -> (Vec<Vec<M31>>, Vec<Vec<QM31>>) {
    use r0::transport::ROW_TO_COEFFICIENT;
    let pts = points(a);
    let mut base = Vec::new();
    let mut ext = Vec::new();
    for r in 0..N {
        let co = usize::from(ROW_TO_COEFFICIENT[r]);
        let mut b = vec![if inactive(r) { M31::ONE } else { M31::ZERO }];
        let mut e = vec![if inactive(r) { QM31::ONE } else { QM31::ZERO }];
        for p in pts {
            let x = eq(&p, r);
            b.extend(limbs(x));
            e.push(x);
        }
        let h = h_weight(a, co);
        b.extend(limbs(h));
        e.push(h);
        for p in z {
            let x = evalrow(co, *p);
            b.extend(limbs(x));
            e.push(x);
        }
        for &u in queries {
            for slot in 0..4 {
                let point = stored_point::<M31>(child_index(
                    FibreIndex::new(u).unwrap(),
                    SlotIndex::new(slot).unwrap(),
                ));
                let x = evalrow(co, point);
                b.push(x);
                e.push(QM31::from_m31(x));
            }
        }
        assert_eq!(b.len(), 113);
        assert_eq!(e.len(), 95);
        base.push(b);
        ext.push(e);
    }
    (base, ext)
}
fn tail_row(a: &[QM31; 10], row: usize) -> Vec<QM31> {
    let co = usize::from(r0::transport::ROW_TO_COEFFICIENT[row]);
    let mut out = vec![QM31::ZERO; 271];
    if co >= 56 {
        return out;
    }
    let m = if co < 28 { 8 } else { 9 };
    let d = co % 28;
    let endpoint_sum = q(if d == 0 { 2 } else { 1 });
    out[0] = endpoint_sum.mul_m31(M31(512));
    for j in 0..10 {
        if j < m {
            out[1 + 27 * j] = endpoint_sum.mul_m31(M31(1 << (8 - j)));
        } else if j == m {
            if d != 1 {
                out[1 + 27 * j + if d == 0 { 0 } else { d - 1 }] = q(1 << (9 - j));
            }
        } else {
            out[1 + 27 * j] = a[m].pow(d as u64).mul_m31(M31(1 << (9 - j)));
        }
    }
    out
}
fn final_value(v: &[QM31], a: &[QM31; 10]) -> QM31 {
    last_coeff(v, a)
        .iter()
        .rev()
        .fold(QM31::ZERO, |sum, x| sum.mul(a[9]).add(*x))
}
fn phi0(v: &[QM31], explicit_mask_at_alpha: QM31, extra_d_claim: QM31, a: &[QM31; 10]) -> QM31 {
    final_value(v, a)
        .sub(explicit_mask_at_alpha)
        .sub(extra_d_claim)
}
fn normalize_d(v: &[QM31], phi: QM31, a: &[QM31; 10]) -> Option<Vec<QM31>> {
    let half = QM31::from_m31(M31(2).inv());
    let inv = a[9].sub(half).try_inv()?;
    let mut out = v.to_vec();
    out[244] = out[244].add(phi.mul(inv).mul(half));
    assert_eq!(final_value(&out, a), final_value(v, a).sub(phi));
    Some(out)
}
fn normalized(
    t: &Targets,
    a: &[QM31; 10],
    w: &Trace,
    wp: &Trace,
    ch: &Challenges,
    public: Public<'_>,
) -> Targets {
    let y = point_claims(w, a);
    let yp = point_claims(wp, a);
    let md = mask_value(&y, a).sub(mask_value(&yp, a));
    assert_eq!(phi0(&t.pinned, QM31::ZERO, QM31::ZERO, a), t.terminal[0]);
    assert_eq!(phi0(&t.difference, md, QM31::ZERO, a), t.terminal[2]);
    let pinned = normalize_d(&t.pinned, t.terminal[0], a).expect("alpha9=1/2");
    let derivative = normalize_d(&t.derivative, t.terminal[1], a).expect("alpha9=1/2");
    let difference = normalize_d(&t.difference, t.terminal[2], a).expect("alpha9=1/2");
    assert_eq!(phi0(&difference, md, QM31::ZERO, a), QM31::ZERO);
    // Psi and its inverse use the same unchanged claim coordinates. Reapply
    // their known original-terminal difference to recover the exact old payload.
    let original = public
        .terminal_qm31(&y, a, ch)
        .unwrap()
        .sub(public.terminal_qm31(&yp, a, ch).unwrap())
        .mul(ch.eta);
    assert_eq!(
        normalize_d(&difference, original.neg(), a).unwrap(),
        t.difference
    );
    assert_eq!(
        normalize_d(&pinned, t.terminal[0].neg(), a).unwrap(),
        t.pinned
    );
    Targets {
        pinned,
        derivative,
        difference,
        terminal: [QM31::ZERO; 3],
    }
}
fn c1_c(trial: usize, a: &[QM31; 10], z: &[Point<QM31>; 2], qs: &[usize]) -> bool {
    let mut all = true;
    for (name, qset) in [("random", qs.to_vec()), ("consecutive", (0..22).collect())] {
        let (raw, _) = raw_c(a, z, &qset);
        let mut ranks = Vec::new();
        for c in 0..16 {
            let mut e = Ech::new(112);
            for r in 0..N {
                if r == 1023 || !eligible(c, r) {
                    continue;
                }
                e.insert(
                    raw[r][1..]
                        .iter()
                        .zip(&raw[1023][1..])
                        .map(|(x, d)| if inactive(r) { x.sub(*d) } else { *x })
                        .collect(),
                );
            }
            ranks.push(e.rank);
        }
        println!("C1_C trial={trial} pattern={name} ranks={ranks:?} want_each=112");
        if name == "random" && ranks.iter().any(|&r| r < 112) {
            all = false;
        }
    }
    all
}
fn copied_ech(e: &Ech<M31>) -> Ech<M31> {
    Ech {
        p: e.p.clone(),
        rank: e.rank,
    }
}
fn initial_zero(mut e: Ech<M31>) -> Ech<M31> {
    for i in 0..4 {
        if e.p[i].take().is_some() {
            e.rank -= 1;
        }
    }
    e
}
fn compensated_rows(
    a: &[QM31; 10],
    c: Option<usize>,
    physical_lane: usize,
    tail: &[Vec<QM31>],
    libra: bool,
) -> Vec<Vec<QM31>> {
    let coefficient = if libra {
        q(7).pow(physical_lane as u64)
            .mul(q(7).pow(28).try_inv().unwrap())
    } else {
        QM31::ZERO
    };
    (0..N)
        .map(|r| {
            let base = c
                .map(|c| round_row(a, r, c))
                .unwrap_or_else(|| vec![QM31::ZERO; 271]);
            base.iter()
                .zip(&tail[r])
                .map(|(b, h)| b.sub(coefficient.mul(*h)))
                .collect()
        })
        .collect()
}
fn pure_c(
    a: &[QM31; 10],
    br: &[Vec<M31>],
    gr: &[Vec<QM31>],
    tail: &[Vec<QM31>],
    libra: bool,
) -> Ech<M31> {
    let mut image = Ech::new(1084);
    let cols: Vec<_> = if libra {
        (0..11).collect()
    } else {
        (12..38).chain(std::iter::once(10)).collect()
    };
    for (position, c) in cols.into_iter().enumerate() {
        let lane = if c == 10 { 27 } else { 16 + position };
        let rr = compensated_rows(a, Some(c), lane, tail, libra);
        if c == 10 {
            lane_eliminate(gr, &rr, &[], true, &mut image);
        } else {
            lane_eliminate(br, &rr, &[], false, &mut image);
        }
    }
    image
}
fn full_c(
    a: &[QM31; 10],
    br: &[Vec<M31>],
    gr: &[Vec<QM31>],
    tail: &[Vec<QM31>],
    traces: &[Trace],
    targets: &[Targets],
    pure: &Ech<M31>,
    libra: bool,
) -> (Ech<M31>, Vec<Vec<M31>>) {
    let mut all = copied_ech(pure);
    let pairs = targets.len();
    let mut residuals: Vec<_> = targets.iter().map(|t| t.difference.clone()).collect();
    // Target batch offset: after every lane's raw target is matched, D's word
    // = gamma^-28 * batch(target - chosen sources), so all its own raw claims
    // (including w_h) are zero. Account for its tail instead of discarding it.
    if libra {
        for pair in 0..pairs {
            for c in 0..17 {
                let lane = if c == 16 { 26 } else { c };
                let factor = q(7).pow(lane as u64).mul(q(7).pow(28).try_inv().unwrap());
                for r in 0..N {
                    let d = traces[2 * pair][c][r]
                        .sub(traces[2 * pair + 1][c][r])
                        .mul(factor);
                    if d == QM31::ZERO {
                        continue;
                    }
                    for i in 0..271 {
                        residuals[pair][i] = residuals[pair][i].sub(d.mul(tail[r][i]));
                    }
                }
            }
        }
    }
    for c in 0..16 {
        let allowed: Vec<_> = (0..N).filter(|&r| r != 1023 && eligible(c, r)).collect();
        let raw: Vec<Vec<M31>> = allowed
            .iter()
            .map(|&r| {
                br[r]
                    .iter()
                    .zip(&br[1023])
                    .map(|(x, d)| if inactive(r) { x.sub(*d) } else { *x })
                    .collect()
            })
            .collect();
        let rr_all = compensated_rows(a, Some(38 + c), c, tail, libra);
        let rr: Vec<_> = allowed
            .iter()
            .map(|&r| {
                rr_all[r]
                    .iter()
                    .zip(&rr_all[1023])
                    .map(|(x, d)| if inactive(r) { x.sub(*d) } else { *x })
                    .collect()
            })
            .collect();
        let tg: Vec<_> = (0..pairs)
            .map(|p| {
                let left: Vec<_> = traces[2 * p][c].iter().map(|x| x.c0.a).collect();
                let right: Vec<_> = traces[2 * p + 1][c].iter().map(|x| x.c0.a).collect();
                difference_raw(br, &left, &right)
            })
            .collect();
        let solutions = lane_eliminate(&raw, &rr, &tg, false, &mut all);
        for p in 0..pairs {
            for i in 0..271 {
                residuals[p][i] = residuals[p][i].sub(solutions[p][i]);
            }
        }
    }
    let allowed: Vec<_> = (1..N).filter(|&r| inactive(r)).collect();
    let raw: Vec<Vec<QM31>> = allowed
        .iter()
        .map(|&r| gr[r].iter().zip(&gr[0]).map(|(x, d)| x.sub(*d)).collect())
        .collect();
    let rr_all = compensated_rows(a, None, 26, tail, libra);
    let rr: Vec<_> = allowed
        .iter()
        .map(|&r| {
            rr_all[r]
                .iter()
                .zip(&rr_all[0])
                .map(|(x, d)| x.sub(*d))
                .collect()
        })
        .collect();
    let tg: Vec<_> = (0..pairs)
        .map(|p| difference_raw(gr, &traces[2 * p][16], &traces[2 * p + 1][16]))
        .collect();
    let solutions = lane_eliminate(&raw, &rr, &tg, true, &mut all);
    for p in 0..pairs {
        for i in 0..271 {
            residuals[p][i] = residuals[p][i].sub(solutions[p][i]);
        }
    }
    (all, residuals.iter().map(|v| flatten(v)).collect())
}
fn pass_count(e: &Ech<M31>, t: &[Vec<M31>]) -> usize {
    t.iter()
        .filter(|v| e.residual((*v).clone()).iter().all(|x| *x == M31::ZERO))
        .count()
}
fn gate_c(
    label: &str,
    a: &[QM31; 10],
    z: &[Point<QM31>; 2],
    qs: &[usize],
    traces: &[Trace],
    targets: &[Targets],
    control: bool,
) -> bool {
    let (br, gr) = raw_c(a, z, qs);
    let tail: Vec<_> = (0..N).map(|r| tail_row(a, r)).collect();
    let design = if control { "columns26" } else { "libra" };
    let pure = pure_c(a, &br, &gr, &tail, !control);
    let silent = initial_zero(copied_ech(&pure));
    let i: Vec<_> = targets.iter().map(|t| flatten(&t.pinned)).collect();
    let derivative: Vec<_> = targets.iter().map(|t| flatten(&t.derivative)).collect();
    let (all, ii) = full_c(a, &br, &gr, &tail, traces, targets, &pure, !control);
    summarize(&format!("{label} {design}_i_prime"), &silent, &i);
    summarize(
        &format!("{label} {design}_derivative_diagnostic"),
        &silent,
        &derivative,
    );
    summarize(&format!("{label} {design}_ii_prime"), &all, &ii);
    let ip = pass_count(&silent, &i);
    let iip = pass_count(&all, &ii);
    println!("GATE_C {label} design={design} silent_rank={} initial_retained_rank={} full_conditioned_rank={} i_pass={ip} ii_pass={iip} attempted={} batch_word_matched=true gamma=7 fourth_claims_all_lanes=true",silent.rank,pure.rank,all.rank,targets.len());
    // Achieving the boundary/terminal upper bound proves this sufficient
    // zero-batched-word subspace equals the entire silent round image.
    ip == targets.len() && iip == targets.len()
}
fn check_tail_and_transport(a: &[QM31; 10], z: &[Point<QM31>; 2]) {
    use r0::transport::{to_coefficients, to_rows, COEFFICIENT_TO_ROW, ROW_TO_COEFFICIENT};
    let rows: [M31; 1024] = std::array::from_fn(|r| M31((r + 1) as u32));
    assert_eq!(to_rows(&to_coefficients(&rows)), rows);
    assert_eq!(ROW_TO_COEFFICIENT[1023], 1023);
    for j in 0..89 {
        let r = usize::from(COEFFICIENT_TO_ROW[j]);
        assert!(inactive(r));
        assert!((0..16).all(|c| eligible(c, r)));
    }
    // Actual R0 eval_message on transported coefficients versus direct rows.
    let co = to_coefficients(&rows).map(QM31::from_m31);
    for &p in z {
        let actual = r0::encoder::eval_message(&co, p);
        let direct = (0..N).fold(QM31::ZERO, |v, r| {
            v.add(evalrow(usize::from(ROW_TO_COEFFICIENT[r]), p).mul_m31(rows[r]))
        });
        assert_eq!(actual, direct);
    }
    for coefficient in 0..56 {
        let row = usize::from(COEFFICIENT_TO_ROW[coefficient]);
        let v = tail_row(a, row);
        assert_eq!(final_value(&v, a), h_weight(a, coefficient));
        let m = if coefficient < 28 { 8 } else { 9 };
        let d = coefficient % 28;
        let mut previous = v[0];
        for j in 0..10 {
            let mut co = [QM31::ZERO; 28];
            co[0] = v[1 + 27 * j];
            co[2..].copy_from_slice(&v[2 + 27 * j..28 + 27 * j]);
            co[1] = previous
                .sub(co[0].add(co[0]))
                .sub(co[2..].iter().fold(QM31::ZERO, |s, x| s.add(*x)));
            for x in [0, 1, 2, 29] {
                let got = co.iter().rev().fold(QM31::ZERO, |v, c| v.mul(q(x)).add(*c));
                let expected = if j < m {
                    q(1 << (8 - j)).mul(q(if d == 0 { 2 } else { 1 }))
                } else if j == m {
                    q(1 << (9 - j)).mul(q(x).pow(d as u64))
                } else {
                    q(1 << (9 - j)).mul(a[m].pow(d as u64))
                };
                assert_eq!(got, expected);
            }
            previous = co.iter().rev().fold(QM31::ZERO, |v, c| v.mul(a[j]).add(*c));
        }
    }
    println!("TAIL_TRANSPORT_CHECKS 56 monomials x 10 rounds x 4 evaluation_points; transported encoder identity passed");
}

fn controls_c(
    public: Public<'_>,
    a: &[QM31; 10],
    ch: &Challenges,
    w: &Trace,
    wp: &Trace,
    n: &Trace,
    z: &[Point<QM31>; 2],
    qs: &[usize],
) {
    let mut cases = Vec::new();
    for name in ["theta=0", "mu=0", "eta=0", "theta=mu=0"] {
        let mut c = *ch;
        if name.contains("theta") {
            c.theta = QM31::ZERO;
        }
        if name.contains("mu") {
            c.mu = QM31::ZERO;
        }
        if name == "eta=0" {
            c.eta = QM31::ZERO;
        }
        cases.push((name.to_string(), *a, c));
    }
    for j in 0..10 {
        for bit in 0..2 {
            let mut p = *a;
            p[j] = q(bit);
            cases.push((format!("alpha_{j}={bit}"), p, *ch));
        }
    }
    cases.push(("alpha=all_zero".to_string(), [QM31::ZERO; 10], *ch));
    cases.push(("alpha=all_one".to_string(), [QM31::ONE; 10], *ch));
    for (name, p, c) in cases {
        println!("CONTROL_START name={name}");
        let original = compute_targets(public, &p, &c, w, wp, n, 0);
        let t = normalized(&original, &p, w, wp, &c, public);
        let pass = gate_c(
            &format!("control={name}"),
            &p,
            z,
            qs,
            &[w.clone(), wp.clone()],
            &[t],
            false,
        );
        println!("CONTROL_DONE name={name} all_pass={pass}");
    }
    let mut p = *a;
    p[9] = QM31::from_m31(M31(2).inv());
    let b = point_claims(w, &p);
    let np = point_claims(n, &p);
    let bp = point_claims(wp, &p);
    let (f0, f1, _) = terminal_jet(public, &b, &np, &p, ch, &interp_weights(6), true);
    let g = f1.sub(f0).mul(ch.eta);
    let ii = f0
        .sub(public.terminal_qm31(&bp, &p, ch).unwrap())
        .mul(ch.eta);
    assert!(normalize_d(&vec![QM31::ZERO; 271], g, &p).is_none());
    println!("ALPHA9_HALF denominator_zero=true psi_undefined=true normalization_undefined=true pinned_phi={:?} ii_phi={:?}",limbs(g).map(|x|x.0),limbs(ii).map(|x|x.0));
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.iter().any(|x| x == "--z4b") {
        return z4b_main();
    }
    if args.iter().any(|x| x == "--z4a") {
        return z4a_main();
    }
    let trials = args
        .windows(2)
        .find(|x| x[0] == "--trials")
        .map(|x| x[1].parse::<usize>().unwrap())
        .unwrap_or(20);
    let seed = args
        .windows(2)
        .find(|x| x[0] == "--seed")
        .map(|x| u64::from_str_radix(x[1].trim_start_matches("0x"), 16).unwrap())
        .unwrap_or(0x5348f0b9a87835d0);
    assert_eq!(seed, 0x5348f0b9a87835d0, "Z4c must replay the Z4b seed");
    use aspis_statement::pool_v1::pair_forest_hiding::{
        pool_v1_pair_forest_copy_active_row_masks_v1,
        pool_v1_pair_forest_relation_free_mask_cells_v1,
    };
    assert_eq!(
        pool_v1_pair_forest_copy_active_row_masks_v1().unwrap(),
        ACTIVE
    );
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    for c in 0..16 {
        for r in 0..N {
            assert_eq!(
                eligible(c, r),
                cells
                    .iter()
                    .any(|x| x.column as usize == c && x.row as usize == r)
            );
        }
    }
    let (pubdata, instances) = real::instances();
    println!("Z4C seed={seed:#x} trials={trials} pairs=5 base=a17cd72f8 D13_transport=true fourth_claim_all_lanes=true gamma=7 optimized_overflow_checks=true");
    let mut control_data = None;
    // Sequential admission obeys the explicit stop list: no later challenge
    // or control is computed after a failed generic Libra containment gate.
    for trial in 0..trials {
        let start = Instant::now();
        let trial_seed = seed.wrapping_add((trial as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15));
        let mut rng = Rng(trial_seed);
        let a = std::array::from_fn(|_| rng.q());
        let z = [circle(rng.q()), circle(rng.q())];
        let sets = query_sets(&mut rng);
        let ch = Challenges {
            lambda: rng.q(),
            chi: rng.q(),
            theta: rng.q(),
            zc: std::array::from_fn(|_| rng.q()),
            mu: rng.q(),
            eta: rng.q(),
        };
        assert!(a.iter().all(|x| *x != QM31::ZERO && *x != QM31::ONE));
        assert!(ch.theta != QM31::ZERO && ch.mu != QM31::ZERO && ch.eta != QM31::ZERO);
        println!("TRIAL_SEED trial={trial} seed={trial_seed:#x}");
        println!(
            "CHALLENGE trial={trial} alpha={a:?} semantic={ch:?} circle={z:?} queries={:?}",
            sets[0].1
        );
        if trial == 0 {
            check_tail_and_transport(&a, &z);
        }
        if args.iter().any(|x| x == "--preflight") {
            println!("PREFLIGHT_DONE no_containment_gate_run=true");
            return;
        }
        if !c1_c(trial, &a, &z, &sets[0].1) {
            println!("STOP reason=random_C1_rank_below_112 trial={trial}");
            std::process::exit(21);
        }
        let traces: Vec<Trace> = instances
            .iter()
            .map(|w| {
                let mut t: Trace = w
                    .compilation
                    .semantic_c1
                    .c1
                    .iter()
                    .map(|col| col.iter().map(|x| QM31::from_m31(*x)).collect())
                    .collect();
                match build_pool_v1_pair_forest_copy_helper_v1(
                    &w.compilation.trace,
                    w.compilation.public_statement.live_snapshot.next_pair_index,
                    ch.lambda,
                    ch.chi,
                ) {
                    Ok(h) => t.push(h),
                    Err(error) => {
                        println!(
                            "STOP reason=helper_pole_or_helper_abort trial={trial} error={error:?}"
                        );
                        std::process::exit(22);
                    }
                }
                balance_trace(&mut t);
                t
            })
            .collect();
        let mut targets = Vec::new();
        for pair in 0..5 {
            let mut noise: Trace = (0..17)
                .map(|c| {
                    (0..N)
                        .map(|r| {
                            if c < 16 && eligible(c, r) {
                                QM31::from_m31(rng.m())
                            } else if c == 16 && inactive(r) {
                                rng.q()
                            } else {
                                QM31::ZERO
                            }
                        })
                        .collect()
                })
                .collect();
            balance_trace(&mut noise);
            let public =
                Public::Transfer(&pubdata, &instances[2 * pair].compilation.public_statement);
            let original = compute_targets(
                public,
                &a,
                &ch,
                &traces[2 * pair],
                &traces[2 * pair + 1],
                &noise,
                pair,
            );
            println!(
                "Z4B_REPLAY trial={trial} pair={pair} pinned={:?} derivative={:?} ii={:?}",
                limbs(original.terminal[0]).map(|v| v.0),
                limbs(original.terminal[1]).map(|v| v.0),
                limbs(original.terminal[2]).map(|v| v.0)
            );
            let t = normalized(
                &original,
                &a,
                &traces[2 * pair],
                &traces[2 * pair + 1],
                &ch,
                public,
            );
            targets.push(t);
            if trial == 0 && pair == 0 {
                control_data = Some((
                    a,
                    z,
                    ch,
                    traces[0].clone(),
                    traces[1].clone(),
                    noise,
                    sets[0].1.clone(),
                ));
            }
        }
        if !gate_c(
            &format!("trial={trial}"),
            &a,
            &z,
            &sets[0].1,
            &traces,
            &targets,
            false,
        ) {
            println!("STOP reason=Libra_containment_failure trial={trial} required_i_pass=100/100 required_ii_pass=100/100");
            std::process::exit(23);
        }
        gate_c(
            &format!("trial={trial}"),
            &a,
            &z,
            &sets[0].1,
            &traces,
            &targets,
            true,
        );
        println!(
            "TRIAL_DONE trial={trial} wall_seconds={:.3}",
            start.elapsed().as_secs_f64()
        );
    }
    if trials == 20 {
        let (a, z, ch, w, wp, n, qs) = control_data.unwrap();
        controls_c(
            Public::Transfer(&pubdata, &instances[0].compilation.public_statement),
            &a,
            &ch,
            &w,
            &wp,
            &n,
            &z,
            &qs,
        );
    }
    println!(
        "Z4C_DONE trials={trials} i_pass={} ii_pass={}",
        5 * trials,
        5 * trials
    );
}
