//! Z6: the original (eta-free) terminal at every Boolean row, with and without
//! eligible noise. Reuses Z4c's witnesses, challenge replay and tape draws.
//! No elimination routine is used or changed.
use super::*;
use aspis_statement::pool_v1::{
    pair_forest_hiding::{
        pool_v1_pair_forest_copy_active_row_masks_v1,
        pool_v1_pair_forest_relation_free_mask_cells_v1,
    },
    pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1,
    pair_trace::PoolV1PairTupleLimbV1,
};
use std::fmt::Write as _;

const MASTER: u64 = 0x5348f0b9a87835d0;
const THREADS: usize = 8;

fn bits(b: usize) -> [QM31; 10] {
    std::array::from_fn(|i| q(((b >> (9 - i)) & 1) as u32))
}
fn lane(c: usize) -> usize {
    if c == 16 { 26 } else { c }
}
/// Boolean-row claims: z at b, succ at b+1 (mod 1024), xor12 at b^12.
fn row_claims(t: &Trace, b: usize) -> [[QM31; 29]; 3] {
    let mut out = [[QM31::ZERO; 29]; 3];
    for c in 0..17 {
        out[0][lane(c)] = t[c][b];
        out[1][lane(c)] = t[c][(b + 1) % N];
        out[2][lane(c)] = t[c][b ^ 12];
    }
    out
}
fn term(public: Public<'_>, t: &Trace, ch: &Challenges, b: usize) -> Result<QM31, ()> {
    public.terminal_qm31(&row_claims(t, b), &bits(b), ch).map_err(|_| ())
}
fn rows_subset(public: Public<'_>, t: &Trace, ch: &Challenges, rows: &[usize]) -> Vec<Result<QM31, ()>> {
    let chunk = rows.len().div_ceil(THREADS).max(1);
    std::thread::scope(|s| {
        let hs: Vec<_> = rows
            .chunks(chunk)
            .map(|part| s.spawn(move || part.iter().map(|&b| term(public, t, ch, b)).collect::<Vec<_>>()))
            .collect();
        hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
    })
}
fn all_rows(public: Public<'_>, t: &Trace, ch: &Challenges) -> Vec<QM31> {
    let rows: Vec<usize> = (0..N).collect();
    rows_subset(public, t, ch, &rows).into_iter().map(|x| x.expect("honest terminal error")).collect()
}
fn total(v: &[QM31]) -> QM31 {
    v.iter().fold(QM31::ZERO, |s, x| s.add(*x))
}
fn l(x: QM31) -> [u32; 4] {
    limbs(x).map(|v| v.0)
}
fn fnv(v: &[QM31]) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325u64;
    for x in v {
        for limb in l(*x) {
            for byte in limb.to_le_bytes() {
                h ^= byte as u64;
                h = h.wrapping_mul(0x100_0000_01b3);
            }
        }
    }
    h
}
/// Lean `balance`: overwrite `dep` with minus the sum over copyInactiveRows \ {dep}.
fn balance(col: &mut [QM31], dep: usize) {
    let sum = (0..N).filter(|&r| r != dep && inactive(r)).fold(QM31::ZERO, |s, r| s.add(col[r]));
    col[dep] = QM31::ZERO.sub(sum);
}
fn diff_report(label: &str, a: &[QM31], b: &[QM31]) -> (usize, String) {
    let rows: Vec<usize> = (0..N).filter(|&r| a[r] != b[r]).collect();
    let mut s = format!("{label} diff_count={} ", rows.len());
    if rows.len() <= 64 {
        write!(s, "rows={rows:?} values=[").unwrap();
        for (i, &r) in rows.iter().enumerate() {
            if i > 0 { s.push(','); }
            write!(s, "[{r},{:?},{:?}]", l(a[r]), l(b[r])).unwrap();
        }
        s.push_str("] ");
    } else {
        let mut m16 = [0usize; 16];
        let mut blk = [0usize; 64];
        for &r in &rows { m16[r % 16] += 1; blk[r / 16] += 1; }
        write!(s, "rows=omitted hist_mod16={m16:?} hist_block={blk:?} ").unwrap();
    }
    let (sa, sb) = (total(a), total(b));
    write!(s, "sum_a={:?} sum_b={:?} sum_diff={:?} hash_a={:#018x} hash_b={:#018x}", l(sa), l(sb), l(sb.sub(sa)), fnv(a), fnv(b)).unwrap();
    (rows.len(), s)
}

fn structural_checks() -> Vec<(usize, usize)> {
    assert_eq!(pool_v1_pair_forest_copy_active_row_masks_v1().unwrap(), ACTIVE);
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let mut list = vec![];
    let mut on_active = vec![];
    for c in 0..16 {
        for r in 0..N {
            let e = eligible(c, r);
            assert_eq!(e, cells.iter().any(|x| x.column as usize == c && x.row as usize == r));
            if e {
                if !inactive(r) { on_active.push((c, r)); }
                list.push((c, r));
            }
        }
    }
    assert!(inactive(1023));
    let reg = build_pool_v1_pair_forest_copy_registry_v1().unwrap();
    let (mut tuples, mut read) = (0, 0);
    for link in &reg {
        for t in [link.producer, link.consumer] {
            tuples += 1;
            assert!(!inactive(t.row as usize));
            for limb in t.limbs {
                if let PoolV1PairTupleLimbV1::Cell { source, .. } = limb {
                    let (r, c) = (source.cell.row as usize, source.cell.column as usize);
                    read += 1;
                    assert!(c < 16 && !inactive(r) && r != 1023 && !eligible(c, r), "helper reads ({c},{r})");
                }
            }
        }
    }
    let rows_per_col: Vec<usize> = (0..16).map(|c| list.iter().filter(|x| x.0 == c).count()).collect();
    println!("Z6_STRUCT eligible_cells={} per_column={rows_per_col:?} eligible_on_copy_active_rows={on_active:?} row1023_inactive=true eligible_1023_columns={:?} registry_links={} tuples={tuples} helper_cell_reads={read} helper_reads_only_active_noneligible_non1023=true inactive_rows={}",
        list.len(), (0..16).filter(|&c| eligible(c, 1023)).collect::<Vec<_>>(), reg.len(), (0..N).filter(|&r| inactive(r)).count());
    list
}

struct Trial {
    a: [QM31; 10],
    ch: Challenges,
    tapes: Vec<Trace>,
}
/// Exact replay of z4c_main's RNG consumption (challenges, then five tapes).
fn trial(trial: usize, print: bool) -> Trial {
    let trial_seed = MASTER.wrapping_add((trial as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15));
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
    if print { println!("TRIAL_SEED trial={trial} seed={trial_seed:#x}");
    println!("CHALLENGE trial={trial} alpha={a:?} semantic={ch:?} circle={z:?} queries={:?}", sets[0].1); }
    let tapes = (0..5)
        .map(|_| {
            (0..17)
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
                .collect()
        })
        .collect();
    Trial { a, ch, tapes }
}

/// Part 3: perturb one cell (no balance) and record which Boolean rows change.
fn cell_rows(public: Public<'_>, base: &Trace, ch: &Challenges, c: usize, r: usize, deltas: &[QM31]) -> Vec<usize> {
    let mut readers = vec![r, (r + N - 1) % N, r ^ 12];
    readers.sort_unstable();
    readers.dedup();
    let before = rows_subset(public, base, ch, &readers);
    assert!(before.iter().all(|x| x.is_ok()), "terminal error before c={c} r={r}");
    let mut changed = vec![];
    for d in deltas {
        let mut t = base.clone();
        t[c][r] = t[c][r].add(*d);
        let after = rows_subset(public, &t, ch, &readers);
        assert!(after.iter().all(|x| x.is_ok()), "terminal error after c={c} r={r}");
        for (i, &b) in readers.iter().enumerate() {
            if before[i] != after[i] && !changed.contains(&b) {
                changed.push(b);
            }
        }
    }
    changed.sort_unstable();
    changed
}

pub(super) fn main() {
    let start = Instant::now();
    let preflight = std::env::args().any(|x| x == "--preflight");
    let trials = if preflight { 1 } else { 20 };
    let elig = structural_checks();
    let (pubdata, instances) = real::instances();
    for tr in 0..trials {
        let t0 = Instant::now();
        let Trial { a, ch, tapes } = trial(tr, true);
        assert!(a.iter().all(|x| *x != QM31::ZERO && *x != QM31::ONE));
        // (C) raw semantic C1 + helper; (A) = Lean prepare(applyEligible t 0).
        let mut raws = vec![];
        let mut preps = vec![];
        for (w, inst) in instances.iter().enumerate() {
            let mut t: Trace = inst.compilation.semantic_c1.c1.iter()
                .map(|col| col.iter().map(|x| QM31::from_m31(*x)).collect()).collect();
            let h = build_pool_v1_pair_forest_copy_helper_v1(
                &inst.compilation.trace,
                inst.compilation.public_statement.live_snapshot.next_pair_index,
                ch.lambda, ch.chi).expect("helper");
            let nz_inactive = (0..N).filter(|&r| inactive(r) && h[r] != QM31::ZERO).count();
            t.push(h);
            let mut p = t.clone();
            for c in 0..16 { balance(&mut p[c], 1023); }
            // Z4c's trace applies balance_trace also to H1 (dep row 0).
            let mut z4c = t.clone();
            balance_trace(&mut z4c);
            let changed_1023: Vec<usize> = (0..16).filter(|&c| p[c][1023] != t[c][1023]).collect();
            let other_changed = (0..16).any(|c| (0..1023).any(|r| p[c][r] != t[c][r]));
            println!("Z6_PREP trial={tr} witness={w} helper_nonzero_inactive_rows={nz_inactive} balance_changes_row1023_columns={changed_1023:?} balance_changes_other_rows={other_changed} lean_A_equals_z4c_trace={}", p == z4c);
            raws.push(t);
            preps.push(p);
        }
        if tr == 0 {
            // Boolean-row claims equal the eq-weighted claims at the Boolean point.
            for &b in &[0usize, 12, 13, 15, 911, 1007, 1011, 1022, 1023] {
                assert_eq!(row_claims(&preps[0], b), point_claims(&preps[0], &bits(b)), "row claims b={b}");
            }
            println!("Z6_PREFLIGHT row_claims_match_point_claims=true rows=[0,12,13,15,911,1007,1011,1022,1023]");
        }
        for (k, tape) in tapes.iter().enumerate() {
            let mut e = tape.clone();
            e[16] = vec![QM31::ZERO; N];
            let mut pad = vec![QM31::ZERO; N];
            pad.copy_from_slice(&tape[16]);
            balance(&mut pad, 0);
            let cells = (0..16).map(|c| (0..N).filter(|&r| e[c][r] != QM31::ZERO).count()).sum::<usize>();
            println!("Z6_TAPE trial={tr} tape={k} eligible_nonzero_cells={cells} hash_eligible={:#018x} hash_h1pad={:#018x}",
                fnv(&e[..16].concat()), fnv(&pad));
        }
        let mut done = 0;
        for w in 0..10 {
            let public = Public::Transfer(&pubdata, &instances[w].compilation.public_statement);
            let va = all_rows(public, &preps[w], &ch);
            let vc = all_rows(public, &raws[w], &ch);
            let (_, s) = diff_report(&format!("Z6_AC trial={tr} witness={w}"), &vc, &va);
            println!("{s}");
            if tr == 0 && w == 0 {
                println!("Z6_FULL_A trial=0 witness=0 values={:?}", va.iter().map(|x| l(*x)).collect::<Vec<_>>());
            }
            for (k, tape) in tapes.iter().enumerate() {
                // (B) Lean actual(0,n): balance1023(t + eligible noise); helper invariant (Z6_STRUCT).
                let mut tb = raws[w].clone();
                for c in 0..16 {
                    for r in 0..N {
                        if eligible(c, r) { tb[c][r] = tb[c][r].add(tape[c][r]); }
                    }
                    balance(&mut tb[c], 1023);
                }
                let vb = all_rows(public, &tb, &ch);
                let (_, s) = diff_report(&format!("Z6_AB trial={tr} witness={w} tape={k} own_pair={}", k == w / 2), &va, &vb);
                println!("{s}");
                // Supplementary: Z4c's full tape including its H1 padding (Lean affine tape lane 1).
                let mut tp = tb.clone();
                let mut pad = tape[16].clone();
                balance(&mut pad, 0);
                for r in 0..N { tp[16][r] = tp[16][r].add(pad[r]); }
                let vp = all_rows(public, &tp, &ch);
                let mm = ch.mu.add(ch.mu.mul(ch.mu));
                let formula = (0..N).all(|b| vp[b].sub(va[b]) == mm.mul(pad[b]));
                let pad_rows = (0..N).filter(|&b| pad[b] != QM31::ZERO).count();
                let (_, s) = diff_report(&format!("Z6_APAD trial={tr} witness={w} tape={k} own_pair={} diff_equals_mu_plus_mu2_times_pad={formula} pad_nonzero_rows={pad_rows}", k == w / 2), &va, &vp);
                println!("{s}");
                done += 1;
            }
        }
        println!("Z6_TRIAL_DONE trial={tr} combos={done} wall_seconds={:.3}", t0.elapsed().as_secs_f64());
        if tr == 0 {
            // Part 3 on trial 0 challenges (and trial 1 for the random base).
            let public = Public::Transfer(&pubdata, &instances[0].compilation.public_statement);
            let mut rng = Rng(0x2636_5a7e_2026_1011);
            let deltas: Vec<QM31> = (0..2).map(|_| QM31::from_m31(rng.m())).collect();
            let mut random: Trace = (0..16).map(|_| (0..N).map(|_| QM31::from_m31(rng.m())).collect()).collect();
            random.push(preps[0][16].clone());
            let ch1 = trial(1, false).ch;
            let mut summary: std::collections::BTreeMap<String, usize> = Default::default();
            let mut sel = elig.clone();
            for c in 0..16 { if !sel.contains(&(c, 1023)) { sel.push((c, 1023)); } }
            for &(c, r) in &sel {
                let h = cell_rows(public, &preps[0], &ch, c, r, &deltas);
                let x = cell_rows(public, &random, &ch, c, r, &deltas);
                let y = cell_rows(public, &random, &ch1, c, r, &deltas);
                let tag = if eligible(c, r) && r != 1023 { "eligible" } else { "row1023" };
                *summary.entry(format!("{tag} honest={h:?}_rel random={x:?}_rel", h = h.iter().map(|b| *b as i64 - r as i64).collect::<Vec<_>>(), x = x.iter().map(|b| *b as i64 - r as i64).collect::<Vec<_>>())).or_default() += 1;
                if !h.is_empty() || !x.is_empty() || !y.is_empty() || r == 1023 {
                    println!("Z6_CELL c={c} r={r} kind={tag} honest_trial0={h:?} random_trial0={x:?} random_trial1={y:?}");
                }
            }
            for (k, v) in summary { println!("Z6_CELL_CLASS {k} count={v}"); }
            println!("Z6_CELL_DONE cells={} deltas=2 bases=honest_w0_t0,random_t0,random_t1", sel.len());
        }
        if preflight { println!("Z6_PREFLIGHT_DONE"); }
    }
    println!("Z6_DONE trials={trials} wall_seconds={:.3}", start.elapsed().as_secs_f64());
}
