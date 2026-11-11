//! Aspis one-transaction verifier: mutation campaign over the two recorded
//! devnet proofs (PIN2 run of 11 November 2026, re-packed into the
//! one-transaction format).
//!
//! Purpose: to compare two builds of the verifier source. The tool is built
//! once in each source tree and run on the same inputs; the two output files
//! must be byte-identical. Every line is one corrupted proof and the verifier's
//! verdict on it (`Ok` or the error variant) together with the number of
//! observer marks reached, so a rewrite that drops a check, changes the order
//! of two checks, or changes which error is returned shows as a differing line.
//!
//! This is a test on these mutants of these two proofs. It is not a proof that
//! the two sources agree on every input.
//!
//! Mutants per proof (offsets are bytes of the 55,815-byte proof):
//! - `bit i`: bit `i % 8` of byte `i` flipped, every `i` (or every `stride`-th);
//! - `ff4 i`: bytes `i..i+4` set to 0xFF (a non-canonical field limb), every
//!   4-aligned `i`, and every `i` congruent to the node region's start;
//! - `zero32 k`: the 32 bytes at `OFF_NODES + 32k` zeroed, every node and
//!   certificate block;
//! - `swap32 k`: node blocks `k` and `k + 1` exchanged;
//! - `len`: the proof shortened by one byte, lengthened by one zero byte,
//!   halved, and empty.
//! The unmutated proof is the first line and must be `Ok`.
//!
//! usage: one_tx_mutants <transactions.json> <out.txt> [stride] [threads]
use anyhow::{anyhow, ensure, Context, Result};
use aspis_r1_cost_probe::verifier::{candidate::fused, Phase};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{cell::Cell, env, fs, path::Path};

#[derive(Clone, Copy)]
struct Sha;
impl aspis_core::Digest32 for Sha {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
        let mut d = Sha256::new();
        for p in parts {
            d.update(p);
        }
        d.finalize().into()
    }
}

thread_local! { static MARKS: Cell<u32> = const { Cell::new(0) }; }
fn observe(_: Phase) {
    MARKS.with(|c| c.set(c.get() + 1));
}

fn unbase64(s: &str) -> Result<Vec<u8>> {
    let mut out = Vec::with_capacity(s.len() / 4 * 3);
    let (mut acc, mut bits) = (0u32, 0u32);
    for c in s.bytes() {
        let v = match c {
            b'A'..=b'Z' => c - b'A',
            b'a'..=b'z' => c - b'a' + 26,
            b'0'..=b'9' => c - b'0' + 52,
            b'+' => 62,
            b'/' => 63,
            b'=' => break,
            _ => return Err(anyhow!("base64 byte {c}")),
        };
        acc = (acc << 6) | v as u32;
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
            acc &= (1 << bits) - 1;
        }
    }
    Ok(out)
}

/// Data of the first recorded pre-state account owned by `owner` that `pick` accepts.
fn recorded(tx: &Value, owner: &str, pick: impl Fn(usize) -> bool) -> Result<Vec<u8>> {
    for a in tx["pre"]["accounts"].as_array().context("pre.accounts")? {
        if !a["exists"].as_bool().unwrap_or(false) || a["owner"].as_str() != Some(owner) {
            continue;
        }
        let data = unbase64(a["data_base64"].as_str().context("data")?)?;
        ensure!(data.len() as u64 == a["space"].as_u64().context("space")?, "recorded data length");
        if pick(data.len()) {
            return Ok(data);
        }
    }
    Err(anyhow!("no such recorded account"))
}

#[derive(Clone, Copy)]
enum Mutant {
    None,
    Bit(usize),
    Ff4(usize),
    Zero32(usize),
    Swap32(usize),
    Shorter,
    Longer,
    Half,
    Empty,
}

impl Mutant {
    fn name(self) -> String {
        match self {
            Mutant::None => "none".into(),
            Mutant::Bit(i) => format!("bit {i}"),
            Mutant::Ff4(i) => format!("ff4 {i}"),
            Mutant::Zero32(k) => format!("zero32 {k}"),
            Mutant::Swap32(k) => format!("swap32 {k}"),
            Mutant::Shorter => "len shorter".into(),
            Mutant::Longer => "len longer".into(),
            Mutant::Half => "len half".into(),
            Mutant::Empty => "len empty".into(),
        }
    }
    fn apply(self, base: &[u8]) -> Vec<u8> {
        let mut m = base.to_vec();
        let nodes = fused::summed_format::OFF_NODES;
        match self {
            Mutant::None => {}
            Mutant::Bit(i) => m[i] ^= 1 << (i % 8),
            Mutant::Ff4(i) => m[i..i + 4].fill(0xFF),
            Mutant::Zero32(k) => m[nodes + 32 * k..nodes + 32 * k + 32].fill(0),
            Mutant::Swap32(k) => {
                let (a, b) = m[nodes + 32 * k..nodes + 32 * k + 64].split_at_mut(32);
                a.swap_with_slice(b);
            }
            Mutant::Shorter => {
                m.pop();
            }
            Mutant::Longer => m.push(0),
            Mutant::Half => m.truncate(base.len() / 2),
            Mutant::Empty => m.clear(),
        }
        m
    }
}

fn mutants(len: usize, stride: usize) -> Vec<Mutant> {
    let nodes = fused::summed_format::OFF_NODES;
    let blocks = (len - nodes) / 32;
    let mut out = vec![Mutant::None];
    out.extend((0..len).step_by(stride).map(Mutant::Bit));
    out.extend((0..len - 3).step_by(4 * stride).map(Mutant::Ff4));
    if nodes % 4 != 0 {
        out.extend((nodes..len - 3).step_by(4 * stride).map(Mutant::Ff4));
    }
    out.extend((0..blocks).map(Mutant::Zero32));
    out.extend((0..blocks.saturating_sub(1)).map(Mutant::Swap32));
    out.extend([Mutant::Shorter, Mutant::Longer, Mutant::Half, Mutant::Empty]);
    out
}

fn main() -> Result<()> {
    ensure!(!cfg!(debug_assertions), "release build only");
    let args: Vec<_> = env::args().collect();
    ensure!(args.len() >= 3 && args.len() <= 5, "usage: one_tx_mutants <transactions.json> <out.txt> [stride] [threads]");
    let all: Value = serde_json::from_slice(&fs::read(&args[1])?)?;
    let out = Path::new(&args[2]);
    ensure!(!out.exists(), "output exists: {}", out.display());
    let stride: usize = args.get(3).map(|s| s.parse()).transpose()?.unwrap_or(1);
    let threads: usize = args.get(4).map(|s| s.parse()).transpose()?.unwrap_or(4);
    ensure!(stride >= 1 && threads >= 1, "stride and threads must be positive");
    let upload = all["upload_program"].as_str().context("upload id")?.to_string();
    let find = |name: String| all["transactions"].as_array().unwrap().iter().find(|t| t["name"] == name.as_str()).cloned().ok_or_else(|| anyhow!("no transaction {name}"));
    let prefix = aspis_statement::pool_v1::POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let mut text = String::new();
    for operation in ["transfer", "withdrawal"] {
        let proof = recorded(&find(format!("{operation}-stage2"))?, &upload, |n| n > 50_000)?;
        let public = recorded(&find(format!("{operation}-stage1"))?, &upload, |n| n == 1880)?;
        let statement = aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public).map_err(|e| anyhow!("statement: {e:?}"))?;
        let packed = fused::to_summed_format(statement.semantic_public(), &proof[prefix..], Sha).map_err(|e| anyhow!("re-pack: {e:?}"))?;
        ensure!(packed.len() == fused::summed_format::PROOF_BYTES, "packed length");
        let list = mutants(packed.len(), stride);
        let chunk = list.len().div_ceil(threads);
        let lines: Vec<Vec<String>> = std::thread::scope(|scope| {
            let handles: Vec<_> = list
                .chunks(chunk)
                .map(|part| {
                    let (packed, statement) = (&packed, &statement);
                    scope.spawn(move || {
                        part.iter()
                            .map(|m| {
                                let bytes = m.apply(packed);
                                MARKS.with(|c| c.set(0));
                                let verdict = fused::verify_summed_format(statement.semantic_public(), &bytes, Sha, Some(observe));
                                let marks = MARKS.with(|c| c.get());
                                match verdict {
                                    Ok(()) => format!("{operation} {} Ok {marks}", m.name()),
                                    Err(e) => format!("{operation} {} {e:?} {marks}", m.name()),
                                }
                            })
                            .collect::<Vec<_>>()
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().expect("worker")).collect()
        });
        let lines: Vec<String> = lines.into_iter().flatten().collect();
        ensure!(lines[0].contains(" none Ok "), "the unmutated {operation} proof is not accepted: {}", lines[0]);
        let packed_sha: [u8; 32] = Sha256::digest(&packed).into();
        text.push_str(&format!("# {operation} proof sha256 {} mutants {}\n", packed_sha.iter().map(|b| format!("{b:02x}")).collect::<String>(), lines.len()));
        for l in lines {
            text.push_str(&l);
            text.push('\n');
        }
    }
    fs::write(out, text)?;
    Ok(())
}
