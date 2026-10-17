//! Actual saved S2 semantic run; only symmetric fault wrappers are synthetic.
use super::*;
use alloc::{vec, vec::Vec};
use sha2::{Digest, Sha256};
use std::cell::RefCell;
use wire::ValidatedRecord;

const PROOF: &[u8] = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-proof.bin"));
const PUBLIC: &[u8] = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-public-asf8.bin"));

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
enum Fault {
    #[default] None,
    Parse, Public, Begin,
    Lookup(u8, usize), Decode(u8), Boundary(u8), Semantic(u8),
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    Parse, Public([u8; 32]), Begin([u8; 32], u8),
    Lookup(u8, usize), Decode(u8, usize, usize),
    Semantic(u8, [u8; 32], u8), SemanticDone(u8, [u8; 32], u8),
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
struct Log {
    fault: Fault, events: Vec<Event>,
    phases: Vec<crate::verifier::Phase>,
    digests: Vec<(Vec<Vec<u8>>, [u8; 32])>,
    lookups: [usize; 10],
}
std::thread_local! {static LOG: RefCell<Log> = RefCell::new(Log::default());}
fn fault() -> Fault { LOG.with(|s| s.borrow().fault) }
fn event(e: Event) { LOG.with(|s| s.borrow_mut().events.push(e)); }

pub(super) fn parse(bytes: &[u8]) -> Result<Prefix<'_>, Error> {
    event(Event::Parse);
    if fault() == Fault::Parse { return Err(Error::InvalidRow); }
    Prefix::parse(bytes)
}
pub(super) fn public_transcript<H: Digest32>(public: Public<'_>, hash: H, root: &[u8; 32]) -> Result<SemanticTranscript<H>, Error> {
    event(Event::Public(*root));
    if fault() == Fault::Public { return Err(Error::Public); }
    super::public_transcript(public, hash, root)
}
pub(super) fn begin<H: Digest32>(prefix: &Prefix<'_>, transcript: &mut SemanticTranscript<H>) -> Result<Challenges, Error> {
    event(Event::Begin(transcript.state(), transcript.next_row()));
    if fault() == Fault::Begin { return Err(Error::RowOrder { expected: 0, actual: 1 }); }
    wire::begin(prefix, transcript)
}
pub(super) fn lookup<'a>(prefix: &Prefix<'a>, row: u8) -> Result<ValidatedRecord<'a>, Error> {
    assert!((15..=24).contains(&row));
    let n = LOG.with(|s| { let mut s = s.borrow_mut(); let n = s.lookups[(row - 15) as usize]; s.lookups[(row - 15) as usize] += 1; n });
    event(Event::Lookup(row, n));
    if fault() == Fault::Lookup(row, n) { return Err(Error::InvalidRow); }
    prefix.validated_record(row)
}
pub(super) fn decode<const N: usize>(prefix: &Prefix<'_>, row: u8, offset: usize) -> Result<[QM31; N], Error> {
    let record = lookup(prefix, row)?;
    event(Event::Decode(row, N, offset));
    if fault() == Fault::Decode(row) { return Err(Error::NonCanonical { row, value: 0 }); }
    let mut polynomial = record.decode_k::<N>(offset)?;
    if fault() == Fault::Boundary(row) {
        assert_eq!(N, 28);
        // Perturb coefficient1 once. The production boundary fold and its
        // original error branch execute unchanged in both source bodies.
        polynomial[1] = polynomial[1].add(QM31::ONE);
    }
    Ok(polynomial)
}
pub(super) fn semantic_validated<H: Digest32>(transcript: &mut SemanticTranscript<H>, record: ValidatedRecord<'_>) -> Result<QM31, Error> {
    let row = record.row();
    event(Event::Semantic(row, transcript.state(), transcript.next_row()));
    if fault() == Fault::Semantic(row) { return Err(Error::RowOrder { expected: row, actual: row + 1 }); }
    let value = transcript.semantic_validated(record)?;
    event(Event::SemanticDone(row, transcript.state(), transcript.next_row()));
    Ok(value)
}
#[derive(Clone, Copy)] struct RecordedSha;
impl Digest32 for RecordedSha {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
        let mut h = Sha256::new();
        for p in parts { h.update(p); }
        let out = h.finalize().into();
        LOG.with(|s| s.borrow_mut().digests.push((parts.iter().map(|x| x.to_vec()).collect(), out)));
        out
    }
}
fn observer(p: crate::verifier::Phase) { LOG.with(|s| s.borrow_mut().phases.push(p)); }
fn k_bytes(x: QM31, bytes: &mut Vec<u8>) { let mut b = [0; 16]; x.write_le_bytes(&mut b); bytes.extend_from_slice(&b); }
fn snapshot(out: Verified<RecordedSha>) -> Vec<u8> {
    let mut b = Vec::new();
    for root in out.roots { b.extend_from_slice(&root); }
    for x in [out.challenges.lambda, out.challenges.chi, out.challenges.theta] { k_bytes(x, &mut b); }
    for x in out.challenges.zc { k_bytes(x, &mut b); }
    for x in [out.challenges.mu, out.challenges.eta] { k_bytes(x, &mut b); }
    for x in out.alpha { k_bytes(x, &mut b); }
    for row in *out.claims { for x in row { k_bytes(x, &mut b); } }
    for x in out.extra { k_bytes(x, &mut b); }
    for x in out.before_z1 { k_bytes(x, &mut b); }
    b.extend_from_slice(&out.state_before_z0);
    for z in out.z { k_bytes(z.x, &mut b); k_bytes(z.y, &mut b); }
    b.extend_from_slice(&out.transcript.state()); b.push(out.transcript.next_row());
    for row in out.round_checks { for x in row { k_bytes(x, &mut b); } }
    k_bytes(out.terminal, &mut b); k_bytes(out.masked_terminal, &mut b);
    b
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Outcome { result: Result<Vec<u8>, Error>, log: Log, values: Vec<(u16, usize, [u8; 32])> }
fn run(old: bool, configured: Fault, observed: bool) -> Outcome {
    let statement = aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(PUBLIC).unwrap();
    let public = aspis_prover::r0_fixture::statement_public(&statement);
    let view = crate::verifier::View::parse(PROOF).unwrap();
    LOG.with(|s| *s.borrow_mut() = Log { fault: configured, ..Log::default() });
    let _ = crate::trace::take();
    let obs = if observed { Some(observer as fn(crate::verifier::Phase)) } else { None };
    let result = if old { migration_old_verify_observed(public, view.semantic, RecordedSha, obs) }
        else { verify_observed(public, view.semantic, RecordedSha, obs) }.map(snapshot);
    Outcome { result, log: LOG.with(|s| s.borrow().clone()), values: crate::trace::take() }
}
fn expected_error(f: Fault) -> Option<Error> {
    match f {
        Fault::None => None,
        Fault::Parse | Fault::Lookup(_, _) => Some(Error::InvalidRow),
        Fault::Public => Some(Error::Public),
        Fault::Begin => Some(Error::RowOrder { expected: 0, actual: 1 }),
        Fault::Decode(row) => Some(Error::NonCanonical { row, value: 0 }),
        Fault::Boundary(row) => Some(Error::Boundary { round: (row - 15) as usize }),
        Fault::Semantic(row) => Some(Error::RowOrder { expected: row, actual: row + 1 }),
    }
}
#[test]
fn verify_saved_s2_exact_old_new_all_round_failures_and_success() {
    assert_eq!(&PROOF[..8], b"R1P3COST");
    let mut faults = vec![Fault::None, Fault::Parse, Fault::Public, Fault::Begin];
    for row in 15..=24 { faults.extend([Fault::Lookup(row, 0), Fault::Decode(row), Fault::Boundary(row), Fault::Lookup(row, 1), Fault::Semantic(row)]); }
    assert_eq!(faults.len(), 54);
    for observed in [false, true] {
        let success = run(true, Fault::None, observed);
        assert!(success.result.is_ok(), "actual saved S2 semantic verification must succeed");
        for configured in &faults {
            let old = run(true, *configured, observed);
            let new = run(false, *configured, observed);
            assert_eq!(old, new, "fault={configured:?} observed={observed}");
            assert_eq!(old.result.as_ref().err().copied(), expected_error(*configured));
            assert_eq!(old.log.digests, success.log.digests[..old.log.digests.len()]);
            assert_eq!(old.values, success.values[..old.values.len()]);
            assert_eq!(old.log.phases, success.log.phases[..old.log.phases.len()]);
            assert_eq!(old.log.events, success.log.events[..old.log.events.len()]);
            if !observed || !cfg!(feature="detail-phases") { assert!(old.log.phases.is_empty()); }
            let digest: [u8; 32] = Sha256::digest(std::format!("{old:?}").as_bytes()).into();
            std::println!("VERIFY_REAL_S2_CASE fault={configured:?} observed={observed} detail_phases={} old_new_equal=true error={:?} digest_calls={} trace_values={} events={} phases={} full_outcome_sha256={digest:02x?}", cfg!(feature="detail-phases"), old.result.as_ref().err(), old.log.digests.len(), old.values.len(), old.log.events.len(), old.log.phases.len());
        }
    }
    std::println!("VERIFY_REAL_S2_PASS cases=108 faults=53 rows=15..24 observers=Some,None detail_phases={}", cfg!(feature="detail-phases"));
}
