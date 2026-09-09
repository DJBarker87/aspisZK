//! Research-only actual-answer recorder and prefix-local C1 resolver.
//! No extra oracle calls, default-subtree hashing, or witness inputs.
//! This is a Rust model/differential check, not a translated-source theorem.
use std::{cell::RefCell, collections::BTreeMap};

pub type Digest208 = [u8; 26];
#[derive(Clone)]
pub struct Answer { pub input: Vec<u8>, pub full: [u8; 32] }
impl Answer { fn digest(&self) -> Digest208 { self.full[..26].try_into().unwrap() } }
thread_local! { static LOG: RefCell<Option<Vec<Answer>>> = const { RefCell::new(None) }; }
pub fn begin() { LOG.with(|l| { let mut l = l.borrow_mut(); assert!(l.is_none()); *l = Some(vec![]); }); }
pub fn record(parts: &[&[u8]], answer: [u8; 32]) {
    LOG.with(|l| { if let Some(l) = l.borrow_mut().as_mut() { l.push(Answer { input: parts.concat(), full: answer }); } });
}
pub fn freeze() -> Vec<Answer> { LOG.with(|l| l.borrow_mut().take().expect("active actual-answer recorder")) }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Leaf { pub value: [u8; 403], pub salt: [u8; 32] }
impl Default for Leaf { fn default() -> Self { Self { value: [0; 403], salt: [0; 32] } } }
#[derive(Debug, PartialEq, Eq)]
pub enum Failure { Collision208, InconsistentAnswer, Position, Fuel }
#[derive(Debug, PartialEq, Eq)]
pub enum Resolution {
    Resolved { leaf: Leaf, path_queries: Vec<usize> },
    Unresolved { target: Digest208, height: usize, path_queries: Vec<usize> },
}
pub struct Prefix {
    answers: Vec<Answer>,
    first: BTreeMap<Digest208, usize>,
}
impl Prefix {
    pub fn new(answers: Vec<Answer>) -> Result<Self, Failure> {
        let mut first = BTreeMap::<Digest208, usize>::new();
        for (i, a) in answers.iter().enumerate() {
            if let Some(&old) = first.get(&a.digest()) {
                if answers[old].input != a.input { return Err(Failure::Collision208); }
            } else { first.insert(a.digest(), i); }
        }
        // Same-input/different-full-answer is not a 208-bit collision.
        // Check it separately even if the 26-byte projections differ.
        let mut by_input = BTreeMap::new();
        for a in &answers {
            if let Some(old) = by_input.insert(a.input.as_slice(), a.full) {
                if old != a.full { return Err(Failure::InconsistentAnswer); }
            }
        }
        Ok(Self { answers, first })
    }
    pub fn counts(&self) -> (usize, usize, usize) {
        (self.answers.len(), self.first.len(), self.answers.iter().map(|a| a.input.len()).sum())
    }
    /// First matching recorded digest, then typed parse, then the high-bit
    /// path choice. Height is the termination measure: no chronological-child
    /// premise and no hashes of an unresolved/default subtree are added.
    pub fn resolve(&self, root: Digest208, depth: usize, position: usize, mut fuel: usize)
        -> Result<Resolution, Failure> {
        if depth > 18 || position >= (1usize << depth) { return Err(Failure::Position); }
        let mut target = root; let mut path_queries = vec![];
        for height in (0..=depth).rev() {
            if fuel == 0 { return Err(Failure::Fuel); } fuel -= 1;
            let Some(&index) = self.first.get(&target) else {
                return Ok(Resolution::Unresolved { target, height, path_queries });
            };
            path_queries.push(index);
            let input = &self.answers[index].input;
            if height == 0 {
                if input.len() == 437 && input[..2] == [0x10, 0x71] {
                    return Ok(Resolution::Resolved { leaf: Leaf {
                        value: input[2..405].try_into().unwrap(), salt: input[405..437].try_into().unwrap()
                    }, path_queries });
                }
            } else if input.len() == 53 && input[0] == 0x11 {
                let start = if position & (1 << (height - 1)) == 0 { 1 } else { 27 };
                target = input[start..start + 26].try_into().unwrap();
                continue;
            }
            return Ok(Resolution::Unresolved { target, height, path_queries });
        }
        unreachable!()
    }
    pub fn totalized_leaf(&self, root: Digest208, depth: usize, position: usize) -> Result<Leaf, Failure> {
        match self.resolve(root, depth, position, depth + 1)? {
            Resolution::Resolved { leaf, .. } => Ok(leaf),
            Resolution::Unresolved { .. } => Ok(Leaf::default()),
        }
    }
}

/// Check actual q22 proof records against the early resolver AND the separate
/// public verifier's recorded authentication paths. The only extractor input
/// here is the early answers/root; queried bytes are comparison targets.
pub fn check_execution(early: Prefix, verifier_answers: Vec<Answer>, root: Digest208,
    queries: &[u32], records: &[u8]) {
    assert_eq!(queries.len(), 22); assert_eq!(records.len(), 22 * 621);
    let verifier = Prefix::new(verifier_answers).expect("consistent verifier hash view");
    let (raw, unique, raw_bytes) = early.counts();
    let (verifier_raw, _, _) = verifier.counts();
    let mut path_checks = 0;
    for (&position, record) in queries.iter().zip(records.chunks_exact(621)) {
        let expected = Leaf { value: record[..403].try_into().unwrap(), salt: record[589..621].try_into().unwrap() };
        let Resolution::Resolved { leaf, path_queries } = early.resolve(root, 18, position as usize, 19).unwrap()
            else { panic!("honest early C1 path unresolved"); };
        assert_eq!(leaf, expected); assert_eq!(path_queries.len(), 19);
        let Resolution::Resolved { leaf, path_queries } = verifier.resolve(root, 18, position as usize, 19).unwrap()
            else { panic!("actual verifier trace lacks accepted path"); };
        assert_eq!(leaf, expected); assert_eq!(path_queries.len(), 19);
        path_checks += path_queries.len();
    }
    println!("EARLY_C1_TRACE raw={raw} unique={unique} input_bytes={raw_bytes} verifier_calls={verifier_raw} accepted_openings=22 path_memberships={path_checks} pre_lambda_chi=true actual_answers=true resolver_hash_calls=0 raw_trace_persisted=false");
}

#[cfg(test)] mod tests {
    use super::*;
    // Synthetic oracle answers test resolver logic, not cryptographic odds.
    fn answer(input: Vec<u8>, n: u8) -> Answer { Answer { input, full: [n; 32] } }
    fn leaf(n: u8) -> Answer { let mut x = vec![0x10, 0x71]; x.resize(437, 0); x[2] = n; answer(x, n) }
    fn node(l: u8, r: u8, n: u8) -> Answer { let mut x = vec![0x11]; x.extend([l; 26]); x.extend([r; 26]); answer(x, n) }
    #[test] fn prefix_local_partial_resolution() {
        let inputs = [leaf(1), leaf(2), node(1, 2, 3)];
        // Every subset, both positions, all included-input permutations.
        let mut cases = 0;
        for mask in 0..8 { for order in [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]] {
            let log: Vec<_> = order.into_iter().filter(|i| mask & (1 << i) != 0).map(|i| inputs[i].clone()).collect();
            let p = Prefix::new(log).unwrap();
            for position in 0..2 {
                let got = p.resolve([3; 26], 1, position, 2).unwrap();
                let resolved = mask & 4 != 0 && mask & (1 << position) != 0;
                assert_eq!(matches!(got, Resolution::Resolved { .. }), resolved);
                assert_eq!(p.totalized_leaf([3; 26],1,position).unwrap().value[0], if resolved { (position + 1) as u8 } else { 0 });
                cases += 1;
            }
        }}
        assert_eq!(cases,96);
        let p = Prefix::new(inputs.to_vec()).unwrap();
        assert_eq!(p.resolve([3;26],1,2,2),Err(Failure::Position));
        assert_eq!(p.resolve([3;26],1,0,1),Err(Failure::Fuel));
        let p = Prefix::new(vec![answer(vec![0x10,0xf1],3)]).unwrap();
        assert!(matches!(p.resolve([3;26],1,0,2).unwrap(),Resolution::Unresolved { target:[3,..],height:1,.. }));
        let mut nc=leaf(1); nc.input[2..6].fill(255);
        assert_eq!(Prefix::new(vec![nc]).unwrap().totalized_leaf([1;26],0,0).unwrap().value[0],255);
        // Raw bytes remain intact; canonical field totalization is downstream.
    }
    #[test] fn answer_consistency_and_collisions() {
        assert!(matches!(Prefix::new(vec![answer(vec![1],1),answer(vec![2],1)]),Err(Failure::Collision208)));
        assert!(matches!(Prefix::new(vec![answer(vec![1],1),answer(vec![1],2)]),Err(Failure::InconsistentAnswer)));
        let a=answer(vec![1],1);let mut b=a.clone();b.full[31]^=1;
        assert!(matches!(Prefix::new(vec![a.clone(),b]),Err(Failure::InconsistentAnswer)));
        assert_eq!(Prefix::new(vec![a.clone(),a]).unwrap().counts(),(2,1,2));
    }
    #[test] fn recording_preserves_segmentation_and_frozen_prefix() {
        begin(); record(&[&[1,2],&[3]], [7;32]); let early=freeze();
        begin(); record(&[&[4]], [8;32]); let later=freeze();
        assert_eq!(early[0].input,vec![1,2,3]);assert_eq!(early[0].full,[7;32]);
        assert_eq!(later[0].input,vec![4]);assert_eq!(early.len(),1);
    }
}
