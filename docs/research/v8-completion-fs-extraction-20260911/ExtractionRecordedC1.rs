//! First 256 C1 fibres from a finite recorded-answer prefix. No hash function,
//! fresh-query capability, full encoded word, coefficients, or witness input.
//! Record answers must be the caller's actual authorised prefix answers;
//! their source provenance/causal cut is NOT invented or verified here.
use std::collections::BTreeMap;
use super::authenticated_c1::{C1Openings, read31};

pub type Digest = [u8; 26];
#[derive(Clone, Debug)]
pub struct RecordedQuery { pub input: Vec<u8>, pub answer: [u8; 32] }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccessError {
    QueryBudget, ByteBudget, MissingRoot, MissingPreimage, ForwardReference,
    InconsistentAnswer, TruncatedCollision, MalformedNode, MalformedLeaf,
    NoncanonicalLeaf, LookupBudget,
}
#[derive(Clone, Copy, Debug)]
pub struct Limits { pub records: usize, pub raw_bytes: usize, pub lookups: usize }
#[derive(Clone, Debug, Default)]
pub struct AccessStats {
    pub records: usize, pub raw_bytes: usize, pub unique_inputs: usize,
    pub lookups: usize, pub leaves: usize, pub parents: usize,
    pub frontier_digests: usize,
}
pub struct Material { pub openings: C1Openings, pub stats: AccessStats }
struct Index<'a> {
    records: &'a [RecordedQuery], first: BTreeMap<Digest, usize>,
    stats: AccessStats, remaining: usize,
}
pub fn truncated(answer: &[u8; 32]) -> Digest { answer[..26].try_into().unwrap() }
impl<'a> Index<'a> {
    fn new(records: &'a [RecordedQuery], limits: Limits) -> Result<Self, AccessError> {
        if records.len() > limits.records { return Err(AccessError::QueryBudget); }
        let mut by_input: BTreeMap<&[u8], [u8; 32]> = BTreeMap::new();
        let mut first: BTreeMap<Digest, usize> = BTreeMap::new();
        let mut bytes = 0usize;
        for (i, record) in records.iter().enumerate() {
            bytes = bytes.checked_add(record.input.len()).ok_or(AccessError::ByteBudget)?;
            if bytes > limits.raw_bytes { return Err(AccessError::ByteBudget); }
            if let Some(answer) = by_input.get(record.input.as_slice()) {
                if answer != &record.answer { return Err(AccessError::InconsistentAnswer); }
            } else { by_input.insert(record.input.as_slice(), record.answer); }
            let target = truncated(&record.answer);
            if let Some(&earlier) = first.get(&target) {
                if records[earlier].input != record.input {
                    return Err(AccessError::TruncatedCollision);
                }
            } else { first.insert(target, i); }
        }
        let stats = AccessStats { records: records.len(), raw_bytes: bytes,
            unique_inputs: by_input.len(), ..AccessStats::default() };
        Ok(Self { records, first, stats, remaining: limits.lookups })
    }
    fn read(&mut self, target: Digest, before: usize, root: bool)
        -> Result<(usize, &'a [u8]), AccessError>
    {
        if self.remaining == 0 { return Err(AccessError::LookupBudget); }
        self.remaining -= 1; self.stats.lookups += 1;
        let i = *self.first.get(&target).ok_or(if root {
            AccessError::MissingRoot
        } else { AccessError::MissingPreimage })?;
        if i >= before { return Err(AccessError::ForwardReference); }
        Ok((i, &self.records[i].input))
    }
    fn walk(&mut self, height: usize, target: Digest, before: usize,
        output: &mut C1Openings) -> Result<(), AccessError>
    {
        let (ordinal, input) = self.read(target, before, height == 18)?;
        if height == 0 {
            if input.len() != 437 || input[..2] != [0x10, 0x71] {
                return Err(AccessError::MalformedLeaf);
            }
            for limb in 0..104 {
                read31(&input[2..405], 31 * limb).map_err(|_|AccessError::NoncanonicalLeaf)?;
            }
            output.ids.push(output.leaves.len() as u32);
            output.leaves.push(input[2..405].to_vec());
            output.salts.push(input[405..437].try_into().unwrap());
            self.stats.leaves += 1;
            return Ok(());
        }
        if input.len() != 53 || input[0] != 0x11 { return Err(AccessError::MalformedNode); }
        let left: Digest = input[1..27].try_into().unwrap();
        let right: Digest = input[27..53].try_into().unwrap();
        self.stats.parents += 1;
        self.walk(height - 1, left, ordinal, output)?;
        if height <= 8 {
            self.walk(height - 1, right, ordinal, output)?;
        } else {
            // Source minimal-multiproof order is bottom-up: recurse before
            // appending the sibling at heights 8 through 17.
            output.frontier.extend(right);
            self.stats.frontier_digests += 1;
        }
        Ok(())
    }
}

/// Returns the exact C1Openings shape consumed by unchanged recover_c1.
/// No placeholder/default preimage is created for an unresolved target.
/// Off-path sibling *digests* come from recorded parents; their preimages
/// are not needed, read, queried, or completed.
pub fn extract_first_256(records: &[RecordedQuery], root: Digest, limits: Limits)
    -> Result<Material, AccessError>
{
    let mut index = Index::new(records, limits)?;
    let mut openings = C1Openings { ids: Vec::new(), leaves: Vec::new(),
        salts: Vec::new(), frontier: Vec::new() };
    index.walk(18, root, records.len(), &mut openings)?;
    debug_assert_eq!((openings.ids.len(), openings.leaves.len(), openings.salts.len(),
        openings.frontier.len()), (256, 256, 256, 260));
    debug_assert_eq!((index.stats.lookups, index.stats.leaves, index.stats.parents,
        index.stats.frontier_digests), (521, 256, 265, 10));
    Ok(Material { openings, stats: index.stats })
}
