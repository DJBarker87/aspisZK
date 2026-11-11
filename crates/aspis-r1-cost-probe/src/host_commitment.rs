//! UNPROVED COST PROBE. Isolated packed commitments and native encoder.
use alloc::vec::Vec;
use aspis_core::{HashFn,field::{WideExact as E,M31,QM31},r0::{domain::{self,FibreIndex,Point},fold,merkle,wire::FibreOpening,opening::LANES,heap::filled,CodeField,Error,Message,FIBRE_COUNT,WORD_LEN}};
/// Natural-product evaluation tree. Coordinates are always in F.
pub struct EncodingDomain {
    xy: Vec<Point<M31>>,
    levels: Vec<Vec<M31>>,
}
impl EncodingDomain {
    pub fn new() -> Result<Self, Error> {
        let xy = domain_points()?;
        let mut levels = Vec::new();
        levels.try_reserve_exact(9).map_err(|_| Error::Allocation)?;
        let first = domain_first_level(&xy)?;
        levels.push(first);
        let levels = domain_append_levels(levels, 0)?;
        Ok(Self { xy, levels })
    }
    pub fn evaluate<T: CodeField>(&self, coefficients: &[T], depth: usize) -> Result<Vec<T>, Error> {
        let count = self.levels[depth].len();
        if coefficients.len() == 1 {
            return filled(count, coefficients[0]);
        }
        let mut even = filled(coefficients.len() / 2, T::ZERO)?;
        let mut odd = filled(even.len(), T::ZERO)?;
        split_coefficients(coefficients, &mut even, &mut odd);
        let a = self.evaluate(&even, depth + 1)?;
        let b = self.evaluate(&odd, depth + 1)?;
        let mut out = filled(count, T::ZERO)?;
        merge_evaluations(&self.levels[depth], &a, &b, &mut out);
        Ok(out)
    }
    /// Exact §3 encoder at every stored index, O(N log 1024), using
    /// N_(2j)(x)=N_j(2x²−1), N_(2j+1)(x)=x*N_j(2x²−1).
    pub fn encode<T: CodeField>(&self, message: &Message<T>) -> Result<Vec<T>, Error> {
        let mut channels = Vec::new();
        channels
            .try_reserve_exact(4)
            .map_err(|_| Error::Allocation)?;
        channels.push(self.evaluate(&channel_coefficients(message, 0), 0)?);
        channels.push(self.evaluate(&channel_coefficients(message, 1), 0)?);
        channels.push(self.evaluate(&channel_coefficients(message, 2), 0)?);
        channels.push(self.evaluate(&channel_coefficients(message, 3), 0)?);
        let mut word = filled(WORD_LEN, T::ZERO)?;
        encode_fibres(&self.xy, &channels, &mut word);
        Ok(word)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitmentTime {
    C1,
    C2,
}
enum Word {
    Base(Vec<M31>),
    Secure(Vec<QM31>),
}
impl Word {
    fn value(&self, i: usize) -> E {
        match self {
            Self::Base(w) => E::from_m31(w[i]),
            Self::Secure(w) => E::from_qm31(w[i]),
        }
    }
}
/// C1 can be constructed before λ/χ; C2 separately after them. The 29-entry
/// input permits virtual lanes but only this time's lanes are committed.
pub struct Commitment {
    time: CommitmentTime,
    lanes: Vec<usize>,
    messages: Vec<Message<E>>,
    words: Vec<Word>,
    /// Binary tree of the adopted format (PREREG-PROOF-SIZE-2). The eight-way
    /// tree is retired: a prover build cannot emit an eight-way proof.
    tree: crate::multiproof::BinaryTree,
    private_salts: Option<PrivateSalts>,
}
/// Host-only secret salts retained until queried openings have been emitted.
/// Drop overwrites the full salt buffer so salts for unopened leaves are not
/// left in the allocator after proof construction.
pub struct PrivateSalts(Vec<[u8; 32]>);
impl PrivateSalts {
    pub fn new(values: Vec<[u8; 32]>) -> Self { Self(values) }
    pub fn get(&self, index: usize) -> &[u8; 32] { &self.0[index] }
    fn len(&self) -> usize { self.0.len() }
}
/// One volatile 32-byte clear. Kept as a separate item so that an extraction
/// can treat it as an opaque contract (Aeneas has no `&raw mut`).
#[inline(always)]
fn clear_private_salt(salt: &mut [u8; 32]) {
    // SAFETY: the caller passes a uniquely borrowed salt cell.
    unsafe { core::ptr::write_volatile(salt, [0; 32]); }
}
impl Drop for PrivateSalts {
    fn drop(&mut self) {
        let mut index = 0;
        while index < self.0.len() {
            clear_private_salt(&mut self.0[index]);
            index += 1;
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}
impl Commitment {
    pub fn new_salted(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        salts: PrivateSalts,
    ) -> Result<Self, Error> {
        Self::build(hash, domain, time, messages, variant, Some(salts))
    }
    fn build(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        private_salts: Option<PrivateSalts>,
    ) -> Result<Self, Error> {
        if messages.len() != LANES {
            return Err(Error::WrongLength);
        }
        let salts_ok = match &private_salts {
            Some(salts) => salts.len() == FIBRE_COUNT,
            None => true,
        };
        if !salts_ok {
            return Err(Error::WrongLength);
        }
        let lanes = commitment_lanes(time)?;
        let mut words = Vec::new();
        words
            .try_reserve_exact(lanes.len())
            .map_err(|_| Error::Allocation)?;
        let mut saved = Vec::new();
        saved
            .try_reserve_exact(lanes.len())
            .map_err(|_| Error::Allocation)?;
        encode_lanes(domain, messages, variant, &lanes, &mut words, &mut saved)?;
        let mut leaves = filled(FIBRE_COUNT, [0; 32])?;
        let tag = match time {
            CommitmentTime::C1 => merkle::C1_TAG,
            CommitmentTime::C2 => merkle::C2_TAG,
        };
        match &private_salts {
            Some(salts) => salted_leaves(hash, tag, &lanes, &words, salts, &mut leaves),
            None => plain_leaves(hash, tag, &lanes, &words, &mut leaves),
        }
        Ok(Self {
            time,
            lanes,
            messages: saved,
            words,
            tree: crate::multiproof::BinaryTree::new(aspis_core::digest::LegacyHashFn(hash), leaves)
                .ok_or(Error::WrongLength)?,
            private_salts,
        })
    }
    pub fn root(&self) -> [u8; 32] {
        self.tree.root()
    }
    /// Binary multiproof for strictly increasing indices.
    pub(crate) fn multiproof(&self, indices: &[u32]) -> Option<Vec<u8>> {
        self.tree.multiproof(indices)
    }
    fn matches(&self, messages: &[Message<E>]) -> bool {
        self.lanes
            .iter()
            .enumerate()
            .all(|(j, &l)| self.messages[j] == messages[l])
    }
    pub(crate) fn fill_opening(&self, u: FibreIndex, out: &mut FibreOpening) {
        out.values = opening_values(self, 4 * u.get(), out.values, 0);
        // No per-query path: authentication is the batch multiproof.
        out.paths[opening_path(self.time)] = [[[0; 32]; 7]; 6];
    }
    pub(crate) fn opening_salt(&self, u: FibreIndex) -> Option<&[u8; 32]> {
        match &self.private_salts {
            Some(salts) => Some(salts.get(u.get())),
            None => None,
        }
    }
}


// ===== Extraction helpers (pv-rw-b-20261110). Behaviour-preserving rewrites of the
// pinned bodies into shapes the pinned Charon/Aeneas translate: one counted loop
// per function, no iterator adaptors, no closures, `&mut` slice parameters for
// loops that write and may fail. Same values, same order, same first error. =====
fn domain_points() -> Result<Vec<Point<M31>>, Error> {
    let mut xy = filled(
        FIBRE_COUNT,
        Point {
            x: M31::ZERO,
            y: M31::ZERO,
        },
    )?;
    fill_domain_points(&mut xy)?;
    Ok(xy)
}
fn fill_domain_points(xy: &mut [Point<M31>]) -> Result<(), Error> {
    let mut u = 0;
    while u < xy.len() {
        xy[u] = domain::fibre_point(FibreIndex::new(u)?);
        u += 1;
    }
    Ok(())
}
fn domain_first_level(xy: &[Point<M31>]) -> Result<Vec<M31>, Error> {
    let mut first = filled(FIBRE_COUNT, M31::ZERO)?;
    let mut u = 0;
    while u < FIBRE_COUNT {
        first[u] = xy[u].x.mul(xy[u].x).double().sub(M31::ONE);
        u += 1;
    }
    Ok(first)
}
fn domain_next_level(previous: &[M31]) -> Result<Vec<M31>, Error> {
    let mut next = filled(previous.len() / 2, M31::ZERO)?;
    let mut j = 0;
    while j < next.len() {
        next[j] = previous[2 * j].mul(previous[2 * j]).double().sub(M31::ONE);
        j += 1;
    }
    Ok(next)
}
fn domain_append_levels(mut levels: Vec<Vec<M31>>, depth: usize) -> Result<Vec<Vec<M31>>, Error> {
    if depth == 8 {
        return Ok(levels);
    }
    let next = domain_next_level(&levels[depth])?;
    levels.push(next);
    domain_append_levels(levels, depth + 1)
}
fn split_coefficients<T: CodeField>(coefficients: &[T], even: &mut [T], odd: &mut [T]) {
    let mut j = 0;
    while j < even.len() {
        even[j] = coefficients[2 * j];
        odd[j] = coefficients[2 * j + 1];
        j += 1;
    }
}
fn merge_evaluations<T: CodeField>(nodes: &[M31], a: &[T], b: &[T], out: &mut [T]) {
    let mut j = 0;
    while j < nodes.len() {
        out[j] = a[j / 2].add(T::from_m31(nodes[j]).mul(b[j / 2]));
        j += 1;
    }
}
fn channel_coefficients<T: CodeField>(message: &Message<T>, s: usize) -> [T; 256] {
    let mut coeff = [T::ZERO; 256];
    let mut d = 0;
    while d < 256 {
        coeff[d] = message[4 * d + s];
        d += 1;
    }
    coeff
}
fn encode_fibres<T: CodeField>(xy: &[Point<M31>], channels: &[Vec<T>], word: &mut [T]) {
    let mut u = 0;
    while u < xy.len() {
        let values = fold::phi_inverse(
            T::from_m31(xy[u].x),
            T::from_m31(xy[u].y),
            [channels[0][u], channels[1][u], channels[2][u], channels[3][u]],
        );
        word[4 * u..4 * u + 4].copy_from_slice(&values);
        u += 1;
    }
}
fn commitment_lanes(time: CommitmentTime) -> Result<Vec<usize>, Error> {
    match time {
        CommitmentTime::C1 => {
            let mut lanes = filled(27, 0)?;
            lanes.copy_from_slice(&[
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 28,
            ]);
            Ok(lanes)
        }
        CommitmentTime::C2 => {
            let mut lanes = filled(2, 0)?;
            lanes.copy_from_slice(&[26, 27]);
            Ok(lanes)
        }
    }
}
/// True iff some row of `message` has a nonzero limb at index `first` or above.
/// No early exit: every row is scanned (the result equals the original `any`).
fn lane_has_high_limbs(message: &Message<E>, first: usize) -> bool {
    let mut bad = false;
    let mut row = 0;
    while row < message.len() {
        bad = bad | limbs_nonzero_from(&message[row].to_limbs(), first);
        row += 1;
    }
    bad
}
fn limbs_nonzero_from(limbs: &[u32; 8], first: usize) -> bool {
    let mut bad = false;
    let mut i = first;
    while i < 8 {
        bad = bad | (limbs[i] != 0);
        i += 1;
    }
    bad
}
fn base_coefficients(coefficients: &Message<E>) -> Message<M31> {
    let mut out = [M31::ZERO; 1024];
    let mut i = 0;
    while i < 1024 {
        out[i] = M31(coefficients[i].to_limbs()[0]);
        i += 1;
    }
    out
}
fn secure_coefficients(coefficients: &Message<E>) -> Message<QM31> {
    let mut out = [QM31::ZERO; 1024];
    let mut i = 0;
    while i < 1024 {
        out[i] = coefficients[i].c0();
        i += 1;
    }
    out
}
fn encode_lane(
    domain: &EncodingDomain,
    message: &Message<E>,
    variant: crate::transport::Variant,
    lane: usize,
) -> Result<Word, Error> {
    // API inputs and retained matching data are semantic rows; only
    // Enc consumes coefficients. W_l = Enc(t_l ∘ π⁻¹), D13.
    let coefficients = variant.coefficients(message);
    if lane < 26 {
        Ok(Word::Base(domain.encode(&base_coefficients(&coefficients))?))
    } else {
        Ok(Word::Secure(domain.encode(&secure_coefficients(&coefficients))?))
    }
}
/// Per lane, in lane order: range check, then encode, then retain the rows
/// (the original interleaving, so the first error is unchanged).
fn encode_lanes(
    domain: &EncodingDomain,
    messages: &[Message<E>],
    variant: crate::transport::Variant,
    lanes: &[usize],
    words: &mut Vec<Word>,
    saved: &mut Vec<Message<E>>,
) -> Result<(), Error> {
    let mut j = 0;
    while j < lanes.len() {
        let l = lanes[j];
        if lane_has_high_limbs(&messages[l], if l < 26 { 1 } else { 4 }) {
            return Err(Error::WrongField);
        }
        let word = encode_lane(domain, &messages[l], variant, l)?;
        words.push(word);
        saved.push(messages[l]);
        j += 1;
    }
    Ok(())
}
fn leaf_row_bytes(bytes: &mut [u8; 480], mut at: usize, words: &[Word], lanes: &[usize], index: usize) -> usize {
    let mut j = 0;
    while j < lanes.len() {
        let b = words[j].value(index).to_le_bytes();
        let width = if lanes[j] < 26 { 4 } else { 16 };
        bytes[at..at + width].copy_from_slice(&b[..width]);
        at += width;
        j += 1;
    }
    at
}
fn leaf_bytes(words: &[Word], lanes: &[usize], u: usize) -> ([u8; 480], usize) {
    let mut bytes = [0u8; 480];
    let mut at = 0;
    let mut s = 0;
    while s < 4 {
        at = leaf_row_bytes(&mut bytes, at, words, lanes, 4 * u + s);
        s += 1;
    }
    (bytes, at)
}
fn salted_leaves(hash: HashFn, tag: u8, lanes: &[usize], words: &[Word], salts: &PrivateSalts, leaves: &mut [[u8; 32]]) {
    let mut u = 0;
    while u < leaves.len() {
        let (bytes, at) = leaf_bytes(words, lanes, u);
        leaves[u] = aspis_core::state_only_private_merkle::private_leaf_hash(hash, tag, &bytes[..at], salts.get(u));
        u += 1;
    }
}
fn plain_leaves(hash: HashFn, tag: u8, lanes: &[usize], words: &[Word], leaves: &mut [[u8; 32]]) {
    let mut u = 0;
    while u < leaves.len() {
        let (bytes, at) = leaf_bytes(words, lanes, u);
        leaves[u] = merkle::leaf(hash, tag, &bytes[..at]);
        u += 1;
    }
}
fn opening_path(time: CommitmentTime) -> usize {
    match time {
        CommitmentTime::C1 => 0,
        CommitmentTime::C2 => 1,
    }
}
/// The opened values of fibre `at / 4`, lane by lane in lane order (the pinned
/// nested loop). Structural recursion over the lane index with the value array
/// passed by value: every loop form of this write was rejected by Aeneas.
fn opening_values(c: &Commitment, at: usize, mut values: [[E; 29]; 4], j: usize) -> [[E; 29]; 4] {
    if j == c.lanes.len() {
        return values;
    }
    let lane = c.lanes[j];
    values[0][lane] = c.words[j].value(at);
    values[1][lane] = c.words[j].value(at + 1);
    values[2][lane] = c.words[j].value(at + 2);
    values[3][lane] = c.words[j].value(at + 3);
    opening_values(c, at, values, j + 1)
}

/// pv-rw-b-20261110: the pinned (4bb3b3f) bodies, kept verbatim under cfg(test)
/// so the rewritten bodies can be compared with them on random inputs.
#[cfg(test)]
mod lane_b_equivalence {
    use super::*;
    use aspis_core::field::CM31;

    fn original_new() -> Result<EncodingDomain, Error> {
        let mut xy = filled(
            FIBRE_COUNT,
            Point {
                x: M31::ZERO,
                y: M31::ZERO,
            },
        )?;
        for (u, z) in xy.iter_mut().enumerate() {
            *z = domain::fibre_point(FibreIndex::new(u)?);
        }
        let mut levels = Vec::new();
        levels.try_reserve_exact(9).map_err(|_| Error::Allocation)?;
        let mut first = filled(FIBRE_COUNT, M31::ZERO)?;
        for (n, z) in first.iter_mut().zip(&xy) {
            *n = z.x.mul(z.x).double().sub(M31::ONE);
        }
        levels.push(first);
        for depth in 0..8 {
            let mut next = filled(levels[depth].len() / 2, M31::ZERO)?;
            for (j, n) in next.iter_mut().enumerate() {
                *n = levels[depth][2*j].mul(levels[depth][2*j]).double().sub(M31::ONE);
            }
            levels.push(next);
        }
        Ok(EncodingDomain { xy, levels })
    }
    fn original_evaluate<T: CodeField>(d: &EncodingDomain, coefficients: &[T], depth: usize) -> Result<Vec<T>, Error> {
        let nodes = &d.levels[depth];
        if coefficients.len() == 1 {
            return filled(nodes.len(), coefficients[0]);
        }
        let mut even = filled(coefficients.len() / 2, T::ZERO)?;
        let mut odd = filled(even.len(), T::ZERO)?;
        for j in 0..even.len() {
            even[j] = coefficients[2 * j];
            odd[j] = coefficients[2 * j + 1];
        }
        let a = original_evaluate(d, &even, depth + 1)?;
        let b = original_evaluate(d, &odd, depth + 1)?;
        let mut out = filled(nodes.len(), T::ZERO)?;
        for j in 0..nodes.len() {
            out[j] = a[j / 2].add(T::from_m31(nodes[j]).mul(b[j / 2]));
        }
        Ok(out)
    }
    fn original_encode<T: CodeField>(d: &EncodingDomain, message: &Message<T>) -> Result<Vec<T>, Error> {
        let mut channels = Vec::new();
        channels
            .try_reserve_exact(4)
            .map_err(|_| Error::Allocation)?;
        for s in 0..4 {
            let coeff = core::array::from_fn::<_, 256, _>(|d| message[4 * d + s]);
            channels.push(original_evaluate(d, &coeff, 0)?);
        }
        let mut word = filled(WORD_LEN, T::ZERO)?;
        for (u, z) in d.xy.iter().enumerate() {
            let values = fold::phi_inverse(
                T::from_m31(z.x),
                T::from_m31(z.y),
                core::array::from_fn(|s| channels[s][u]),
            );
            word[4 * u..4 * u + 4].copy_from_slice(&values);
        }
        Ok(word)
    }
    fn original_build(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        private_salts: Option<PrivateSalts>,
    ) -> Result<Commitment, Error> {
        if messages.len() != LANES {
            return Err(Error::WrongLength);
        }
        if private_salts.as_ref().is_some_and(|salts| salts.len() != FIBRE_COUNT) {
            return Err(Error::WrongLength);
        }
        let indices: &[usize] = match time {
            CommitmentTime::C1 => &[
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 28,
            ],
            CommitmentTime::C2 => &[26, 27],
        };
        let mut lanes = filled(indices.len(), 0)?;
        lanes.copy_from_slice(indices);
        let mut words = Vec::new();
        words
            .try_reserve_exact(lanes.len())
            .map_err(|_| Error::Allocation)?;
        let mut saved = Vec::new();
        saved
            .try_reserve_exact(lanes.len())
            .map_err(|_| Error::Allocation)?;
        for &l in &lanes {
            if messages[l].iter().any(|x| {
                x.to_limbs()[if l < 26 { 1 } else { 4 }..]
                    .iter()
                    .any(|&d| d != 0)
            }) {
                return Err(Error::WrongField);
            }
            let coefficients = variant.coefficients(&messages[l]);
            words.push(if l < 26 {
                Word::Base(original_encode(domain, &coefficients.map(|x| M31(x.to_limbs()[0])))?)
            } else {
                Word::Secure(original_encode(domain, &coefficients.map(|x| x.c0()))?)
            });
            saved.push(messages[l]);
        }
        let mut leaves = filled(FIBRE_COUNT, [0; 32])?;
        for (u, digest) in leaves.iter_mut().enumerate() {
            let mut bytes = [0u8; 480];
            let mut at = 0;
            for s in 0..4 {
                for (j, &l) in lanes.iter().enumerate() {
                    let b = words[j].value(4 * u + s).to_le_bytes();
                    let width = if l < 26 { 4 } else { 16 };
                    bytes[at..at + width].copy_from_slice(&b[..width]);
                    at += width;
                }
            }
            let tag = if time == CommitmentTime::C1 { merkle::C1_TAG } else { merkle::C2_TAG };
            *digest = if let Some(salts) = private_salts.as_ref() {
                aspis_core::state_only_private_merkle::private_leaf_hash(hash, tag, &bytes[..at], salts.get(u))
            } else {
                merkle::leaf(hash, tag, &bytes[..at])
            };
        }
        Ok(Commitment {
            time,
            lanes,
            messages: saved,
            words,
            tree: crate::multiproof::BinaryTree::new(aspis_core::digest::LegacyHashFn(hash), leaves)
                .ok_or(Error::WrongLength)?,
            private_salts,
        })
    }
    fn original_fill_opening(c: &Commitment, u: FibreIndex, out: &mut FibreOpening) {
        for (j, &l) in c.lanes.iter().enumerate() {
            for s in 0..4 {
                out.values[s][l] = c.words[j].value(4 * u.get() + s);
            }
        }
        out.paths[if c.time == CommitmentTime::C1 {
            0
        } else {
            1
        }] = [[[0; 32]; 7]; 6];
    }

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0
        }
        fn m31(&mut self) -> M31 { M31(((self.next() >> 33) % 0x7fff_ffff) as u32) }
        fn qm31(&mut self) -> QM31 {
            QM31 { c0: CM31::new(self.m31(), self.m31()), c1: CM31::new(self.m31(), self.m31()) }
        }
        fn e(&mut self) -> E { E::new(self.qm31(), self.qm31()) }
    }
    fn test_hash(parts: &[&[u8]]) -> [u8; 32] {
        aspis_prover::HOST_HASH(parts)
    }
    fn words_equal(a: &Commitment, b: &Commitment) -> bool {
        a.words.len() == b.words.len()
            && (0..a.words.len()).all(|j| match (&a.words[j], &b.words[j]) {
                (Word::Base(x), Word::Base(y)) => x == y,
                (Word::Secure(x), Word::Secure(y)) => x == y,
                _ => false,
            })
    }
    /// Messages whose lanes are in range: base lanes (< 26) carry one M31 limb,
    /// secure lanes (26..29) carry a QM31 (limbs 0..4).
    fn in_range_messages(rng: &mut Rng) -> Vec<Message<E>> {
        let mut out = Vec::new();
        for l in 0..LANES {
            let mut m = [E::ZERO; 1024];
            for x in m.iter_mut() {
                *x = if l < 26 { E::from_m31(rng.m31()) } else { E::from_qm31(rng.qm31()) };
            }
            out.push(m);
        }
        out
    }

    #[test]
    fn encoding_domain_matches_the_pinned_body() {
        let new = EncodingDomain::new().unwrap();
        let old = original_new().unwrap();
        assert!(new.xy == old.xy);
        assert_eq!(new.levels, old.levels);
        let mut rng = Rng(0x5eed_0101);
        for (len, depth) in [(1usize, 8usize), (2, 7), (4, 6), (64, 2), (256, 0)] {
            let qc: Vec<QM31> = (0..len).map(|_| rng.qm31()).collect();
            assert_eq!(new.evaluate(&qc, depth).unwrap(), original_evaluate(&old, &qc, depth).unwrap());
            let mc: Vec<M31> = (0..len).map(|_| rng.m31()).collect();
            assert_eq!(new.evaluate(&mc, depth).unwrap(), original_evaluate(&old, &mc, depth).unwrap());
        }
        let ec: Vec<E> = (0..256).map(|_| rng.e()).collect();
        assert_eq!(new.evaluate(&ec, 0).unwrap(), original_evaluate(&old, &ec, 0).unwrap());
        let mm: Message<M31> = core::array::from_fn(|_| rng.m31());
        assert_eq!(new.encode(&mm).unwrap(), original_encode(&old, &mm).unwrap());
        let mq: Message<QM31> = core::array::from_fn(|_| rng.qm31());
        assert_eq!(new.encode(&mq).unwrap(), original_encode(&old, &mq).unwrap());
    }

    #[test]
    fn commitment_matches_the_pinned_body() {
        let domain = EncodingDomain::new().unwrap();
        let mut rng = Rng(0x5eed_0202);
        let messages = in_range_messages(&mut rng);
        let salts = |rng: &mut Rng| {
            let v: Vec<[u8; 32]> = (0..FIBRE_COUNT).map(|_| core::array::from_fn(|_| rng.next() as u8)).collect();
            v
        };
        for time in [CommitmentTime::C1, CommitmentTime::C2] {
            for variant in [crate::transport::Variant::S1, crate::transport::Variant::S2, crate::transport::Variant::D] {
                let s = salts(&mut rng);
                let new = Commitment::build(test_hash, &domain, time, &messages, variant, Some(PrivateSalts::new(s.clone()))).unwrap();
                let old = original_build(test_hash, &domain, time, &messages, variant, Some(PrivateSalts::new(s))).unwrap();
                assert_eq!(new.root(), old.root());
                assert_eq!(new.lanes, old.lanes);
                assert!(new.messages == old.messages);
                assert!(words_equal(&new, &old));
                for u in [0usize, 1, 4097, FIBRE_COUNT - 1] {
                    let fu = FibreIndex::new(u).unwrap();
                    let values: [[E; 29]; 4] = core::array::from_fn(|_| core::array::from_fn(|_| rng.e()));
                    let mut a = FibreOpening { values, paths: [[[[9; 32]; 7]; 6]; 2] };
                    let mut b = FibreOpening { values, paths: [[[[9; 32]; 7]; 6]; 2] };
                    new.fill_opening(fu, &mut a);
                    original_fill_opening(&old, fu, &mut b);
                    assert!(a.values == b.values && a.paths == b.paths);
                    assert_eq!(new.opening_salt(fu), old.opening_salt(fu));
                }
                // unsalted path
                let new = Commitment::build(test_hash, &domain, time, &messages, variant, None).unwrap();
                let old = original_build(test_hash, &domain, time, &messages, variant, None).unwrap();
                assert_eq!(new.root(), old.root());
                assert_eq!(new.opening_salt(FibreIndex::new(3).unwrap()), None);
            }
        }
    }

    #[test]
    fn commitment_errors_match_the_pinned_body() {
        let domain = EncodingDomain::new().unwrap();
        let mut rng = Rng(0x5eed_0303);
        let messages = in_range_messages(&mut rng);
        let v = crate::transport::Variant::S2;
        let t = CommitmentTime::C1;
        let short = &messages[..LANES - 1];
        assert_eq!(Commitment::build(test_hash, &domain, t, short, v, None).err(),
                   original_build(test_hash, &domain, t, short, v, None).err());
        let bad_salts = || Some(PrivateSalts::new(alloc::vec![[1u8; 32]; 5]));
        assert_eq!(Commitment::build(test_hash, &domain, t, &messages, v, bad_salts()).err(),
                   original_build(test_hash, &domain, t, &messages, v, bad_salts()).err());
        // out-of-range limb in a base lane, in a secure lane, and in an uncommitted lane
        for (lane, row, limb) in [(3usize, 17usize, 1usize), (28, 1023, 7), (26, 0, 4), (27, 5, 3)] {
            let mut m = messages.clone();
            let mut limbs = m[lane][row].to_limbs();
            limbs[limb] = 1;
            m[lane][row] = E::from_limbs(limbs).unwrap();
            for time in [CommitmentTime::C1, CommitmentTime::C2] {
                assert_eq!(Commitment::build(test_hash, &domain, time, &m, v, None).err(),
                           original_build(test_hash, &domain, time, &m, v, None).err(),
                           "lane {lane} row {row} limb {limb}");
            }
        }
    }
}
