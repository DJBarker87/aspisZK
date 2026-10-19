//! UNPROVED COST PROBE. Isolated packed commitments and native encoder.
use alloc::vec::Vec;
use aspis_core::{HashFn,field::{WideExact as E,M31,QM31},r0::{domain::{self,FibreIndex,Point},fold,merkle::{self,Tree},wire::FibreOpening,opening::LANES,heap::filled,CodeField,Error,Message,FIBRE_COUNT,WORD_LEN}};
/// Natural-product evaluation tree. Coordinates are always in F.
pub struct EncodingDomain {
    xy: Vec<Point<M31>>,
    levels: Vec<Vec<M31>>,
}
impl EncodingDomain {
    pub fn new() -> Result<Self, Error> {
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
        Ok(Self { xy, levels })
    }
    pub fn evaluate<T: CodeField>(&self, coefficients: &[T], depth: usize) -> Result<Vec<T>, Error> {
        let nodes = &self.levels[depth];
        if coefficients.len() == 1 {
            return filled(nodes.len(), coefficients[0]);
        }
        let mut even = filled(coefficients.len() / 2, T::ZERO)?;
        let mut odd = filled(even.len(), T::ZERO)?;
        for j in 0..even.len() {
            even[j] = coefficients[2 * j];
            odd[j] = coefficients[2 * j + 1];
        }
        let a = self.evaluate(&even, depth + 1)?;
        let b = self.evaluate(&odd, depth + 1)?;
        let mut out = filled(nodes.len(), T::ZERO)?;
        for j in 0..nodes.len() {
            out[j] = a[j / 2].add(T::from_m31(nodes[j]).mul(b[j / 2]));
        }
        Ok(out)
    }
    /// Exact §3 encoder at every stored index, O(N log 1024), using
    /// N_(2j)(x)=N_j(2x²−1), N_(2j+1)(x)=x*N_j(2x²−1).
    pub fn encode<T: CodeField>(&self, message: &Message<T>) -> Result<Vec<T>, Error> {
        let mut channels = Vec::new();
        channels
            .try_reserve_exact(4)
            .map_err(|_| Error::Allocation)?;
        for s in 0..4 {
            let coeff = core::array::from_fn::<_, 256, _>(|d| message[4 * d + s]);
            channels.push(self.evaluate(&coeff, 0)?);
        }
        let mut word = filled(WORD_LEN, T::ZERO)?;
        for (u, z) in self.xy.iter().enumerate() {
            let values = fold::phi_inverse(
                T::from_m31(z.x),
                T::from_m31(z.y),
                core::array::from_fn(|s| channels[s][u]),
            );
            word[4 * u..4 * u + 4].copy_from_slice(&values);
        }
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
    tree: CommitTree,
    private_salts: Option<PrivateSalts>,
}
/// Shipped eight-way tree, or the candidate binary tree (proof-size test).
enum CommitTree {
    Eight(Tree),
    #[cfg(feature = "compact-binary")]
    Binary(crate::multiproof::BinaryTree),
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
impl Drop for PrivateSalts {
    fn drop(&mut self) {
        for salt in &mut self.0 {
            // SAFETY: this buffer is uniquely owned while Drop runs.
            unsafe { core::ptr::write_volatile(salt, [0; 32]); }
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}
impl Commitment {
    pub fn new(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
    ) -> Result<Self, Error> {
        Self::build(hash, domain, time, messages, variant, None, false)
    }
    pub fn new_salted(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        salts: PrivateSalts,
    ) -> Result<Self, Error> {
        Self::build(hash, domain, time, messages, variant, Some(salts), false)
    }
    /// UNPROVED CANDIDATE: the same salted leaves under a binary tree.
    #[cfg(feature = "compact-binary")]
    pub fn new_salted_binary(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        salts: PrivateSalts,
    ) -> Result<Self, Error> {
        Self::build(hash, domain, time, messages, variant, Some(salts), true)
    }
    fn build(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        private_salts: Option<PrivateSalts>,
        binary: bool,
    ) -> Result<Self, Error> {
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
            // API inputs and retained matching data are semantic rows; only
            // Enc consumes coefficients. W_l = Enc(t_l ∘ π⁻¹), D13.
            let coefficients = variant.coefficients(&messages[l]);
            words.push(if l < 26 {
                Word::Base(domain.encode(&coefficients.map(|x| M31(x.to_limbs()[0])))?)
            } else {
                Word::Secure(domain.encode(&coefficients.map(|x| x.c0()))?)
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
        Ok(Self {
            time,
            lanes,
            messages: saved,
            words,
            tree: Self::tree(hash, leaves, binary)?,
            private_salts,
        })
    }
    fn tree(hash: HashFn, leaves: Vec<[u8; 32]>, binary: bool) -> Result<CommitTree, Error> {
        #[cfg(feature = "compact-binary")]
        if binary {
            return crate::multiproof::BinaryTree::new(aspis_core::digest::LegacyHashFn(hash), leaves)
                .map(CommitTree::Binary)
                .ok_or(Error::WrongLength);
        }
        let _ = binary;
        Ok(CommitTree::Eight(Tree::new(hash, leaves)?))
    }
    pub fn root(&self) -> [u8; 32] {
        match &self.tree {
            CommitTree::Eight(t) => t.root(),
            #[cfg(feature = "compact-binary")]
            CommitTree::Binary(t) => t.root(),
        }
    }
    /// UNPROVED CANDIDATE: binary multiproof for strictly increasing indices.
    #[cfg(feature = "compact-binary")]
    pub(crate) fn multiproof(&self, indices: &[u32]) -> Option<Vec<u8>> {
        match &self.tree {
            CommitTree::Binary(t) => t.multiproof(indices),
            CommitTree::Eight(_) => None,
        }
    }
    fn matches(&self, messages: &[Message<E>]) -> bool {
        self.lanes
            .iter()
            .enumerate()
            .all(|(j, &l)| self.messages[j] == messages[l])
    }
    pub(crate) fn fill_opening(&self, u: FibreIndex, out: &mut FibreOpening) {
        for (j, &l) in self.lanes.iter().enumerate() {
            for s in 0..4 {
                out.values[s][l] = self.words[j].value(4 * u.get() + s);
            }
        }
        let path = match &self.tree {
            CommitTree::Eight(t) => t.path(u),
            #[cfg(feature = "compact-binary")]
            CommitTree::Binary(_) => [[[0; 32]; 7]; 6],
        };
        out.paths[if self.time == CommitmentTime::C1 {
            0
        } else {
            1
        }] = path;
    }
    pub(crate) fn opening_salt(&self, u: FibreIndex) -> Option<&[u8; 32]> {
        self.private_salts.as_ref().map(|salts| salts.get(u.get()))
    }
}

