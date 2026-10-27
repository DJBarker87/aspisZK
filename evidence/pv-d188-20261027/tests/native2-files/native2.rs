mod field;use field::{QM31,CM31,M31,WideExact as E};
fn state_only_statement_points(z: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let mut successor = *z;
    let mut carry = QM31::ONE;
    for coordinate in (0..z.len()).rev() {
        let bit = z[coordinate];
        let bit_and_carry = bit.mul(carry);
        successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
    }
    let mut absorption = *z;
    absorption[7] = QM31::ONE.sub(absorption[7]);
    absorption[6] = QM31::ONE.sub(absorption[6]);
    [*z, successor, absorption]
}
const STATE_ONLY_HIDING_CONTEXT_BYTES:usize=81;const STATE_ONLY_HIDING_CONTEXT_VERSION:u8=1;
pub struct StateOnlyHidingContext {
    pub statement_digest: [u8; 32],
    /// Public, proof-instance-unique nonce. This is not mask entropy.
    pub mask_nonce: [u8; 32],
    pub mask_layout_fingerprint: u64,
    pub layout_factor_fingerprint: u64,
}
impl StateOnlyHidingContext{pub fn encode(self) -> [u8; STATE_ONLY_HIDING_CONTEXT_BYTES] {
        let mut encoded = [0u8; STATE_ONLY_HIDING_CONTEXT_BYTES];
        encoded[0] = STATE_ONLY_HIDING_CONTEXT_VERSION;
        encoded[1..33].copy_from_slice(&self.statement_digest);
        encoded[33..65].copy_from_slice(&self.mask_nonce);
        encoded[65..73].copy_from_slice(&self.mask_layout_fingerprint.to_le_bytes());
        encoded[73..81].copy_from_slice(&self.layout_factor_fingerprint.to_le_bytes());
        encoded
    }}
pub fn powers<const N: usize>(x: E) -> [E; N] {
    let mut out = [E::ZERO; N];
    let mut p = E::ONE;
    let mut i = 0usize;
    while i < N {
        out[i] = p;
        i += 1;
        if i < N { p = p.mul(x); }
    }
    out
}
pub fn array_reference<T: Copy, const N: usize>(v: &[T], zero: T) -> Option<[T;N]> {
    if v.len() != N { return None; }
    let mut out = [zero;N];
    let mut i=0;
    while i<N { out[i]=v[i]; i+=1; }
    Some(out)
}
pub fn sha_pad_zero(mut buffer:[u8;64],pos:usize)->[u8;64] {
    buffer[pos]=0x80;
    let mut i=pos+1;
    while i<64 {buffer[i]=0;i+=1;}
    buffer
}
pub fn sha_pad_suffix8(mut buffer:[u8;64],suffix:[u8;8])->[u8;64] {
    let [a,b,c,d,e,f,g,h]=suffix;
    buffer[56]=a;buffer[57]=b;buffer[58]=c;buffer[59]=d;
    buffer[60]=e;buffer[61]=f;buffer[62]=g;buffer[63]=h;
    buffer
}
pub fn sha_pad_owned_split8(buffer:[u8;64],pos:usize,suffix:[u8;8])
    ->([u8;64],Option<[u8;64]>,[u8;64],usize) {
    let head=sha_pad_zero(buffer,pos);
    if 64-pos-1<8 {
        let second=sha_pad_suffix8([0u8;64],suffix);
        (head,Some(second),head,0)
    } else {
        let first=sha_pad_suffix8(head,suffix);
        (first,None,first,0)
    }
}
mod sha_fallback_consts {
pub const K32: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Constants necessary for SHA-256 family of digests.
pub const K32X4: [[u32; 4]; 16] = [
    [K32[3], K32[2], K32[1], K32[0]],
    [K32[7], K32[6], K32[5], K32[4]],
    [K32[11], K32[10], K32[9], K32[8]],
    [K32[15], K32[14], K32[13], K32[12]],
    [K32[19], K32[18], K32[17], K32[16]],
    [K32[23], K32[22], K32[21], K32[20]],
    [K32[27], K32[26], K32[25], K32[24]],
    [K32[31], K32[30], K32[29], K32[28]],
    [K32[35], K32[34], K32[33], K32[32]],
    [K32[39], K32[38], K32[37], K32[36]],
    [K32[43], K32[42], K32[41], K32[40]],
    [K32[47], K32[46], K32[45], K32[44]],
    [K32[51], K32[50], K32[49], K32[48]],
    [K32[55], K32[54], K32[53], K32[52]],
    [K32[59], K32[58], K32[57], K32[56]],
    [K32[63], K32[62], K32[61], K32[60]],
];

}
pub mod sha_fallback_reference {
#[inline(always)]
fn shl(v: [u32; 4], o: u32) -> [u32; 4] {
    [v[0] >> o, v[1] >> o, v[2] >> o, v[3] >> o]
}

#[inline(always)]
fn shr(v: [u32; 4], o: u32) -> [u32; 4] {
    [v[0] << o, v[1] << o, v[2] << o, v[3] << o]
}

#[inline(always)]
fn or(a: [u32; 4], b: [u32; 4]) -> [u32; 4] {
    [a[0] | b[0], a[1] | b[1], a[2] | b[2], a[3] | b[3]]
}

#[inline(always)]
fn xor(a: [u32; 4], b: [u32; 4]) -> [u32; 4] {
    [a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2], a[3] ^ b[3]]
}

#[inline(always)]
fn add(a: [u32; 4], b: [u32; 4]) -> [u32; 4] {
    [
        a[0].wrapping_add(b[0]),
        a[1].wrapping_add(b[1]),
        a[2].wrapping_add(b[2]),
        a[3].wrapping_add(b[3]),
    ]
}

fn sha256load(v2: [u32; 4], v3: [u32; 4]) -> [u32; 4] {
    [v3[3], v2[0], v2[1], v2[2]]
}

fn sha256swap(v0: [u32; 4]) -> [u32; 4] {
    [v0[2], v0[3], v0[0], v0[1]]
}

fn sha256msg1(v0: [u32; 4], v1: [u32; 4]) -> [u32; 4] {
    // sigma 0 on vectors
    #[inline]
    fn sigma0x4(x: [u32; 4]) -> [u32; 4] {
        let t1 = or(shl(x, 7), shr(x, 25));
        let t2 = or(shl(x, 18), shr(x, 14));
        let t3 = shl(x, 3);
        xor(xor(t1, t2), t3)
    }

    add(v0, sigma0x4(sha256load(v0, v1)))
}

fn sha256msg2(v4: [u32; 4], v3: [u32; 4]) -> [u32; 4] {
    macro_rules! sigma1 {
        ($a:expr) => {
            $a.rotate_right(17) ^ $a.rotate_right(19) ^ ($a >> 10u32)
        };
    }

    let [x3, x2, x1, x0] = v4;
    let [w15, w14, _, _] = v3;

    let w16 = x0.wrapping_add(sigma1!(w14));
    let w17 = x1.wrapping_add(sigma1!(w15));
    let w18 = x2.wrapping_add(sigma1!(w16));
    let w19 = x3.wrapping_add(sigma1!(w17));

    [w19, w18, w17, w16]
}

fn sha256_digest_round_x2(cdgh: [u32; 4], abef: [u32; 4], wk: [u32; 4]) -> [u32; 4] {
    macro_rules! big_sigma0 {
        ($a:expr) => {
            ($a.rotate_right(2) ^ $a.rotate_right(13) ^ $a.rotate_right(22))
        };
    }
    macro_rules! big_sigma1 {
        ($a:expr) => {
            ($a.rotate_right(6) ^ $a.rotate_right(11) ^ $a.rotate_right(25))
        };
    }
    macro_rules! bool3ary_202 {
        ($a:expr, $b:expr, $c:expr) => {
            $c ^ ($a & ($b ^ $c))
        };
    } // Choose, MD5F, SHA1C
    macro_rules! bool3ary_232 {
        ($a:expr, $b:expr, $c:expr) => {
            ($a & $b) ^ ($a & $c) ^ ($b & $c)
        };
    } // Majority, SHA1M

    let [_, _, wk1, wk0] = wk;
    let [a0, b0, e0, f0] = abef;
    let [c0, d0, g0, h0] = cdgh;

    // a round
    let x0 = big_sigma1!(e0)
        .wrapping_add(bool3ary_202!(e0, f0, g0))
        .wrapping_add(wk0)
        .wrapping_add(h0);
    let y0 = big_sigma0!(a0).wrapping_add(bool3ary_232!(a0, b0, c0));
    let (a1, b1, c1, d1, e1, f1, g1, h1) = (
        x0.wrapping_add(y0),
        a0,
        b0,
        c0,
        x0.wrapping_add(d0),
        e0,
        f0,
        g0,
    );

    // a round
    let x1 = big_sigma1!(e1)
        .wrapping_add(bool3ary_202!(e1, f1, g1))
        .wrapping_add(wk1)
        .wrapping_add(h1);
    let y1 = big_sigma0!(a1).wrapping_add(bool3ary_232!(a1, b1, c1));
    let (a2, b2, _, _, e2, f2, _, _) = (
        x1.wrapping_add(y1),
        a1,
        b1,
        c1,
        x1.wrapping_add(d1),
        e1,
        f1,
        g1,
    );

    [a2, b2, e2, f2]
}

fn schedule(v0: [u32; 4], v1: [u32; 4], v2: [u32; 4], v3: [u32; 4]) -> [u32; 4] {
    let t1 = sha256msg1(v0, v1);
    let t2 = sha256load(v2, v3);
    let t3 = add(t1, t2);
    sha256msg2(t3, v3)
}

macro_rules! rounds4 {
    ($abef:ident, $cdgh:ident, $rest:expr, $i:expr) => {{
        let t1 = add($rest, super::sha_fallback_consts::K32X4[$i]);
        $cdgh = sha256_digest_round_x2($cdgh, $abef, t1);
        let t2 = sha256swap(t1);
        $abef = sha256_digest_round_x2($abef, $cdgh, t2);
    }};
}

macro_rules! schedule_rounds4 {
    (
        $abef:ident, $cdgh:ident,
        $w0:expr, $w1:expr, $w2:expr, $w3:expr, $w4:expr,
        $i: expr
    ) => {{
        $w4 = schedule($w0, $w1, $w2, $w3);
        rounds4!($abef, $cdgh, $w4, $i);
    }};
}

/// Process a block with the SHA-256 algorithm.
fn sha256_digest_block_u32(state: &mut [u32; 8], block: &[u32; 16]) {
    let mut abef = [state[0], state[1], state[4], state[5]];
    let mut cdgh = [state[2], state[3], state[6], state[7]];

    // Rounds 0..64
    let mut w0 = [block[3], block[2], block[1], block[0]];
    let mut w1 = [block[7], block[6], block[5], block[4]];
    let mut w2 = [block[11], block[10], block[9], block[8]];
    let mut w3 = [block[15], block[14], block[13], block[12]];
    let mut w4;

    rounds4!(abef, cdgh, w0, 0);
    rounds4!(abef, cdgh, w1, 1);
    rounds4!(abef, cdgh, w2, 2);
    rounds4!(abef, cdgh, w3, 3);
    schedule_rounds4!(abef, cdgh, w0, w1, w2, w3, w4, 4);
    schedule_rounds4!(abef, cdgh, w1, w2, w3, w4, w0, 5);
    schedule_rounds4!(abef, cdgh, w2, w3, w4, w0, w1, 6);
    schedule_rounds4!(abef, cdgh, w3, w4, w0, w1, w2, 7);
    schedule_rounds4!(abef, cdgh, w4, w0, w1, w2, w3, 8);
    schedule_rounds4!(abef, cdgh, w0, w1, w2, w3, w4, 9);
    schedule_rounds4!(abef, cdgh, w1, w2, w3, w4, w0, 10);
    schedule_rounds4!(abef, cdgh, w2, w3, w4, w0, w1, 11);
    schedule_rounds4!(abef, cdgh, w3, w4, w0, w1, w2, 12);
    schedule_rounds4!(abef, cdgh, w4, w0, w1, w2, w3, 13);
    schedule_rounds4!(abef, cdgh, w0, w1, w2, w3, w4, 14);
    schedule_rounds4!(abef, cdgh, w1, w2, w3, w4, w0, 15);

    let [a, b, e, f] = abef;
    let [c, d, g, h] = cdgh;

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

pub fn extracted_round(a:[u32;4], b:[u32;4], w:[u32;4])->[u32;4] {sha256_digest_round_x2(a,b,w)}
pub fn extracted_schedule(a:[u32;4],b:[u32;4],c:[u32;4],d:[u32;4])->[u32;4] {schedule(a,b,c,d)}
pub fn extracted_round4(mut abef:[u32;4],mut cdgh:[u32;4],rest:[u32;4],k:[u32;4])->([u32;4],[u32;4]) {
    let t1=add(rest,k);
    cdgh=sha256_digest_round_x2(cdgh,abef,t1);
    let t2=sha256swap(t1);
    abef=sha256_digest_round_x2(abef,cdgh,t2);
    (abef,cdgh)
}
pub fn extracted_block(mut s:[u32;8], b:[u32;16])->[u32;8] {sha256_digest_block_u32(&mut s,&b);s}
}
fn main(){
 let q=QM31{c0:CM31{a:M31(2),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}};
 let z=state_only_statement_points(&[q;10]);println!("statement {:?}",z.map(|a|a.map(|q|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0])));
 let c=StateOnlyHidingContext{statement_digest:[2;32],mask_nonce:[3;32],mask_layout_fingerprint:4,layout_factor_fingerprint:5};println!("context {:?}",c.encode());
 let x=E::from_limbs([2,0,0,0,0,0,0,0]).unwrap();println!("powers {:?}",powers::<3>(x));
 println!("array {:?}",array_reference::<u32,4>(&[1,2,3,4],0));
 println!("pad {:?}",sha_pad_zero([255;64],3));
 println!("suffix {:?}",sha_pad_suffix8([255;64],[7;8]));
 println!("sha {:?}",sha_fallback_reference::extracted_block([1;8],[2;16]));
}
