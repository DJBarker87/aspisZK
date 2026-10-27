pub fn finalize<D: digest::FixedOutput + Default + digest::Update + digest::HashMarker>(d: D) -> digest::Output<D> { digest::Digest::finalize(d) }
pub fn vec_empty(v: &Vec<u8>) -> bool { v.is_empty() }
pub fn vec_default() -> Vec<u8> { Vec::default() }
pub fn vec_pop(v: &mut Vec<u8>) -> Option<u8> { v.pop() }
pub fn vec_array(v: Vec<u8>) -> Result<[u8;32],Vec<u8>> { v.try_into() }
pub fn string_capacity(n: usize) -> String { String::with_capacity(n) }
pub fn string_push(s: &mut String, t: &str) { s.push_str(t) }
pub fn path_deref(p: &std::path::PathBuf) -> &std::path::Path { p }
pub fn path_asref(p: &std::path::PathBuf) -> &std::path::Path { p.as_ref() }
pub fn string_path(p: &String) -> &std::path::Path { p.as_ref() }
pub fn path_join(p: &std::path::Path, q: &std::path::Path) -> std::path::PathBuf { p.join(q) }

// Safe owned references; no library implementation is replaced or stubbed.
pub fn empty_reference<T>(v: &Vec<T>) -> bool { v.len() == 0 }
pub fn default_reference<T>() -> Vec<T> { Vec::new() }
pub fn pop_reference<T>(v: &mut Vec<T>) -> Option<T> {
    if v.len() == 0 { None } else { Some(v.remove(v.len() - 1)) }
}
pub fn sha_update_blocks(c: &mut sha2::Sha256VarCore, b: &[digest::core_api::Block<sha2::Sha256VarCore>]) {
    digest::core_api::UpdateCore::update_blocks(c,b)
}
pub fn sha_finalize_variable(c: &mut sha2::Sha256VarCore, b: &mut digest::core_api::Buffer<sha2::Sha256VarCore>, o: &mut digest::Output<sha2::Sha256VarCore>) {
    digest::core_api::VariableOutputCore::finalize_variable_core(c,b,o)
}
pub fn sha_finalize_into(c: sha2::Sha256, o: &mut digest::Output<sha2::Sha256>) {
    digest::FixedOutput::finalize_into(c,o)
}
pub fn sha_update(c: &mut sha2::Sha256, b: &[u8]) { digest::Update::update(c,b) }
pub fn sha_default() -> sha2::Sha256 { Default::default() }
pub fn sha_finalize_fixed(c: &mut digest::core_api::CtVariableCoreWrapper<sha2::Sha256VarCore, digest::consts::U32, sha2::OidSha256>, b: &mut digest::core_api::Buffer<sha2::Sha256VarCore>, o: &mut digest::Output<sha2::Sha256>) {
    digest::core_api::FixedOutputCore::finalize_fixed_core(c,b,o)
}
// Safe pure conversion kernel. The adapter retains the input on the None branch.
pub fn array_reference<T: Copy, const N: usize>(v: &[T], zero: T) -> Option<[T;N]> {
    if v.len() != N { return None; }
    let mut out = [zero;N];
    let mut i=0;
    while i<N { out[i]=v[i]; i+=1; }
    Some(out)
}
// Owned safe path-byte reference on Unix. No filesystem operation occurs.
pub fn path_bytes_reference(v: Vec<u8>) -> Vec<u8> { v }
// Functional owned pop reference; every item is moved exactly once.
pub fn pop_owned_reference<T>(v: Vec<T>) -> (Option<T>, Vec<T>) {
    let n = v.len(); let mut remaining = Vec::new(); let mut last = None;
    let mut i=0;
    for item in v {
        if i+1 == n { last = Some(item); } else { remaining.push(item); }
        i+=1;
    }
    (last,remaining)
}

// Unix Path::join as a safe owned byte-string operation.
pub fn join_bytes_reference(base: &[u8], path: &[u8]) -> Vec<u8> {
    let mut out=Vec::new();
    let absolute=path.len()>0 && path[0]==b'/';
    if !absolute {
        let mut i=0;
        while i<base.len() { out.push(base[i]); i+=1; }
        if base.len()>0 && base[base.len()-1]!=b'/' { out.push(b'/'); }
    }
    let mut j=0;
    while j<path.len() { out.push(path[j]); j+=1; }
    out
}
// Exact native owned carrier for a pure PathBuf view. No layout is exposed.
pub fn path_owned_reference(p: std::path::PathBuf) -> std::path::PathBuf { p }

pub fn array_qm31_reference(v: &[aspis_core::field::QM31]) -> Option<[aspis_core::field::QM31;1024]> {
    array_reference(v,aspis_core::field::QM31 {c0:aspis_core::field::CM31 {a:aspis_core::field::M31(0),b:aspis_core::field::M31(0)},c1:aspis_core::field::CM31 {a:aspis_core::field::M31(0),b:aspis_core::field::M31(0)}})
}
pub fn split_owned_reference(data: &[u8], size: usize) -> (Vec<Vec<u8>>,Vec<u8>) {
    let count=data.len()/size;
    let mut blocks=Vec::new();let mut i=0;
    while i<count {
        let mut block=Vec::new();let mut j=0;
        while j<size {block.push(data[i*size+j]);j+=1;}
        blocks.push(block);i+=1;
    }
    let mut tail=Vec::new();let mut k=count*size;
    while k<data.len() {tail.push(data[k]);k+=1;}
    (blocks,tail)
}
// Complete Result reference on the concrete Vec<QM31> instantiation.
// A shared input is sufficient for the pure source-value law; the error value
// is an owned copy with identical elements, and every output variant is kept.
pub fn array_full_reference(v: &Vec<aspis_core::field::QM31>) -> Result<[aspis_core::field::QM31;1024],Vec<aspis_core::field::QM31>> {
    match array_qm31_reference(v) { Some(a)=>Ok(a),None=>Err(v.clone()) }
}
// Owned input preserves the complete error branch without a cloning callback.
pub fn array_result_reference(v: Vec<aspis_core::field::QM31>) -> Result<[aspis_core::field::QM31;1024],Vec<aspis_core::field::QM31>> {
    if v.len()!=1024 {return Err(v);}
    let z=aspis_core::field::QM31 {c0:aspis_core::field::CM31 {a:aspis_core::field::M31(0),b:aspis_core::field::M31(0)},c1:aspis_core::field::CM31 {a:aspis_core::field::M31(0),b:aspis_core::field::M31(0)}};
    let mut out=[z;1024];let mut i=0;
    while i<1024 {out[i]=v[i];i+=1;}
    Ok(out)
}
// Actual sha2 constructor supporting the op217 default dependency chain.
pub fn sha_core_new(n: usize) -> Result<sha2::Sha256VarCore,digest::InvalidOutputSize> {
    <sha2::Sha256VarCore as digest::core_api::VariableOutputCore>::new(n)
}

// Owned String view preserves all valid UTF-8 without a loan escaping.
pub fn string_owned_reference(s: String) -> String { s }

// Pure String contents of with_capacity; allocation/capacity association remains explicit.
pub fn string_capacity_reference(_n: usize) -> String { String::new() }

// Borrowed update keeps the owned Vec with its caller on every path.
pub fn join_mut_reference(base: &mut Vec<u8>, path: &[u8]) {
    if path.len()>0 && path[0]==b'/' {base.clear();}
    else if base.len()>0 && base[base.len()-1]!=b'/' {base.push(b'/');}
    let mut i=0;
    while i<path.len() {base.push(path[i]);i+=1;}
}

// Byte-matched scalar helpers from the compiled x86 fallback.
// This is not a replacement for SHA-NI or the runtime dispatcher.
#[allow(dead_code)]
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
#[allow(dead_code)]
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

// Retained inputs make ownership loss explicit in adapter frontiers.
pub fn array_retained_reference<T:Copy,const N:usize>(v:Vec<T>, zero:T)->(Option<[T;N]>,Vec<T>) {
    let out=array_reference(&v,zero);(out,v)
}
pub fn pop_retained_reference<T>(mut v:Vec<T>)->(Option<T>,Vec<T>) {
    let n=v.len();
    let out=if n==0 {None} else {Some(v.remove(n-1))};
    (out,v)
}

// Separate default route to the empty String value.
pub fn string_default_reference(_n:usize)->String {String::default()}

// Owned byte representation reference for the pure empty String observation.
pub fn string_capacity_bytes_reference(_n:usize)->Vec<u8> {Vec::new()}
// Borrowed Vec update avoids owned-input unwind destruction.
pub fn push_bytes_reference(s:&mut Vec<u8>,t:&[u8]) {s.extend_from_slice(t)}

// Field-identical owned carrier for the byte-matched core constructor.
#[derive(Clone,Copy)]
pub struct ShaCoreOwned {pub state:[u32;8], pub block_len:u64}
#[derive(Clone,Copy)]
pub struct InvalidOutputSizeOwned;
pub fn sha_core_new_owned(output_size:usize)->Result<ShaCoreOwned,InvalidOutputSizeOwned> {
    let state = match output_size {
        28 => [0xc1059ed8,0x367cd507,0x3070dd17,0xf70e5939,0xffc00b31,0x68581511,0x64f98fa7,0xbefa4fa4],
        32 => [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19],
        _ => return Err(InvalidOutputSizeOwned),
    };
    let block_len = 0;
    Ok(ShaCoreOwned { state, block_len })
}

// Fixed SHA-256 padding reference; callback blocks and retained buffer are
// returned explicitly. It does not replace the shipped digest/loan semantics.
pub fn sha_pad_owned(mut buffer:[u8;64],pos:usize,suffix:[u8;8])
    ->([u8;64],Option<[u8;64]>,[u8;64],usize) {
    buffer[pos]=0x80;
    let mut i=pos+1;
    while i<64 {buffer[i]=0;i+=1;}
    if 64-pos-1<8 {
        let mut block=[0u8;64];let mut j=0;
        while j<8 {block[56+j]=suffix[j];j+=1;}
        (buffer,Some(block),buffer,0)
    } else {
        let mut j=0;
        while j<8 {buffer[56+j]=suffix[j];j+=1;}
        (buffer,None,buffer,0)
    }
}

pub fn sha_pad_zero(mut buffer:[u8;64],pos:usize)->[u8;64] {
    buffer[pos]=0x80;
    let mut i=pos+1;
    while i<64 {buffer[i]=0;i+=1;}
    buffer
}
pub fn sha_pad_suffix(mut buffer:[u8;64],suffix:[u8;8])->[u8;64] {
    let mut j=0;
    while j<8 {buffer[56+j]=suffix[j];j+=1;}
    buffer
}
pub fn sha_pad_owned_split(buffer:[u8;64],pos:usize,suffix:[u8;8])
    ->([u8;64],Option<[u8;64]>,[u8;64],usize) {
    let head=sha_pad_zero(buffer,pos);
    if 64-pos-1<8 {
        let second=sha_pad_suffix([0u8;64],suffix);
        (head,Some(second),head,0)
    } else {
        let first=sha_pad_suffix(head,suffix);
        (first,None,first,0)
    }
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

// Owned byte codecs for the pinned soft compression driver.
pub fn sha_load_be4(b:[u8;4])->u32 {
    ((b[0] as u32)<<24u32)|((b[1] as u32)<<16u32)|((b[2] as u32)<<8u32)|(b[3] as u32)
}
pub fn sha_store_be4(w:u32)->[u8;4] {
    [(w>>24u32) as u8,(w>>16u32) as u8,(w>>8u32) as u8,w as u8]
}
pub fn sha_load_lane0(b:[u8;64])->u32 { sha_load_be4([b[0],b[1],b[2],b[3]]) }
pub fn sha_load_lane1(b:[u8;64])->u32 { sha_load_be4([b[4],b[5],b[6],b[7]]) }
pub fn sha_load_lane2(b:[u8;64])->u32 { sha_load_be4([b[8],b[9],b[10],b[11]]) }
pub fn sha_load_lane3(b:[u8;64])->u32 { sha_load_be4([b[12],b[13],b[14],b[15]]) }
pub fn sha_load_lane4(b:[u8;64])->u32 { sha_load_be4([b[16],b[17],b[18],b[19]]) }
pub fn sha_load_lane5(b:[u8;64])->u32 { sha_load_be4([b[20],b[21],b[22],b[23]]) }
pub fn sha_load_lane6(b:[u8;64])->u32 { sha_load_be4([b[24],b[25],b[26],b[27]]) }
pub fn sha_load_lane7(b:[u8;64])->u32 { sha_load_be4([b[28],b[29],b[30],b[31]]) }
pub fn sha_load_lane8(b:[u8;64])->u32 { sha_load_be4([b[32],b[33],b[34],b[35]]) }
pub fn sha_load_lane9(b:[u8;64])->u32 { sha_load_be4([b[36],b[37],b[38],b[39]]) }
pub fn sha_load_lane10(b:[u8;64])->u32 { sha_load_be4([b[40],b[41],b[42],b[43]]) }
pub fn sha_load_lane11(b:[u8;64])->u32 { sha_load_be4([b[44],b[45],b[46],b[47]]) }
pub fn sha_load_lane12(b:[u8;64])->u32 { sha_load_be4([b[48],b[49],b[50],b[51]]) }
pub fn sha_load_lane13(b:[u8;64])->u32 { sha_load_be4([b[52],b[53],b[54],b[55]]) }
pub fn sha_load_lane14(b:[u8;64])->u32 { sha_load_be4([b[56],b[57],b[58],b[59]]) }
pub fn sha_load_lane15(b:[u8;64])->u32 { sha_load_be4([b[60],b[61],b[62],b[63]]) }
pub fn sha_load64(b:[u8;64])->[u32;16] { [sha_load_lane0(b),sha_load_lane1(b),sha_load_lane2(b),sha_load_lane3(b),sha_load_lane4(b),sha_load_lane5(b),sha_load_lane6(b),sha_load_lane7(b),sha_load_lane8(b),sha_load_lane9(b),sha_load_lane10(b),sha_load_lane11(b),sha_load_lane12(b),sha_load_lane13(b),sha_load_lane14(b),sha_load_lane15(b)] }
pub fn sha_byte_codec_root(b:[u8;64],w:u32)->([u32;16],[u8;4]) {(sha_load64(b),sha_store_be4(w))}

// Copy-only borrowed pop avoids the foreign remove and owned Drop frontiers.
pub fn pop_copy_resize_reference<T:Copy>(v:&mut Vec<T>)->Option<T> {
    let n=v.len();
    if n==0 { None } else {
        let last=v[n-1];
        v.resize(n-1,last);
        Some(last)
    }
}
// Unix join update using only extracted indexing, resize and append primitives.
pub fn join_resize_reference(base:&mut Vec<u8>,path:&[u8]) {
    if path.len()>0 && path[0]==b'/' {base.resize(0,0);}
    else if base.len()>0 && base[base.len()-1]!=b'/' {base.push(b'/');}
    base.extend_from_slice(path);
}

pub fn sha_length_suffix64(w:u64)->[u8;8] {
    [(w>>56u32) as u8,(w>>48u32) as u8,(w>>40u32) as u8,(w>>32u32) as u8,
     (w>>24u32) as u8,(w>>16u32) as u8,(w>>8u32) as u8,w as u8]
}
pub fn sha_compress_byte_owned(state:[u32;8],block:[u8;64])->[u32;8] {
    sha_fallback_reference::extracted_block(state,sha_load64(block))
}
pub fn sha_digest32(state:[u32;8])->[u8;32] {
    let a=sha_store_be4(state[0]);let b=sha_store_be4(state[1]);
    let c=sha_store_be4(state[2]);let d=sha_store_be4(state[3]);
    let e=sha_store_be4(state[4]);let f=sha_store_be4(state[5]);
    let g=sha_store_be4(state[6]);let h=sha_store_be4(state[7]);
    [a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],c[0],c[1],c[2],c[3],d[0],d[1],d[2],d[3],
     e[0],e[1],e[2],e[3],f[0],f[1],f[2],f[3],g[0],g[1],g[2],g[3],h[0],h[1],h[2],h[3]]
}
pub fn sha_finalize_soft_owned(state:[u32;8],blocks:u64,buffer:[u8;64],pos:usize)
 ->([u8;32],[u32;8],[u8;64],usize) {
    let bits=8u64.wrapping_mul((pos as u64).wrapping_add(64u64.wrapping_mul(blocks)));
    let (first,second,retained,newpos)=sha_pad_owned_split8(buffer,pos,sha_length_suffix64(bits));
    let mut next=sha_compress_byte_owned(state,first);
    if let Some(block)=second {next=sha_compress_byte_owned(next,block);}
    (sha_digest32(next),next,retained,newpos)
}

// Fixed-carrier buffer driver: owns its working state and retains every outcome.
pub fn sha_update_soft_owned(mut state:[u32;8],mut blocks:u64,mut buffer:[u8;64],mut pos:usize,data:&[u8])
 ->([u32;8],u64,[u8;64],usize) {
    let mut i=0;
    while i<data.len() {
        buffer[pos]=data[i];pos+=1;i+=1;
        if pos==64 {state=sha_compress_byte_owned(state,buffer);blocks=blocks.wrapping_add(1);pos=0;}
    }
    (state,blocks,buffer,pos)
}
pub fn sha_default_soft_owned()->([u32;8],u64,[u8;64],usize) {
    ([0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19],0,[0u8;64],0)
}
pub fn sha_digest_soft_owned(data:&[u8])->[u8;32] {
    let (state,blocks,buffer,pos)=sha_default_soft_owned();
    let (state,blocks,buffer,pos)=sha_update_soft_owned(state,blocks,buffer,pos,data);
    let (digest,_,_,_)=sha_finalize_soft_owned(state,blocks,buffer,pos);
    digest
}

// Full value variants, with a borrowed input and an owned error byte image.
pub fn array_slice_result_reference<T:Copy,const N:usize>(v:&[T],zero:T)
 ->Result<[T;N],Vec<T>> {
    match array_reference(v,zero) { Some(out)=>Ok(out), None=>Err(v.to_vec()) }
}
