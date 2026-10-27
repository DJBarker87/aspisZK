#[path="op205.rs"] mod digest;
#[path="op252.rs"] mod weights;
#[path="op226.rs"] mod public;
#[path="op249.rs"] mod sampler;
#[path="op134.rs"] mod forest;
#[path="op36.rs"] mod adapter;
mod sha_checks {use super::digest::*;
#[test] fn sha256_boundaries_and_chunking(){
let input=[];let expected=[227,176,196,66,152,252,28,20,154,251,244,200,153,111,185,36,39,174,65,228,100,155,147,76,164,149,153,27,120,82,184,85];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19];let expected=[171,137,127,189,237,250,80,43,45,131,155,106,86,16,8,135,220,205,197,7,85,92,40,46,89,88,158,6,48,10,98,226];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92];let expected=[199,86,189,16,77,20,6,236,44,56,12,38,141,190,248,143,210,8,40,25,193,90,33,200,100,75,205,142,141,228,188,150];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121];let expected=[12,67,163,9,112,238,149,37,166,96,61,86,86,128,60,50,91,222,209,72,250,101,187,211,99,223,84,203,58,195,222,229];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194];let expected=[244,220,220,9,200,70,209,179,98,23,1,81,107,48,0,85,193,231,135,94,33,107,160,25,221,68,35,245,164,32,242,208];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11];let expected=[87,158,8,176,170,10,124,182,142,237,50,90,101,142,204,32,85,126,20,79,253,92,93,154,221,170,132,5,95,197,21,102];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193];let expected=[186,59,182,44,67,105,254,116,231,185,67,146,208,240,78,210,132,167,181,215,41,91,250,72,250,189,178,92,1,216,90,183];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10];let expected=[203,104,98,38,140,167,192,46,123,106,245,88,240,227,210,54,206,158,199,255,65,204,116,107,40,72,192,76,88,45,169,78];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83];let expected=[182,138,245,93,249,206,142,230,8,112,228,93,16,227,107,46,131,99,201,137,111,110,98,71,141,203,111,89,58,77,113,51];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185];let expected=[23,86,36,240,249,91,10,71,161,179,181,47,91,20,159,136,128,45,56,34,177,132,50,93,12,32,161,167,193,50,166,135];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185,2];let expected=[5,152,163,216,181,168,39,16,221,165,79,5,196,170,17,253,209,192,170,95,175,178,22,132,15,204,186,227,35,240,117,32];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185,2,75,148,221,38,111,184,1];let expected=[168,54,91,110,110,209,218,245,108,65,186,232,154,176,137,192,59,103,18,64,174,16,48,112,72,10,127,39,27,219,173,87];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185,2,75,148,221,38,111,184,1,74];let expected=[211,153,240,101,201,242,30,47,213,30,42,234,219,119,104,234,183,230,228,94,81,80,243,18,39,201,113,25,52,164,209,211];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185,2,75,148,221,38,111,184,1,74,147];let expected=[214,114,64,142,5,113,99,110,162,16,146,48,78,179,27,168,252,31,191,252,93,94,166,83,29,98,176,114,113,69,153,219];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185,2,75,148,221,38,111,184,1,74,147,220,37,110,183,0,73,146,219,36,109,182,255,72,145,218,35,108,181,254,71,144,217,34,107,180,253,70,143,216,33,106,179,252,69,142,215,32,105,178,251,68,141,214,31,104,177,250,67,140,213,30,103,176,249,66,139,212,29,102,175,248,65,138,211,28,101,174,247,64,137,210,27,100,173,246,63,136,209,26,99,172,245,62,135,208,25,98,171,244,61,134,207,24,97,170,243,60,133,206,23,96,169,242,59,132,205,22,95,168,241,58,131,204,21,94,167,240,57,130,203,20,93,166,239,56,129];let expected=[109,89,241,179,168,134,232,203,129,62,119,209,240,202,14,166,62,216,170,143,82,81,28,74,67,142,251,106,74,81,209,255];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
let input=[19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185,2,75,148,221,38,111,184,1,74,147,220,37,110,183,0,73,146,219,36,109,182,255,72,145,218,35,108,181,254,71,144,217,34,107,180,253,70,143,216,33,106,179,252,69,142,215,32,105,178,251,68,141,214,31,104,177,250,67,140,213,30,103,176,249,66,139,212,29,102,175,248,65,138,211,28,101,174,247,64,137,210,27,100,173,246,63,136,209,26,99,172,245,62,135,208,25,98,171,244,61,134,207,24,97,170,243,60,133,206,23,96,169,242,59,132,205,22,95,168,241,58,131,204,21,94,167,240,57,130,203,20,93,166,239,56,129,202,19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185,2,75,148,221,38,111,184,1,74,147,220,37,110,183,0,73,146,219,36,109,182,255,72,145,218,35,108,181,254,71,144,217,34,107,180,253,70,143,216,33,106,179,252,69,142,215,32,105,178,251,68,141,214,31,104,177,250,67,140,213,30,103,176,249,66,139,212,29,102,175,248,65,138,211,28,101,174,247,64,137,210,27,100,173,246,63,136,209,26,99,172,245,62,135,208,25,98,171,244,61,134,207,24,97,170,243,60,133,206,23,96,169,242,59,132,205,22,95,168,241,58,131,204,21,94,167,240,57,130,203,20,93,166,239,56,129,202,19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185,2,75,148,221,38,111,184,1,74,147,220,37,110,183,0,73,146,219,36,109,182,255,72,145,218,35,108,181,254,71,144,217,34,107,180,253,70,143,216,33,106,179,252,69,142,215,32,105,178,251,68,141,214,31,104,177,250,67,140,213,30,103,176,249,66,139,212,29,102,175,248,65,138,211,28,101,174,247,64,137,210,27,100,173,246,63,136,209,26,99,172,245,62,135,208,25,98,171,244,61,134,207,24,97,170,243,60,133,206,23,96,169,242,59,132,205,22,95,168,241,58,131,204,21,94,167,240,57,130,203,20,93,166,239,56,129,202,19,92,165,238,55,128,201,18,91,164,237,54,127,200,17,90,163,236,53,126,199,16,89,162,235,52,125,198,15,88,161,234,51,124,197,14,87,160,233,50,123,196,13,86,159,232,49,122,195,12,85,158,231,48,121,194,11,84,157,230,47,120,193,10,83,156,229,46,119,192,9,82,155,228,45,118,191,8,81,154,227,44,117,190,7,80,153,226,43,116,189,6,79,152,225,42,115,188,5,78,151,224,41,114,187,4,77,150,223,40,113,186,3,76,149,222,39,112,185,2,75,148,221,38,111,184,1,74,147,220,37,110,183,0,73,146,219,36,109,182,255,72,145,218,35,108,181,254,71,144,217,34,107,180,253,70,143,216,33,106,179,252,69,142,215,32,105,178,251,68,141,214,31,104,177,250,67,140,213,30,103,176,249,66,139,212,29,102,175,248,65,138,211,28,101,174,247,64,137,210,27,100,173,246,63,136,209,26,99,172,245,62,135,208,25,98,171,244,61,134,207,24,97,170,243,60,133,206,23,96,169,242,59,132,205,22,95,168,241,58,131,204,21,94,167,240,57,130,203,20,93,166,239,56,129,202];let expected=[224,81,209,0,118,7,222,73,76,7,61,163,194,153,3,214,192,171,254,231,164,192,96,159,86,10,52,10,25,71,180,112];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);
}}
#[test] fn forest_inventory(){let masks=forest::active_row_masks().ok().unwrap();let mut hash=0xcbf29ce484222325u64;let mut count=0;for row in 0..1024 {if masks[row/16]&(1u16<<(row%16))!=0 {count+=1;for b in (row as u16).to_le_bytes(){hash=(hash^b as u64).wrapping_mul(0x100000001b3);}}}assert_eq!(count,214);assert_eq!(hash,0xdf394a5a8554d09c);}
#[test] fn owned_error_carrier(){let v=adapter::Buffer{data:[9u32,8,7,6],len:3};let e=adapter::array_try_from::<u32,2,4>(v,0).err().unwrap();assert_eq!(e.data,v.data);assert_eq!(e.len,3);let a=adapter::array_try_from::<u32,3,4>(v,0).ok().unwrap();assert_eq!(a,[9,8,7]);}
mod original_sampler {use aspis_core::field::{WideExact,CM31,M31,P,QM31};fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
    let mut quotient: [u32; 8] =
        core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
    let digits = core::array::from_fn(|_| {
        let mut remainder = 0u64;
        for limb in quotient.iter_mut().rev() {
            let dividend = (remainder << 32) | u64::from(*limb);
            *limb = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
        remainder as u32
    });

    // After eight divisions, the quotient is at most 256 and fits in u32.
    debug_assert!(quotient[1..].iter().all(|&limb| limb == 0));
    debug_assert!(quotient[0] <= 256);
    (digits, quotient[0])
}

fn decode8(digits: [u32; 8]) -> WideExact {
    WideExact::new(
        QM31 {
            c0: CM31::new(M31(digits[0]), M31(digits[1])),
            c1: CM31::new(M31(digits[2]), M31(digits[3])),
        },
        QM31 {
            c0: CM31::new(M31(digits[4]), M31(digits[5])),
            c1: CM31::new(M31(digits[6]), M31(digits[7])),
        },
    )
}

/// Add a small integer to a base-P digit vector. Returns the carry beyond
/// the final digit, which is at most one for the values used by the sampler.
fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
    for digit in digits {
        let sum = u64::from(*digit) + u64::from(addend);
        *digit = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
    }
    debug_assert!(addend <= 1);
    addend != 0
}

/// `decode8(rank(block) mod P^8)`, byte-for-byte equivalent to the frozen
/// R0 sampler. The repeated divisions directly produce the low eight digits.
pub fn ordinary_sample(block: &[u8; 32]) -> WideExact {
    let (digits, _) = low_base_p_digits(block);
    decode8(digits)
}

/// `decode8((rank(block) mod (P^8 - 1)) + 1)`, byte-for-byte equivalent to
/// the frozen R0 sampler. Since `P^8 ≡ 1 (mod P^8 - 1)`, the high quotient can
/// be added to the low digits before the final increment. A carry past digit
/// seven contributes one more modulo `P^8 - 1`.
pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
    let (mut digits, quotient) = low_base_p_digits(block);
    let wrapped = add_small_base_p(&mut digits, quotient + 1);
    if wrapped {
        let wrapped_again = add_small_base_p(&mut digits, 1);
        debug_assert!(!wrapped_again);
    }
    decode8(digits)
}

}
#[test] fn sampler_differential(){for seed in 0..1024u32 {let mut block=[0u8;32];let mut x=seed.wrapping_add(1);for b in &mut block {x=x.wrapping_mul(1664525).wrapping_add(1013904223);*b=(x>>24) as u8;}assert_eq!(sampler::gamma_sample(&block),original_sampler::gamma_sample(&block));assert_eq!(sampler::ordinary_sample(&block),original_sampler::ordinary_sample(&block));}}
mod original_weights {use super::weights::{Weights,Variant,Error};use aspis_core::field::QM31 as K;use aspis_core::circle::SecureCirclePoint;const TAU:[usize;5]=[3,4,2,0,1];fn double(x:K)->K{x.mul(x).add(x.mul(x)).sub(K::ONE)}pub fn new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])->Result<Box<Weights>,Error>{        let points=aspis_core::state_only_prefix::r0::statement_points(alpha);
        let extra=[alpha[8],alpha[9]];
        let mut factors=[[[K::ZERO;4];5];5];
        for k in 0..3 { for d in 0..5 {
            let a=points[k][9-2*TAU[d]]; let b=points[k][8-2*TAU[d]];
            factors[k][d]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
        }}
        for k in 0..2 {
            factors[3+k][0]=[K::ONE,z[k].y,z[k].x,z[k].x.mul(z[k].y)];
            let mut x=double(z[k].x);
            for d in 1..5 {
                let y=double(x); factors[3+k][d]=[K::ONE,x,y,x.mul(y)]; x=double(y);
            }
        }
        Ok(Box::new(Weights {variant,factors,points,extra}))}}
#[test] fn weights_differential(){use aspis_core::field::QM31 as K;use aspis_core::field::{M31,CM31};use aspis_core::circle::SecureCirclePoint;for seed in 0..64u32 {let mut alpha=[K::ZERO;10];for i in 0..10 {alpha[i]=K::from_cm31(CM31::from_m31(M31(seed*17+i as u32)));}let z=[SecureCirclePoint{x:alpha[0],y:alpha[1]},SecureCirclePoint{x:alpha[2],y:alpha[3]}];for v in [weights::Variant::S1,weights::Variant::S2,weights::Variant::D]{let a=weights::weights_new(v,&alpha,&z).ok().unwrap();let b=original_weights::new(v,&alpha,&z).ok().unwrap();assert_eq!(a.factors,b.factors);assert_eq!(a.points,b.points);assert_eq!(a.extra,b.extra);}}}
fn old_public(p:public::Public)->Result<Vec<u8>,()>{fn fields(out:&mut Vec<u8>,v:&[u32])->Result<(),()>{for x in v {if *x>=2147483647{return Err(());}out.extend_from_slice(&x.to_le_bytes());}Ok(())}let mut out=vec![if p.withdrawal{1}else{0}];fields(&mut out,&p.anchor)?;fields(&mut out,&p.nullifier)?;fields(&mut out,&[p.asset_id])?;out.push(if p.withdrawal{0}else{1});if !p.withdrawal{fields(&mut out,&p.recipient)?;}fields(&mut out,&p.change)?;out.push(if p.withdrawal{1}else{0});if p.withdrawal{fields(&mut out,&[p.withdrawal_amount])?;}out.extend_from_slice(&p.next_pair_index.to_le_bytes());for x in p.frontier{fields(&mut out,&x)?;}fields(&mut out,&p.next_root)?;for x in p.next_frontier{fields(&mut out,&x)?;}Ok(out)}
#[test] fn public_bytes_differential(){for seed in 0..128u32 {for withdrawal in [false,true] {let mut p=public::Public{withdrawal,anchor:[seed;8],nullifier:[seed+1;8],asset_id:seed+2,recipient:[seed+3;8],change:[seed+4;8],withdrawal_amount:seed+5,next_pair_index:seed as u64,frontier:[[seed+6;8];20],next_root:[seed+7;8],next_frontier:[[seed+8;8];20]};for invalid in 0..8 {let old=old_public(p);let new=public::public_bytes(p);match (old,new){(Ok(a),Ok((b,n)))=>{assert_eq!(a,&b[..n]);assert_eq!(n,if withdrawal{1427}else{1455});},(Err(_),Err(_))=>(),_=>panic!("Result mismatch")};match invalid{0=>p.anchor[0]=2147483647,1=>{p.anchor[0]=seed;p.asset_id=2147483647},2=>{p.asset_id=seed;p.recipient[0]=2147483647},3=>{p.recipient[0]=seed;p.change[0]=2147483647},4=>{p.change[0]=seed;p.withdrawal_amount=2147483647},5=>{p.withdrawal_amount=seed;p.frontier[19][7]=2147483647},_=>{p.frontier[19][7]=seed;p.next_frontier[19][7]=2147483647}}}}}}

#[test] fn carrier_layouts(){assert_eq!(core::mem::size_of::<weights::Weights>(),2116);assert_eq!(core::mem::size_of::<digest::Sha256>(),112);assert_eq!(core::mem::size_of::<public::Public>(),1464);assert_eq!(core::mem::size_of::<adapter::Buffer<u32,4>>(),24);}
