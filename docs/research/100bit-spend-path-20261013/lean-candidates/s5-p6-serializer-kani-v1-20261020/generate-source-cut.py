from pathlib import Path
import json,hashlib,subprocess,sys
root=Path('/Users/dominic/ZK');w=Path(__file__).resolve().parent
model=w/'model/P6ChunksExactMutModelV3.lean'
if not model.is_file(): model=Path('/tmp/s5-p6-v3-overlay/sources/P6ChunksExactMutModelV3.lean')
src=root/'crates/aspis-core/src/field/wide_exact.rs';text=src.read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
def extract(signature):
 start=text.index(signature);brace=text.index('{',start);depth=1;i=brace+1
 while depth:
  depth+=(text[i]=='{')-(text[i]=='}');i+=1
 return text[start:i]
methods=[extract('pub const fn to_limbs('),extract('pub fn to_le_bytes(')]
struct=extract('pub struct WideExact')
# Minimal carrier declarations preserve the actual eight u32 leaves. The
# selected Rust method/struct bodies below are byte-for-byte source cuts.
out='''// Generated exact method/struct cuts; see source-binding.json.
#[derive(Clone, Copy)]
pub struct M31(pub u32);
#[derive(Clone, Copy)]
pub struct CM31 { pub a: M31, pub b: M31 }
#[derive(Clone, Copy)]
pub struct QM31 { pub c0: CM31, pub c1: CM31 }
#[derive(Clone, Copy)]
'''+struct+'''
impl WideExact {
    pub const LIMB_COUNT: usize = 8;
    pub const BYTE_LEN: usize = 32;
'''+''.join('    '+m+'\n' for m in methods)+'''}

// Harness-only constructor; no canonicality assumption, all 256 input bits.
fn raw_wide(x: [u32; 8]) -> WideExact {
    WideExact {
      c0: QM31 { c0: CM31 { a:M31(x[0]),b:M31(x[1]) },
                  c1: CM31 { a:M31(x[2]),b:M31(x[3]) } },
      c1: QM31 { c0: CM31 { a:M31(x[4]),b:M31(x[5]) },
                  c1: CM31 { a:M31(x[6]),b:M31(x[7]) } },
    }
}

/// First-order executable projection of the P6 eight captured-start writes.
/// Forward traversal captures each chunk start and four-byte replacement;
/// unwind applies them from last to first, as the extracted back continuation.
fn captured_writeback(limbs: [u32;8], initial: [u8;32]) -> [u8;32] {
    let mut starts = [0usize;8];
    let mut chunks = [[0u8;4];8];
    let mut cursor = 0usize;
    let mut i = 0usize;
    while i < 8 {
        assert!(cursor + 4 <= 32);
        starts[i] = cursor;
        chunks[i] = limbs[i].to_le_bytes();
        cursor += 4;
        i += 1;
    }
    let mut source = initial;
    while i > 0 {
        i -= 1;
        let start = starts[i];
        let mut b = 0;
        while b < 4 {
            source[start + b] = chunks[i][b];
            b += 1;
        }
    }
    source
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(34)]
fn original_serializer_matches_captured_writeback() {
    let limbs: [u32;8] = kani::any();
    let initial: [u8;32] = kani::any();
    assert_eq!(raw_wide(limbs).to_le_bytes(), captured_writeback(limbs, initial));
}

#[cfg(test)]
mod tests {
 use super::*;
 #[test]
 fn captured_starts_and_terminal_writeback_controls() {
    for limbs in [[0;8], [u32::MAX;8], [1,2,3,4,5,6,7,8],
        [0,1,u32::MAX,2147483646,2147483647,2147483648,0x80000000,0x01020304]] {
        let actual=raw_wide(limbs).to_le_bytes();
        assert_eq!(actual,captured_writeback(limbs,[0xa5;32]));
    }
    let limbs=[1,2,3,4,5,6,7,8];
    let actual=raw_wide(limbs).to_le_bytes();
    // Rejected historical bug 1: all callbacks read the final lastStart.
    let mut wrong_start=[0u8;32];
    for i in (0..8).rev() { wrong_start[28..32].copy_from_slice(&limbs[i].to_le_bytes()); }
    assert_ne!(actual,wrong_start);
    // Rejected historical bug 2: terminal hasLast=false suppresses writeback.
    assert_ne!(actual,[0u8;32]);
 }
}
'''
manifest={'scope':'Exact selected Rust method/struct cuts over a minimal eight-u32 carrier; not whole crate or runtime. Executable P6 projection correspondence to Lean is still an explicit obligation.', 'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'file':str(src.relative_to(root)),'file_sha256':sha(text),'cuts':[{'signature':x.split('{',1)[0].strip(),'sha256':sha(x)} for x in [struct]+methods], 'generated_source_sha256':sha(out), 'lean_model':{'path':'/tmp/s5-p6-v3-overlay/sources/P6ChunksExactMutModelV3.lean','sha256':hashlib.sha256(model.read_bytes()).hexdigest()},'kani_status':'NOT RUN','native_status':'NOT RUN'}
f=w/'src/lib.rs';m=w/'source-binding.json'
if '--check' in sys.argv:
 assert f.read_text()==out
 old=json.loads(m.read_text())
 for k in ['file','file_sha256','cuts','generated_source_sha256','lean_model']: assert old[k]==manifest[k],k
 print('PASS: exact selected source cuts and corrected P6 model pin; no proof claim')
else:
 f.write_text(out);m.write_text(json.dumps(manifest,indent=2)+'\n')
