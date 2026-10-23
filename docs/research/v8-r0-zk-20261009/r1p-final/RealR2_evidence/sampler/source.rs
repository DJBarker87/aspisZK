// Exact borrowed native sampler methods, isolated from Drop and unrelated builders.
type HashFn=fn(&[&[u8]])->[u8;32];
const P:u32=0x7fff_ffff;
const MASK_SAMPLE_RETRY_LIMIT:usize=16;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
#[cfg_attr(kani,derive(kani::Arbitrary))]
struct M31(u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum StateOnlyMaskBuildError{MaskSampleExhausted}
#[derive(Clone,Copy)]
struct SeedExpander{hash:HashFn,seed:[u8;32],counter:u64,block:[u8;32],word:usize}
fn state_only_mask_expander_block(hash:HashFn,seed:[u8;32],counter:u64)->[u8;32]{
 hash(&[b"aspis:state-only:private-mask-expand:v1",&seed,&counter.to_le_bytes()])
}
impl SeedExpander {
fn next_word(&mut self) -> u32 {
        if self.word == 8 {
            self.block = state_only_mask_expander_block(self.hash, self.seed, self.counter);
            self.counter = self.counter.wrapping_add(1);
            self.word = 0;
        }
        let start = 4 * self.word;
        self.word += 1;
        u32::from_le_bytes(self.block[start..start + 4].try_into().unwrap())
    }
fn m31(&mut self) -> Result<M31, StateOnlyMaskBuildError> {
        for _ in 0..MASK_SAMPLE_RETRY_LIMIT {
            let candidate = self.next_word() & 0x7fff_ffff;
            if candidate < P {
                return Ok(M31(candidate));
            }
        }
        Err(StateOnlyMaskBuildError::MaskSampleExhausted)
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
#[cfg_attr(kani,derive(kani::Arbitrary))]
struct State{seed:[u8;32],counter:u64,block:[u8;32],word:usize}
fn next(hash: HashFn, domain: &[u8], mut state: State) -> (u32, State) {
    if state.word == 8 {
        state.block = hash(&[domain, &state.seed, &state.counter.to_le_bytes()]);
        state.counter = state.counter.wrapping_add(1);
        state.word = 0;
    }
    let offset = state.word * 4;
    let bytes = [state.block[offset], state.block[offset+1], state.block[offset+2], state.block[offset+3]];
    state.word += 1;
    (u32::from_le_bytes(bytes), state)
}
fn limb_caller(hash: HashFn, domain: &[u8], mut state: State)
    -> (Result<M31, StateOnlyMaskBuildError>, State)
{
    for _ in 0..16 {
        let (word, after) = next(hash, domain, state);
        state = after;
        let candidate = word & 0x7fff_ffff;
        if candidate < P { return (Ok(M31(candidate)), state); }
    }
    (Err(StateOnlyMaskBuildError::MaskSampleExhausted), state)
}
