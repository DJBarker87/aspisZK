//! Native tests of the verifier checkpoint close instruction. AccountInfo
//! models the owner/flags/data presented to the program; it does not model
//! System Program account creation or runtime writability enforcement.

use super::*;

const SEED: &str = "aspis-ckpt-0001";
const RENT: u64 = 13_196_160;

struct Account {
    key: Pubkey,
    owner: Pubkey,
    lamports: u64,
    data: Vec<u8>,
    signer: bool,
    writable: bool,
    executable: bool,
}

impl Account {
    fn info(&mut self) -> AccountInfo<'_> {
        AccountInfo::new(
            &self.key,
            self.signer,
            self.writable,
            &mut self.lamports,
            &mut self.data,
            &self.owner,
            self.executable,
            0,
        )
    }
}

struct Close {
    program: Pubkey,
    checkpoint: Account,
    base: Account,
}

impl Close {
    fn new() -> Self {
        let program = Pubkey::new_unique();
        let base_key = Pubkey::new_unique();
        let key = Pubkey::create_with_seed(&base_key, SEED, &program).unwrap();
        // Non-zero contents, as left by stage 1 or by a completed stage 2.
        let data = (0..verifier::checkpoint_size(Variant::S2)).map(|i| (i % 251) as u8 | 1).collect();
        Self {
            program,
            checkpoint: Account { key, owner: program, lamports: RENT, data, signer: false, writable: true, executable: false },
            base: Account { key: base_key, owner: Pubkey::default(), lamports: 5, data: vec![], signer: true, writable: true, executable: false },
        }
    }

    fn data(seed: &[u8]) -> Vec<u8> {
        let mut data = vec![7, seed.len() as u8];
        data.extend_from_slice(seed);
        data
    }

    fn run(&mut self, data: &[u8]) -> ProgramResult {
        let accounts = [self.checkpoint.info(), self.base.info()];
        crate::process_r1_cost_probe_instruction(&self.program, &accounts, data)
    }

    fn state(&self) -> (Vec<u8>, u64, u64) {
        (self.checkpoint.data.clone(), self.checkpoint.lamports, self.base.lamports)
    }

    fn rejects(&mut self, data: &[u8], error: ProgramError) {
        let before = self.state();
        assert_eq!(self.run(data), Err(error));
        assert_eq!(self.state(), before);
    }
}

#[test]
fn close_zeroes_checkpoint_and_moves_all_lamports_to_base() {
    let mut close = Close::new();
    let size = close.checkpoint.data.len();
    close.run(&Close::data(SEED.as_bytes())).unwrap();
    assert_eq!(close.checkpoint.data.len(), size);
    assert!(close.checkpoint.data.iter().all(|b| *b == 0));
    assert_eq!(close.checkpoint.lamports, 0);
    assert_eq!(close.base.lamports, RENT + 5);
    assert_eq!(close.checkpoint.owner, close.program);
}

#[test]
fn close_accepts_one_and_thirty_two_byte_seeds() {
    for seed in ["x", "0123456789abcdef0123456789abcdef"] {
        let mut close = Close::new();
        close.checkpoint.key = Pubkey::create_with_seed(&close.base.key, seed, &close.program).unwrap();
        close.run(&Close::data(seed.as_bytes())).unwrap();
        assert!(close.checkpoint.data.iter().all(|b| *b == 0));
        assert_eq!((close.checkpoint.lamports, close.base.lamports), (0, RENT + 5));
    }
}

#[test]
fn close_rejects_wrong_signer() {
    let mut close = Close::new();
    // A different signing key does not derive the checkpoint address.
    close.base.key = Pubkey::new_unique();
    close.rejects(&Close::data(SEED.as_bytes()), ProgramError::InvalidSeeds);
}

#[test]
fn close_rejects_non_signer_base() {
    let mut close = Close::new();
    close.base.signer = false;
    close.rejects(&Close::data(SEED.as_bytes()), ProgramError::MissingRequiredSignature);
}

#[test]
fn close_rejects_wrong_seed() {
    let mut close = Close::new();
    for seed in [&b"aspis-ckpt-0002"[..], b"aspis-ckpt-000", b"Aspis-ckpt-0001"] {
        close.rejects(&Close::data(seed), ProgramError::InvalidSeeds);
    }
    // A seed derived for another program id is also rejected.
    close.checkpoint.key = Pubkey::create_with_seed(&close.base.key, SEED, &Pubkey::new_unique()).unwrap();
    close.rejects(&Close::data(SEED.as_bytes()), ProgramError::InvalidSeeds);
}

#[test]
fn close_rejects_non_utf8_seed() {
    let mut close = Close::new();
    close.rejects(&Close::data(&[0xff, 0xfe]), ProgramError::InvalidInstructionData);
}

#[test]
fn close_rejects_wrong_owner_executable_or_readonly_checkpoint() {
    for case in 0..3 {
        let mut close = Close::new();
        match case {
            0 => close.checkpoint.owner = Pubkey::new_unique(),
            1 => close.checkpoint.executable = true,
            _ => close.checkpoint.writable = false,
        }
        close.rejects(&Close::data(SEED.as_bytes()), ProgramError::InvalidAccountData);
    }
}

#[test]
fn close_rejects_wrong_account_count() {
    let mut close = Close::new();
    let data = Close::data(SEED.as_bytes());
    let before = close.state();
    let mut extra = Account { key: Pubkey::new_unique(), owner: Pubkey::default(), lamports: 0, data: vec![], signer: false, writable: false, executable: false };
    let program = close.program;
    {
        let one = [close.checkpoint.info()];
        assert_eq!(crate::process_r1_cost_probe_instruction(&program, &one, &data), Err(ProgramError::NotEnoughAccountKeys));
    }
    {
        let three = [close.checkpoint.info(), close.base.info(), extra.info()];
        assert_eq!(crate::process_r1_cost_probe_instruction(&program, &three, &data), Err(ProgramError::NotEnoughAccountKeys));
    }
    assert_eq!(close.state(), before);
}

#[test]
fn close_rejects_malformed_instruction_data_at_the_route_guard() {
    let mut close = Close::new();
    let seed = SEED.as_bytes();
    let mut long = vec![7u8, 33];
    long.extend_from_slice(&[b'a'; 33]);
    let mut short = Close::data(seed);
    short.pop();
    let mut extended = Close::data(seed);
    extended.push(b'1');
    let mut tag6 = Close::data(seed);
    tag6[0] = 6;
    for data in [vec![7], vec![7, 0], short, extended, long, tag6] {
        close.rejects(&data, ProgramError::InvalidInstructionData);
    }
    // The handler re-checks the shape if reached without the route guard.
    let before = close.state();
    let accounts = [close.checkpoint.info(), close.base.info()];
    assert_eq!(close_checkpoint(&close.program, &accounts, &[7, 0]), Err(ProgramError::InvalidInstructionData));
    drop(accounts);
    assert_eq!(close.state(), before);
}

#[test]
fn close_rejects_lamport_overflow_without_moving_lamports() {
    let mut close = Close::new();
    close.base.lamports = u64::MAX;
    close.rejects(&Close::data(SEED.as_bytes()), ProgramError::ArithmeticOverflow);
}
