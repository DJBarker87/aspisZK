//! Native unit tests. `AccountInfo::resize` and `original_data_len` read and
//! write the bytes just before the key and the data, as laid out by the
//! runtime's input serialization, so the fixtures reproduce that layout.

use super::*;
use std::{boxed::Box, vec, vec::Vec};

const PROGRAM: Pubkey = Pubkey::new_from_array([7; 32]);
const BASE: Pubkey = Pubkey::new_from_array([9; 32]);
const SEED: &str = "p0abcdef0123456789abcdef01234567";

#[repr(C, align(8))]
struct KeySlot {
    _pad: u32,
    original_data_len: u32,
    key: Pubkey,
}

/// One account in runtime layout: an 8-byte length word, then the data.
struct Fixture {
    key: Box<KeySlot>,
    owner: Box<Pubkey>,
    lamports: Box<u64>,
    words: Vec<u64>,
    len: usize,
    signer: bool,
    writable: bool,
    executable: bool,
}

impl Fixture {
    fn new(key: Pubkey, owner: Pubkey, len: usize, lamports: u64) -> Self {
        let mut words = vec![0u64; 1 + len.div_ceil(8) + 1];
        words[0] = len as u64;
        Fixture {
            key: Box::new(KeySlot { _pad: 0, original_data_len: len as u32, key }),
            owner: Box::new(owner),
            lamports: Box::new(lamports),
            words,
            len,
            signer: false,
            writable: true,
            executable: false,
        }
    }
    fn info(&mut self) -> AccountInfo<'_> {
        // SAFETY: the data slice starts 8 bytes into an 8-aligned buffer whose
        // first word is the serialized length, as in the runtime layout.
        let data = unsafe {
            core::slice::from_raw_parts_mut((self.words.as_mut_ptr() as *mut u8).add(8), self.len)
        };
        AccountInfo::new(
            &self.key.key,
            self.signer,
            self.writable,
            &mut self.lamports,
            data,
            &self.owner,
            self.executable,
            0,
        )
    }
    fn bytes(&self) -> &[u8] {
        let len = self.words[0] as usize;
        unsafe { core::slice::from_raw_parts((self.words.as_ptr() as *const u8).add(8), len) }
    }
}

fn target_key(base: &Pubkey, seed: &str) -> Pubkey {
    Pubkey::create_with_seed(base, seed, &PROGRAM).unwrap()
}

fn pair(len: usize) -> (Fixture, Fixture) {
    let target = Fixture::new(target_key(&BASE, SEED), PROGRAM, len, 1_000_000);
    let mut base = Fixture::new(BASE, system_program::ID, 0, 5_000);
    base.signer = true;
    base.writable = true;
    (target, base)
}

fn write_data(seed: &[u8], offset: u32, bytes: &[u8]) -> Vec<u8> {
    let mut d = vec![WRITE_TAG, seed.len() as u8];
    d.extend_from_slice(seed);
    d.extend_from_slice(&offset.to_le_bytes());
    d.extend_from_slice(bytes);
    d
}

fn close_data(seed: &[u8]) -> Vec<u8> {
    let mut d = vec![CLOSE_TAG, seed.len() as u8];
    d.extend_from_slice(seed);
    d
}

fn run(target: &mut Fixture, base: &mut Fixture, data: &[u8]) -> ProgramResult {
    let accounts = [target.info(), base.info()];
    process_instruction(&PROGRAM, &accounts, data)
}

#[test]
fn decode_rejects_malformed_data() {
    let bad: &[&[u8]] = &[
        &[],
        &[0],
        &[3, 1, b'a'],
        &[6, 1, b'a'],
        &[WRITE_TAG],
        &[WRITE_TAG, 0, 0, 0, 0, 0, 1],
        &[WRITE_TAG, 33],
        &[WRITE_TAG, 2, b'a'],
        &[WRITE_TAG, 1, b'a', 0, 0, 0],
        &[WRITE_TAG, 1, b'a', 0, 0, 0, 0],
        &[WRITE_TAG, 2, 0xc3, 0x28, 0, 0, 0, 0, 1],
        &[WRITE_TAG, 1, 0xff, 0, 0, 0, 0, 1],
        &[CLOSE_TAG],
        &[CLOSE_TAG, 0],
        &[CLOSE_TAG, 2, b'a'],
        &[CLOSE_TAG, 1, b'a', 0],
        &[CLOSE_TAG, 1, 0x80],
    ];
    for data in bad {
        assert_eq!(decode(data), Err(ProgramError::InvalidInstructionData), "{data:?}");
    }
    let long = [b'a'; 33];
    assert!(decode(&write_data(&long, 0, &[1])).is_err());
    assert!(decode(&close_data(&long)).is_err());
    let max = [b'a'; 32];
    assert!(decode(&write_data(&max, 0, &[1])).is_ok());
    assert!(decode(&close_data(&max)).is_ok());
    assert_eq!(
        decode(&write_data("é".as_bytes(), 5, &[1, 2])),
        Ok(UploadInstruction::Write { seed: "é", offset: 5, bytes: &[1, 2] })
    );
    assert_eq!(decode(&close_data(b"x")), Ok(UploadInstruction::Close { seed: "x" }));
}

#[test]
fn write_happy_path_and_ranges() {
    let (mut t, mut b) = pair(16);
    b.writable = false;
    run(&mut t, &mut b, &write_data(SEED.as_bytes(), 3, &[1, 2, 3])).unwrap();
    assert_eq!(&t.bytes()[..8], &[0, 0, 0, 1, 2, 3, 0, 0]);
    run(&mut t, &mut b, &write_data(SEED.as_bytes(), 15, &[9])).unwrap();
    run(&mut t, &mut b, &write_data(SEED.as_bytes(), 0, &[5; 16])).unwrap();
    assert_eq!(t.bytes(), &[5; 16]);
    for (offset, len) in [(16u32, 1usize), (15, 2), (0, 17), (u32::MAX, 1), (u32::MAX - 1, 4)] {
        assert_eq!(
            run(&mut t, &mut b, &write_data(SEED.as_bytes(), offset, &vec![1; len])),
            Err(ProgramError::AccountDataTooSmall),
            "{offset} {len}"
        );
    }
    assert_eq!(t.bytes(), &[5; 16]);
    assert_eq!(*t.lamports, 1_000_000);
}

#[test]
fn account_checks_reject() {
    let data = write_data(SEED.as_bytes(), 0, &[1]);
    let cdata = close_data(SEED.as_bytes());
    for d in [&data, &cdata] {
        let (mut t, mut b) = pair(4);
        t.owner = Box::new(Pubkey::new_from_array([3; 32]));
        assert_eq!(run(&mut t, &mut b, d), Err(ProgramError::IncorrectProgramId));
        let (mut t, mut b) = pair(4);
        t.owner = Box::new(system_program::ID);
        assert_eq!(run(&mut t, &mut b, d), Err(ProgramError::IncorrectProgramId));
        let (mut t, mut b) = pair(4);
        b.signer = false;
        assert_eq!(run(&mut t, &mut b, d), Err(ProgramError::MissingRequiredSignature));
        let (mut t, mut b) = pair(4);
        t.writable = false;
        assert_eq!(run(&mut t, &mut b, d), Err(ProgramError::InvalidAccountData));
        let (mut t, mut b) = pair(4);
        t.executable = true;
        assert_eq!(run(&mut t, &mut b, d), Err(ProgramError::InvalidAccountData));
        // Someone else's account: the signer is a different base.
        let (mut t, _) = pair(4);
        let mut other = Fixture::new(Pubkey::new_from_array([10; 32]), system_program::ID, 0, 1);
        other.signer = true;
        assert_eq!(run(&mut t, &mut other, d), Err(ProgramError::InvalidSeeds));
        // Right base, wrong seed.
        let (mut t, mut b) = pair(4);
        let wrong = if d[0] == WRITE_TAG { write_data(b"p1", 0, &[1]) } else { close_data(b"p1") };
        assert_eq!(run(&mut t, &mut b, &wrong), Err(ProgramError::InvalidSeeds));
        // Target signs but is not the derived address (e.g. a keypair account).
        let mut kp = Fixture::new(Pubkey::new_from_array([11; 32]), PROGRAM, 4, 1);
        kp.signer = true;
        let (_, mut b) = pair(4);
        assert_eq!(run(&mut kp, &mut b, d), Err(ProgramError::InvalidSeeds));
        // Account count.
        let (mut t, mut b) = pair(4);
        assert_eq!(
            process_instruction(&PROGRAM, &[t.info()], d),
            Err(ProgramError::NotEnoughAccountKeys)
        );
        let mut extra = Fixture::new(Pubkey::new_from_array([12; 32]), PROGRAM, 0, 0);
        assert_eq!(
            process_instruction(&PROGRAM, &[t.info(), b.info(), extra.info()], d),
            Err(ProgramError::NotEnoughAccountKeys)
        );
        assert_eq!(process_instruction(&PROGRAM, &[], d), Err(ProgramError::NotEnoughAccountKeys));
        let (t, _) = pair(4);
        assert_eq!(*t.lamports, 1_000_000);
        assert!(t.bytes().iter().all(|&x| x == 0));
    }
}

#[test]
fn alias_target_equals_base_rejected() {
    // Same key twice (the runtime would hand two AccountInfos for one account).
    let mut a = Fixture::new(BASE, PROGRAM, 4, 10);
    a.signer = true;
    let mut b = Fixture::new(BASE, PROGRAM, 4, 10);
    b.signer = true;
    for d in [write_data(SEED.as_bytes(), 0, &[1]), close_data(SEED.as_bytes())] {
        assert_eq!(run(&mut a, &mut b, &d), Err(ProgramError::InvalidArgument));
    }
}

#[test]
fn close_happy_path_refunds_everything() {
    let (mut t, mut b) = pair(58_295);
    run(&mut t, &mut b, &write_data(SEED.as_bytes(), 0, &[0xaa; 3763])).unwrap();
    run(&mut t, &mut b, &close_data(SEED.as_bytes())).unwrap();
    assert_eq!(*t.lamports, 0);
    assert_eq!(*b.lamports, 1_005_000);
    assert_eq!(*t.owner, system_program::ID);
    assert_eq!(t.words[0], 0, "serialized data length must be zero");
    // The underlying bytes were zeroed before the shrink.
    assert!(unsafe { core::slice::from_raw_parts((t.words.as_ptr() as *const u8).add(8), 58_295) }
        .iter()
        .all(|&x| x == 0));
}

#[test]
fn close_requires_writable_base() {
    let (mut t, mut b) = pair(8);
    b.writable = false;
    assert_eq!(run(&mut t, &mut b, &close_data(SEED.as_bytes())), Err(ProgramError::InvalidAccountData));
    assert_eq!(*t.lamports, 1_000_000);
}

#[test]
fn close_overflow_mutates_nothing() {
    let (mut t, mut b) = pair(8);
    run(&mut t, &mut b, &write_data(SEED.as_bytes(), 0, &[4; 8])).unwrap();
    *b.lamports = u64::MAX;
    assert_eq!(run(&mut t, &mut b, &close_data(SEED.as_bytes())), Err(ProgramError::ArithmeticOverflow));
    assert_eq!(t.bytes(), &[4; 8]);
    assert_eq!(*t.owner, PROGRAM);
    assert_eq!(*t.lamports, 1_000_000);
}

#[test]
fn write_or_close_after_close_rejected() {
    let (mut t, mut b) = pair(8);
    run(&mut t, &mut b, &close_data(SEED.as_bytes())).unwrap();
    assert_eq!(
        run(&mut t, &mut b, &write_data(SEED.as_bytes(), 0, &[1])),
        Err(ProgramError::IncorrectProgramId)
    );
    assert_eq!(run(&mut t, &mut b, &close_data(SEED.as_bytes())), Err(ProgramError::IncorrectProgramId));
    assert_eq!(*b.lamports, 1_005_000);
}
