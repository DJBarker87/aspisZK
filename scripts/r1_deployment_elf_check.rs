//! Standalone, dependency-free byte audit. Compile with rustc -O.
use std::{env, fs, ops::Range};
#[allow(dead_code)]
#[path = "../programs/r1-cost-probe/src/deployment_ids.rs"]
mod ids;

fn u16_at(b: &[u8], i: usize) -> usize {
    u16::from_le_bytes(b[i..i + 2].try_into().unwrap()) as usize
}
fn u64_at(b: &[u8], i: usize) -> usize {
    usize::try_from(u64::from_le_bytes(b[i..i + 8].try_into().unwrap())).unwrap()
}
fn sections(b: &[u8]) -> Vec<(String, Range<usize>)> {
    assert_eq!(&b[..6], b"\x7fELF\x02\x01", "expected ELF64 LE");
    let (offset, stride, count, names) =
        (u64_at(b, 40), u16_at(b, 58), u16_at(b, 60), u16_at(b, 62));
    assert!(stride >= 64 && names < count);
    let names_header = offset + names * stride;
    let names_offset = u64_at(b, names_header + 24);
    (0..count)
        .map(|i| {
            let h = offset + i * stride;
            let name = u32::from_le_bytes(b[h..h + 4].try_into().unwrap()) as usize + names_offset;
            let end = b[name..].iter().position(|&c| c == 0).unwrap() + name;
            let start = u64_at(b, h + 24);
            (
                String::from_utf8(b[name..end].to_vec()).unwrap(),
                start..start + u64_at(b, h + 32),
            )
        })
        .collect()
}
fn main() {
    let args: Vec<_> = env::args().collect();
    assert_eq!(
        args.len(),
        5,
        "usage: elf-check frozen.so devnet.so POOL_BASE58 REGISTRY_BASE58"
    );
    let frozen = fs::read(&args[1]).unwrap();
    let devnet = fs::read(&args[2]).unwrap();
    let old_sections = sections(&frozen);
    let new_sections = sections(&devnet);
    println!(
        "frozen_bytes={} devnet_bytes={} section_table_identical={}",
        frozen.len(),
        devnet.len(),
        old_sections == new_sections
    );
    let text = old_sections
        .iter()
        .find(|(name, _)| name == ".text")
        .unwrap();
    let new_text = new_sections
        .iter()
        .find(|(name, _)| name == ".text")
        .unwrap();
    let text_equal = frozen[text.1.clone()] == devnet[new_text.1.clone()];
    println!(
        "text_file_offset={} text_bytes={} text_identical={text_equal}",
        text.1.start,
        text.1.len()
    );
    println!(
        "devnet_text_file_offset={} devnet_text_bytes={}",
        new_text.1.start,
        new_text.1.len()
    );
    let mut expected = frozen.clone();
    let mut valid = frozen.len() == devnet.len() && old_sections == new_sections && text_equal;
    for (label, byte, value) in [("pool", 0x41, &args[3]), ("registry", 0x44, &args[4])] {
        let new = ids::program_id(value).unwrap();
        let matches: Vec<_> = frozen
            .windows(32)
            .enumerate()
            .filter_map(|(i, w)| (w == [byte; 32]).then_some(i))
            .collect();
        println!("{label} contiguous_32_byte_occurrences={}", matches.len());
        valid &= matches.len() == 1;
        for start in matches {
            let (section, range) = old_sections
                .iter()
                .find(|(_, r)| r.contains(&start) && start + 32 <= r.end)
                .unwrap();
            println!("{label} file_offset={start} file_hex=0x{start:x} section={section} section_offset={} bytes=32 replacement_matches={}", start - range.start, devnet[start..start + 32] == new);
            valid &= section == ".rodata" || section == ".data";
            expected[start..start + 32].copy_from_slice(&new);
        }
    }
    let changes = frozen.iter().zip(&devnet).filter(|(a, b)| a != b).count();
    let unexpected = expected.iter().zip(&devnet).filter(|(a, b)| a != b).count();
    println!(
        "overlap_changed_bytes={changes} overlap_unexpected_bytes={unexpected} exact_two_constant_patch={}",
        expected == devnet
    );
    for (i, (a, b)) in expected
        .iter()
        .zip(&devnet)
        .enumerate()
        .filter(|(_, (a, b))| a != b)
        .take(20)
    {
        println!("unexpected offset={i} expected={a:02x} actual={b:02x}");
    }
    if !valid || expected != devnet {
        eprintln!(
            "deployment identity gate FAILED: do not admit this ELF as the data-only release"
        );
        std::process::exit(1);
    }
}
