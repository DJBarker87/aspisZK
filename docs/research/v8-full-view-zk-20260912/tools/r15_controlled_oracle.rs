//! Research-only deterministic function: SHA-256 with a fixed finite table.
//! No adaptive programming, oracle-law claim, or production feature.
use std::sync::OnceLock;
#[path = "r15_query_audit.rs"]
mod query_audit;

type Cell = ([u8; 33], [u8; 32]);

pub fn answer(parts: &[&[u8]], original: [u8; 32]) -> [u8; 32] {
    query_audit::observe(parts);
    static CELLS: OnceLock<Vec<Cell>> = OnceLock::new();
    let cells = CELLS.get_or_init(|| {
        let Some(path) = std::env::var_os("ASPIS_R15_ORACLE_TABLE") else {
            return Vec::new();
        };
        let bytes = std::fs::read(path).expect("research oracle table");
        assert!(bytes.len() >= 8 && &bytes[..8] == b"R15ORCL1");
        assert_eq!((bytes.len() - 8) % 65, 0);
        let mut cells = Vec::<Cell>::new();
        for record in bytes[8..].chunks_exact(65) {
            let key: [u8; 33] = record[..33].try_into().unwrap();
            let value: [u8; 32] = record[33..].try_into().unwrap();
            assert_eq!(key[32], 1, "only ordinary squeeze inputs are overridden");
            assert!(!cells.iter().any(|(prior, _)| *prior == key));
            cells.push((key, value));
        }
        assert!(cells.len() <= 6, "two worlds, three query blocks each");
        cells
    });
    if cells.is_empty() || parts.iter().map(|part| part.len()).sum::<usize>() != 33 {
        return original;
    }
    let mut input = [0u8; 33];
    let mut at = 0;
    for part in parts {
        input[at..at + part.len()].copy_from_slice(part);
        at += part.len();
    }
    cells
        .iter()
        .find(|(key, _)| *key == input)
        .map_or(original, |(_, answer)| *answer)
}

pub fn query_entry(state: [u8; 32]) {
    query_audit::begin(state);
    let hex: String = state.iter().map(|byte| format!("{byte:02x}")).collect();
    eprintln!("R15_Q22_ENTRY {hex}");
}

pub fn query_result(queries: &[u32]) {
    query_audit::end();
    eprintln!("R15_Q22_RESULT {queries:?}");
}
