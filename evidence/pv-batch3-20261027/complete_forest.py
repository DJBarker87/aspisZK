from pathlib import Path
R=Path.cwd();D=R/'crates/aspis-r1-cost-probe/src';P=R/'crates/aspis-prover';S=R/'crates/aspis-statement/src/pool_v1'
s=(D/'host_forest.rs').read_text().replace('use alloc::{vec, vec::Vec};','use std::{vec, vec::Vec};')
f=(S/'pair_forest_hiding.rs').read_text();a=f.index('fn forest_path_aux_cell_is_used(');b=f.index('pub fn pool_v1_pair_forest_relation_free_mask_cells_v1(',a)
helpers=f[a:b]
# These loop bounds are frozen layout constants; retain the existing Option branch.
helpers=helpers.replace('for level in 0..POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {','let mut level=0usize; while level<POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {').replace('    }\n    false','        level+=1;\n    }\n    false')
a=f.index('pub fn pool_v1_pair_forest_relation_free_mask_cells_v1(');b=f.index('\nfn fingerprint_bytes',a);cells=f[a:b]
cells=cells.replace('Result<Vec<TraceCell>', 'Result<([TraceCell;3803],usize)').replace('let mut cells = Vec::new();','let mut cells=[TraceCell{row:0,column:0};3803];let mut len=0usize;').replace('for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {','let mut column=0usize;while column<POOL_V1_PAIR_TRACE_COLUMNS {').replace('for row in 0..POOL_V1_PAIR_TRACE_ROWS {','let mut row=0usize;while row<POOL_V1_PAIR_TRACE_ROWS {').replace('cells.push(TraceCell {','cells[len]=TraceCell {').replace('                });','                };len+=1;').replace('        }\n    }\n    Ok(cells)', '            row+=1;\n        }\n        column+=1;\n    }\n    Ok((cells,len))')
wrappers='''
/// Allocation adapters retain the existing host caller interfaces. They are
/// outside the Drop-free extraction roots and preserve logical element order.
pub fn materialize_active_rows()->Result<Vec<u16>,PoolV1PairHidingLayoutErrorV1>{
 let (rows,len)=pool_v1_pair_forest_copy_active_rows_v1()?;Ok(rows[..len].to_vec())
}
pub fn materialize_mask_cells()->Result<Vec<TraceCell>,PoolV1PairHidingLayoutErrorV1>{
 let (cells,len)=pool_v1_pair_forest_relation_free_mask_cells_v1()?;Ok(cells[..len].to_vec())
}
'''
(P/'src/host_forest.rs').write_text(s+'\n'+helpers+cells+wrappers)
(D/'host_forest.rs').unlink()
p=D/'lib.rs';s=p.read_text().replace('pub mod host_forest;', 'pub use aspis_prover::host_forest;');p.write_text(s)
p=P/'src/lib.rs';p.write_text(p.read_text()+'\n#[cfg(feature = "prover")]\npub mod host_forest;\n')
p=P/'Cargo.toml';s=p.read_text().replace('[features]','[features]\n# Prover-local extraction closure. Never selected by release programs.\nprover = []');p.write_text(s)
p=R/'crates/aspis-r1-cost-probe/Cargo.toml';s=p.read_text().replace('prover = ["private-leaf-salts",','prover = ["aspis-prover/prover", "private-leaf-salts",');p.write_text(s)
for file,names in [('state_only_hiding.rs',['pool_v1_pair_forest_copy_active_rows_v1','pool_v1_pair_forest_relation_free_mask_cells_v1']),('state_only_entropy.rs',['pool_v1_pair_forest_copy_active_row_masks_v1']),('state_only_hiding_rank.rs',['pool_v1_pair_forest_copy_active_rows_v1','pool_v1_pair_forest_copy_inactive_row_masks_v1','pool_v1_pair_forest_relation_free_mask_cells_v1'])]:
 p=P/'src'/file;s=p.read_text()
 # Remove names from the top-level nested import only, then select aliases.
 end=s.index('\nconst ') if '\nconst ' in s else s.index('\n#[derive')
 head,tail=s[:end],s[end:]
 for name in names:
  head=head.replace(name+',','')
  original='aspis_statement::pool_v1::'+name
  copy={'pool_v1_pair_forest_copy_active_rows_v1':'materialize_active_rows','pool_v1_pair_forest_relation_free_mask_cells_v1':'materialize_mask_cells'}.get(name,name)
  head+=f'\n#[cfg(not(feature="prover"))]\nuse {original};\n#[cfg(feature="prover")]\nuse crate::host_forest::{copy} as {name};\n'
 p.write_text(head+tail)
p=D/'prover.rs';s=p.read_text().replace('use aspis_statement::pool_v1::pool_v1_pair_forest_copy_active_row_masks_v1;','use crate::host_forest::pool_v1_pair_forest_copy_active_row_masks_v1;');p.write_text(s)
