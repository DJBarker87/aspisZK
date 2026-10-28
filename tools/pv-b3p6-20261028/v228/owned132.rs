//! Token-exact native root/helper copies; namespace and schedule dependency only.
use aspis_statement::pool_v1::{pair_forest_hiding::*,pair_tree_hiding::*,pair_tree_profile::*};
use aspis_statement::trace_v4::TraceCell;
use super::owned133::forest::build_pool_v1_pair_forest_copy_row_schedule_v1;
fn forest_path_aux_cell_is_used(row: usize, column: usize) -> bool {
    for level in 0..POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
        let Some(base) = pool_v1_pair_forest_path_base_row_v1(level) else {
            return false;
        };
        if (row == base && column <= 8) || row == base + 1 {
            return true;
        }
    }
    false
}
fn forest_poseidon_row(row: usize) -> bool {
    row < POOL_V1_PAIR_FOREST_POSEIDON_BLOCKS_V1 * POOL_V1_PAIR_TRACE_BLOCK_ROWS
}
fn forest_aux_cell_is_used(row: usize, column: usize) -> bool {
    if row < POOL_V1_PAIR_FOREST_PATH_AUX_ROW_START_V1 {
        return false;
    }
    if row < POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1 {
        forest_path_aux_cell_is_used(row, column)
    } else {
        let translated = row - 3 * POOL_V1_PAIR_TRACE_BLOCK_ROWS;
        pool_v1_pair_aux_cell_is_relation_used_v1(translated, column)
    }
}
pub fn pool_v1_pair_forest_relation_free_mask_cells_v1(
) -> Result<Vec<TraceCell>, PoolV1PairHidingLayoutErrorV1> {
    let _ = build_pool_v1_pair_forest_copy_row_schedule_v1()?;
    let mut cells = Vec::new();
    for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
        for row in 0..POOL_V1_PAIR_TRACE_ROWS {
            let poseidon = forest_poseidon_row(row);
            let padding = poseidon
                && row % POOL_V1_PAIR_TRACE_BLOCK_ROWS
                    >= POOL_V1_PAIR_RELATION_FREE_PADDING_LOCAL_ROW_START_V1;
            let auxiliary = !poseidon && !forest_aux_cell_is_used(row, column);
            if padding || auxiliary {
                cells.push(TraceCell {
                    row: row as u16,
                    column: column as u8,
                });
            }
        }
    }
    Ok(cells)
}
