//! Focused source-level V8 per-C1 image-containment probe.
//!
//! The complete rank gate historically required every serialized raw block to
//! span its ambient coordinate product.  That is stronger than hiding and is
//! false for a legal Frobenius-conjugate pair of OOD points.  This diagnostic
//! instead asks the first exact question needed by the hiding proof: is every
//! physical semantic trace direction in the image of the relation-free mask
//! basis after applying the same inactive-row balancing convention?

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V8PerC1ImageContainmentReport {
    pub layout: &'static str,
    pub query_count: usize,
    pub ambient_raw_m31: usize,
    pub mask_rank_m31: [usize; STATE_ONLY_HIDING_C1_COLUMNS],
    pub mask_generators: [usize; STATE_ONLY_HIDING_C1_COLUMNS],
    pub physical_superset_generators: [usize; STATE_ONLY_HIDING_C1_COLUMNS],
    pub physical_superset_contained: bool,
}

fn probe_v8_a100_per_c1_image_containment(
    schedule: &StateOnlyTranscriptScheduleResult,
    layout: RankLayout,
) -> Result<V8PerC1ImageContainmentReport, StateOnlyHidingRankGateError> {
    if schedule.query_count != 22 {
        return Err(StateOnlyHidingRankGateError::Shape);
    }

    let domain_log = STATE_ONLY_LOG_ROWS + 10;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let rows = row_public_maps(
        &encoder,
        domain_log,
        schedule,
        PcsSchedule::RootMessageV8Log20,
        layout,
    )?;
    let ambient_raw_m31 = rows[0].layer0_m31.len() + 12 + 4 * rows[0].pre_gamma_circle_ood.len();
    let mut active = [false; TRACE_ROWS];
    for row in rank_active_rows(layout) {
        active[usize::from(row)] = true;
    }
    let cells = match layout {
        RankLayout::PoolPairV1 => pool_v1_pair_relation_free_mask_cells_v1()
            .map_err(|_| StateOnlyHidingRankGateError::Layout)?,
        RankLayout::PoolPairForestV1 => pool_v1_pair_forest_relation_free_mask_cells_v1()
            .map_err(|_| StateOnlyHidingRankGateError::Layout)?,
        _ => return Err(StateOnlyHidingRankGateError::Layout),
    };
    let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        cells_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }

    let mut mask_rank_m31 = [0usize; STATE_ONLY_HIDING_C1_COLUMNS];
    let mut mask_generators = [0usize; STATE_ONLY_HIDING_C1_COLUMNS];
    let mut physical_superset_generators = [0usize; STATE_ONLY_HIDING_C1_COLUMNS];
    for (column, cells) in cells_by_column.iter().enumerate() {
        let dependent = cells
            .iter()
            .copied()
            .filter(|row| !active[*row])
            .last()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        let mut mask_image = CarryEchelon::new(ambient_raw_m31);
        for &row in cells {
            if row == dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(dependent);
            mask_image.reduce_with_pivot(c1_raw_difference(&rows, row, subtract), Vec::new());
            mask_generators[column] += 1;
        }
        mask_rank_m31[column] = mask_image.rank;

        // This is the exact conservative physical basis used by the complete
        // witness audit: row zero is same-statement public data; the selected
        // inactive dependent is eliminated; active rows contribute e_r and
        // inactive rows contribute e_r-e_d(c).  It contains the legal witness
        // difference image, so containment here is the stronger first gate.
        for row in 1..TRACE_ROWS {
            if row == dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(dependent);
            let source = column * TRACE_ROWS + row;
            physical_superset_generators[column] += 1;
            if mask_image
                .quotient_existing(c1_raw_difference(&rows, row, subtract), Vec::new())
                .is_none()
            {
                return Err(StateOnlyHidingRankGateError::WitnessRawQuotient { source });
            }
        }
    }

    Ok(V8PerC1ImageContainmentReport {
        layout: match layout {
            RankLayout::PoolPairV1 => "pool_pair_v1_rank_model",
            RankLayout::PoolPairForestV1 => "pool_pair_forest_v1",
            _ => unreachable!(),
        },
        query_count: schedule.query_count,
        ambient_raw_m31,
        mask_rank_m31,
        mask_generators,
        physical_superset_generators,
        physical_superset_contained: true,
    })
}

/// Exact q22/two-OOD raw-view containment for the pair-tree rank model.
pub fn probe_v8_a100_pool_pair_per_c1_image_containment(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<V8PerC1ImageContainmentReport, StateOnlyHidingRankGateError> {
    probe_v8_a100_per_c1_image_containment(schedule, RankLayout::PoolPairV1)
}

/// Exact q22/two-OOD raw-view containment for the deployed pair-forest mask
/// inventory and balancing convention.
pub fn probe_v8_a100_pool_pair_forest_per_c1_image_containment(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<V8PerC1ImageContainmentReport, StateOnlyHidingRankGateError> {
    probe_v8_a100_per_c1_image_containment(schedule, RankLayout::PoolPairForestV1)
}
