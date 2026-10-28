//! Prover-local Drop-free forest inventory. Originals remain in aspis-statement.
use aspis_core::field::{M31, QM31};
use aspis_statement::logup::CopyLogUpRow;
use aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1;
use aspis_statement::pool_v1::pair_trace::*;
use aspis_statement::pool_v1::{pair_forest_hiding::*, pair_tree_hiding::*, pair_tree_profile::*};
use aspis_statement::poseidon2::MERKLE_NODE_COMPRESSION_V3_TWEAK;
use aspis_statement::trace_v4::TraceCell;
use std::vec::Vec;

#[derive(Clone, Copy)]
pub struct Schedule {
    pub data: [PoolV1PairCopyRowLinkV1; 136],
    pub len: usize,
}
impl Schedule {
    fn new() -> Self {
        Self {
            data: [PoolV1PairCopyRowLinkV1 {
                kind: PoolV1PairCopyRowLinkKindV1::OwnerOutput,
                producer_row: 0,
                consumer_row: 0,
            }; 136],
            len: 0,
        }
    }
    fn push(&mut self, value: PoolV1PairCopyRowLinkV1) {
        self.data[self.len] = value;
        self.len += 1;
    }
    fn len(&self) -> usize {
        self.len
    }
}
#[derive(Clone, Copy)]
pub struct Registry {
    pub data: [PoolV1PairCopyLinkV1; 136],
    pub len: usize,
}
impl Registry {
    fn new() -> Self {
        Self {
            data: [PoolV1PairCopyLinkV1 {
                id: 0,
                tag: M31::ZERO,
                kind: PoolV1PairCopyRowLinkKindV1::OwnerOutput,
                weight: PoolV1PairCopyWeightV1::One,
                producer: PoolV1PairCopyTupleV1 {
                    row: 0,
                    limbs: [PoolV1PairTupleLimbV1::Zero; 16],
                },
                consumer: PoolV1PairCopyTupleV1 {
                    row: 0,
                    limbs: [PoolV1PairTupleLimbV1::Zero; 16],
                },
            }; 136],
            len: 0,
        }
    }
    fn push(&mut self, value: PoolV1PairCopyLinkV1) {
        self.data[self.len] = value;
        self.len += 1;
    }
    fn len(&self) -> usize {
        self.len
    }
}
#[inline]
fn link(
    kind: PoolV1PairCopyRowLinkKindV1,
    producer_row: usize,
    consumer_row: usize,
) -> PoolV1PairCopyRowLinkV1 {
    PoolV1PairCopyRowLinkV1 {
        kind,
        producer_row: producer_row as u16,
        consumer_row: consumer_row as u16,
    }
}

pub fn build_pool_v1_pair_copy_row_schedule_v1() -> Result<Schedule, PoolV1PairHidingLayoutErrorV1>
{
    let mut links = Schedule::new();

    links.push(link(PoolV1PairCopyRowLinkKindV1::SpongeCarry { from: 1, to: 2 }, 1 * 16 + 11, 2 * 16));
    links.push(link(PoolV1PairCopyRowLinkKindV1::SpongeCarry { from: 2, to: 3 }, 2 * 16 + 11, 3 * 16));
    links.push(link(PoolV1PairCopyRowLinkKindV1::SpongeCarry { from: 25, to: 26 }, 25 * 16 + 11, 26 * 16));
    links.push(link(PoolV1PairCopyRowLinkKindV1::SpongeCarry { from: 27, to: 28 }, 27 * 16 + 11, 28 * 16));
    links.push(link(PoolV1PairCopyRowLinkKindV1::SpongeCarry { from: 28, to: 29 }, 28 * 16 + 11, 29 * 16));
    links.push(link(PoolV1PairCopyRowLinkKindV1::SpongeCarry { from: 30, to: 31 }, 30 * 16 + 11, 31 * 16));
    links.push(link(PoolV1PairCopyRowLinkKindV1::SpongeCarry { from: 31, to: 32 }, 31 * 16 + 11, 32 * 16));
    links.push(link(PoolV1PairCopyRowLinkKindV1::OwnerOutput, 11, 28));
    links.push(link(PoolV1PairCopyRowLinkKindV1::NullifierKey, 12, 412));
    links.push(link(PoolV1PairCopyRowLinkKindV1::InputSaltHead, 44, 428));
    links.push(link(PoolV1PairCopyRowLinkKindV1::InputSaltTail, 60, 428));

    let mut level = 0usize;
    while level < POOL_V1_PAIR_PRIVATE_DIRECTIONS {
        let aux =
            pool_v1_pair_path_base_row_v1(level).ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?;
        let previous_output = (3 + level) * 16 + 11;
        let target_block = 4 + level;
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { level: level as u8 },
            previous_output,
            aux,
        ));
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { level: level as u8 },
            aux + 1,
            target_block * 16 + 12,
        ));
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::PrivatePathRight { level: level as u8 },
            aux + 1,
            target_block * 16,
        ));
        level += 1;
    }

    links.push(link(PoolV1PairCopyRowLinkKindV1::ValueSource { value: 0 }, 44, 960));
    links.push(link(PoolV1PairCopyRowLinkKindV1::ValueSource { value: 1 }, 460, 962));
    links.push(link(PoolV1PairCopyRowLinkKindV1::ValueSource { value: 2 }, 508, 964));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::ConservationInput,
        960,
        966,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::ConservationRecipient,
        962,
        966,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::ConservationChange,
        964,
        967,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::ConservationPartial,
        966,
        967,
    ));

    // Historical input-pair occupancy: duplicate the committed right child
    // and private selected-side bit into one row-local certificate.
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::InputSecondCommitment,
        64,
        POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
    ));
    let input_selected_side_row =
        pool_v1_pair_path_base_row_v1(0).ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?;
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::InputSelectedSide,
        input_selected_side_row,
        POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW,
    ));

    // Newly appended output pair: the change commitment is certified in its
    // own occupancy row before that same complete digest enters the right
    // child of block 33. The recipient is the always-occupied left child.
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::OutputSecondCommitment,
        32 * 16 + 11,
        POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::OutputPairFirst,
        29 * 16 + 11,
        33 * 16 + 12,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::OutputPairFirstWithdrawal,
        32 * 16 + 11,
        33 * 16 + 12,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::OutputPairSecond,
        POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW,
        33 * 16,
    ));

    let mut level = 0usize;
    while level < 20usize {
        let previous_output = (33 + level) * 16 + 11;
        let target_block = 34 + level;
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::AppendCurrentLeft { level: level as u8 },
            previous_output,
            target_block * 16 + 12,
        ));
        links.push(link(
            PoolV1PairCopyRowLinkKindV1::AppendCurrentRight { level: level as u8 },
            previous_output,
            target_block * 16,
        ));
        level += 1;
    }

    if links.len() != POOL_V1_PAIR_COPY_ROW_LINKS_V1 {
        return Err(PoolV1PairHidingLayoutErrorV1::Shape);
    }
    endpoint_counts(&links.data, links.len)?;
    Ok(links)
}
fn endpoint_counts(
    links: &[PoolV1PairCopyRowLinkV1; 136],
    len: usize,
) -> Result<([u8; 1024], [u8; 1024]), PoolV1PairHidingLayoutErrorV1> {
    let mut producers = [0u8; 1024];
    let mut consumers = [0u8; 1024];
    let mut i = 0usize;
    while i < len {
        let item = links[i];
        let p = item.producer_row as usize;
        let c = item.consumer_row as usize;
        if p >= 1024 || producers[p] >= 2 {
            return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity { row: p as u16 });
        }
        producers[p] += 1;
        if c >= 1024 || consumers[c] >= 2 {
            return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity { row: c as u16 });
        }
        consumers[c] += 1;
        i += 1;
    }
    Ok((producers, consumers))
}
pub fn build_pool_v1_pair_forest_copy_row_schedule_v1(
) -> Result<Schedule, PoolV1PairHidingLayoutErrorV1> {
    let legacy = build_pool_v1_pair_copy_row_schedule_v1()?;
    let mut links = Schedule::new();
    let mut i = 0usize;
    while i < legacy.len {
        let scheduled = schedule_at(&legacy, i);
        if !path_kind(scheduled.kind) {
            links.push(scheduled);
        }
        i += 1;
    }
    // The existing schedule's auxiliary endpoints live in rows 864..975.
    // Move that complete seven-block region forward by three blocks while
    // leaving every existing Poseidon endpoint unchanged.
    let mut si = 0usize;
    while si < links.len {
        let mut scheduled = schedule_at(&links, si);
        if usize::from(scheduled.producer_row) >= 54 * POOL_V1_PAIR_TRACE_BLOCK_ROWS {
            scheduled.producer_row += 3 * POOL_V1_PAIR_TRACE_BLOCK_ROWS as u16;
        }
        if usize::from(scheduled.consumer_row) >= 54 * POOL_V1_PAIR_TRACE_BLOCK_ROWS {
            scheduled.consumer_row += 3 * POOL_V1_PAIR_TRACE_BLOCK_ROWS as u16;
        }
        links.data[si] = scheduled;
        si += 1;
    }

    links = append_forest_level(links, 0)?;
    links = append_forest_level(links, 1)?;
    links = append_forest_level(links, 2)?;
    links = append_forest_level(links, 3)?;
    links = append_forest_level(links, 4)?;
    links = append_forest_level(links, 5)?;
    links = append_forest_level(links, 6)?;
    links = append_forest_level(links, 7)?;
    links = append_forest_level(links, 8)?;
    links = append_forest_level(links, 9)?;
    links = append_forest_level(links, 10)?;
    links = append_forest_level(links, 11)?;
    links = append_forest_level(links, 12)?;
    links = append_forest_level(links, 13)?;
    links = append_forest_level(links, 14)?;
    links = append_forest_level(links, 15)?;
    links = append_forest_level(links, 16)?;
    links = append_forest_level(links, 17)?;
    links = append_forest_level(links, 18)?;
    links = append_forest_level(links, 19)?;
    links = append_forest_level(links, 20)?;
    links = append_forest_level(links, 21)?;
    links = append_forest_level(links, 22)?;
    links = append_forest_level(links, 23)?;
    if links.len() != POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1 {
        return Err(PoolV1PairHidingLayoutErrorV1::Shape);
    }
    endpoint_counts(&links.data, links.len)?;
    Ok(links)
}
pub fn pool_v1_pair_forest_copy_active_rows_v1(
) -> Result<([u16; 214], usize), PoolV1PairHidingLayoutErrorV1> {
    let schedule = build_pool_v1_pair_forest_copy_row_schedule_v1()?;
    let mut flags = [false; 1024];
    let mut i = 0usize;
    while i < schedule.len {
        let link = schedule_at(&schedule, i);
        flags[link.producer_row as usize] = true;
        flags[link.consumer_row as usize] = true;
        i += 1;
    }
    let mut rows = [0u16; 214];
    let mut len = 0usize;
    i = 0;
    while i < 1024 {
        if flag_at(&flags, i) {
            rows[len] = i as u16;
            len += 1;
        }
        i += 1;
    }
    Ok((rows, len))
}
const MASK_LINKS: [(u16, u16); 136] = [
    (27, 32),
    (43, 48),
    (411, 416),
    (443, 448),
    (459, 464),
    (491, 496),
    (507, 512),
    (11, 28),
    (12, 412),
    (44, 428),
    (60, 428),
    (44, 1008),
    (460, 1010),
    (508, 1012),
    (1008, 1014),
    (1010, 1014),
    (1012, 1015),
    (1014, 1015),
    (64, 1017),
    (913, 1017),
    (523, 1018),
    (475, 540),
    (523, 540),
    (1018, 528),
    (539, 556),
    (539, 544),
    (555, 572),
    (555, 560),
    (571, 588),
    (571, 576),
    (587, 604),
    (587, 592),
    (603, 620),
    (603, 608),
    (619, 636),
    (619, 624),
    (635, 652),
    (635, 640),
    (651, 668),
    (651, 656),
    (667, 684),
    (667, 672),
    (683, 700),
    (683, 688),
    (699, 716),
    (699, 704),
    (715, 732),
    (715, 720),
    (731, 748),
    (731, 736),
    (747, 764),
    (747, 752),
    (763, 780),
    (763, 768),
    (779, 796),
    (779, 784),
    (795, 812),
    (795, 800),
    (811, 828),
    (811, 816),
    (827, 844),
    (827, 832),
    (843, 860),
    (843, 848),
    (59, 913),
    (914, 76),
    (914, 64),
    (75, 917),
    (918, 92),
    (918, 80),
    (91, 921),
    (922, 108),
    (922, 96),
    (107, 925),
    (926, 124),
    (926, 112),
    (123, 929),
    (930, 140),
    (930, 128),
    (139, 933),
    (934, 156),
    (934, 144),
    (155, 937),
    (938, 172),
    (938, 160),
    (171, 941),
    (942, 188),
    (942, 176),
    (187, 945),
    (946, 204),
    (946, 192),
    (203, 949),
    (950, 220),
    (950, 208),
    (219, 953),
    (954, 236),
    (954, 224),
    (235, 957),
    (958, 252),
    (958, 240),
    (251, 961),
    (962, 268),
    (962, 256),
    (267, 965),
    (966, 284),
    (966, 272),
    (283, 969),
    (970, 300),
    (970, 288),
    (299, 973),
    (974, 316),
    (974, 304),
    (315, 977),
    (978, 332),
    (978, 320),
    (331, 981),
    (982, 348),
    (982, 336),
    (347, 985),
    (986, 364),
    (986, 352),
    (363, 989),
    (990, 380),
    (990, 368),
    (379, 993),
    (994, 396),
    (994, 384),
    (395, 997),
    (998, 876),
    (998, 864),
    (875, 1001),
    (1002, 892),
    (1002, 880),
    (891, 1005),
    (1006, 908),
    (1006, 896),
];
#[inline(never)]
fn mask_endpoint_bump(n: u8) -> Option<u8> {
    if n >= 2 {
        None
    } else {
        Some(n + 1)
    }
}
pub fn pool_v1_pair_forest_copy_active_row_masks_v1(
) -> Result<[u16; 64], PoolV1PairHidingLayoutErrorV1> {
    let mut producers = [0u8; 1024];
    let mut consumers = [0u8; 1024];
    let mut masks = [0u16; 64];
    let mut i = 0usize;
    while i < 136 {
        let (a, b) = MASK_LINKS[i];
        let p = a as usize;
        let c = b as usize;
        if p >= 1024 {
            return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity { row: a });
        }
        producers[p] = match mask_endpoint_bump(producers[p]) {
            Some(n) => n,
            None => return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity { row: a }),
        };
        if c >= 1024 {
            return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity { row: b });
        }
        consumers[c] = match mask_endpoint_bump(consumers[c]) {
            Some(n) => n,
            None => return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity { row: b }),
        };
        masks[p >> 4u32] |= 1u16 << ((p & 15) as u32);
        masks[c >> 4u32] |= 1u16 << ((c & 15) as u32);
        i += 1;
    }
    Ok(masks)
}

pub fn pool_v1_pair_forest_copy_inactive_row_masks_v1(
) -> Result<[u16; 64], PoolV1PairHidingLayoutErrorV1> {
    let mut masks = pool_v1_pair_forest_copy_active_row_masks_v1()?;
    let mut i = 0usize;
    while i < 64 {
        masks[i] = !masks[i];
        i += 1;
    }
    Ok(masks)
}
fn bank_for_row(row: usize) -> PoolV1PairTraceBankV1 {
    if (544..864).contains(&row) {
        PoolV1PairTraceBankV1::Late
    } else {
        PoolV1PairTraceBankV1::Stable
    }
}

fn tuple_cells(row: usize, start: usize, count: usize, tweak_right: bool) -> PoolV1PairCopyTupleV1 {
    let bank = bank_for_row(row);
    let mut limbs = [PoolV1PairTupleLimbV1::Zero; 16];
    let mut lane = 0usize;
    while lane < count {
        let column = start + lane;
        let offset = if tweak_right && lane + 1 == count {
            M31::ZERO.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK)
        } else {
            M31::ZERO
        };
        limbs[lane] = PoolV1PairTupleLimbV1::Cell {
            source: PoolV1PairTraceCellV1 {
                bank,
                cell: TraceCell {
                    row: row as u16,
                    column: column as u8,
                },
            },
            offset,
        };
        lane += 1;
    }
    PoolV1PairCopyTupleV1 {
        row: row as u16,
        limbs,
    }
}

fn aux_tuple(row: usize, start: usize, count: usize) -> PoolV1PairCopyTupleV1 {
    tuple_cells(row, start, count, false)
}
pub fn build_pool_v1_pair_copy_registry_v1() -> Result<Registry, PoolV1PairTraceErrorV1> {
    let rows = match build_pool_v1_pair_copy_row_schedule_v1() {
        Ok(rows) => rows,
        Err(_) => return Err(PoolV1PairTraceErrorV1::CopyLayout),
    };
    let mut output = Registry::new();
    let mut ri = 0usize;
    while ri < rows.len {
        let scheduled = schedule_at(&rows, ri);
        let (producer, consumer, weight) = match scheduled.kind {
            PoolV1PairCopyRowLinkKindV1::SpongeCarry { from, .. } => (
                tuple_cells(scheduled.producer_row as usize, 0, 16, false),
                tuple_cells(scheduled.consumer_row as usize, 0, 16, false),
                if from == 27 || from == 28 {
                    PoolV1PairCopyWeightV1::PrivateTransferOnly
                } else {
                    PoolV1PairCopyWeightV1::One
                },
            ),
            PoolV1PairCopyRowLinkKindV1::OwnerOutput => (
                tuple_cells(11, 0, 8, false),
                tuple_cells(28, 0, 8, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::NullifierKey => (
                tuple_cells(12, 0, 8, false),
                tuple_cells(412, 0, 8, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::InputSaltHead => (
                tuple_cells(44, 2, 6, false),
                tuple_cells(428, 0, 6, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::InputSaltTail => (
                tuple_cells(60, 0, 2, false),
                tuple_cells(428, 6, 2, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. } => (
                tuple_cells(scheduled.producer_row as usize, 0, 8, false),
                aux_tuple(scheduled.consumer_row as usize, 1, 8),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. } => (
                aux_tuple(scheduled.producer_row as usize, 0, 8),
                tuple_cells(scheduled.consumer_row as usize, 0, 8, false),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. } => (
                aux_tuple(scheduled.producer_row as usize, 8, 8),
                tuple_cells(scheduled.consumer_row as usize, 8, 8, true),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::ValueSource { value } => (
                tuple_cells(scheduled.producer_row as usize, 0, 1, false),
                aux_tuple(scheduled.consumer_row as usize, 10, 1),
                if value == 1 {
                    PoolV1PairCopyWeightV1::PrivateTransferOnly
                } else {
                    PoolV1PairCopyWeightV1::One
                },
            ),
            PoolV1PairCopyRowLinkKindV1::ConservationInput => (
                aux_tuple(960, 10, 1),
                aux_tuple(966, 0, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::ConservationRecipient => (
                aux_tuple(962, 10, 1),
                aux_tuple(966, 1, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::ConservationChange => (
                aux_tuple(964, 10, 1),
                aux_tuple(967, 1, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::ConservationPartial => (
                aux_tuple(966, 2, 1),
                aux_tuple(967, 0, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::InputSecondCommitment => (
                tuple_cells(64, 8, 8, true),
                aux_tuple(969, 2, 8),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::InputSelectedSide => (
                aux_tuple(scheduled.producer_row as usize, 0, 1),
                aux_tuple(969, 10, 1),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::OutputSecondCommitment => (
                tuple_cells(523, 0, 8, false),
                aux_tuple(970, 2, 8),
                PoolV1PairCopyWeightV1::PrivateTransferOnly,
            ),
            PoolV1PairCopyRowLinkKindV1::OutputPairFirst => (
                tuple_cells(475, 0, 8, false),
                tuple_cells(540, 0, 8, false),
                PoolV1PairCopyWeightV1::PrivateTransferOnly,
            ),
            PoolV1PairCopyRowLinkKindV1::OutputPairFirstWithdrawal => (
                tuple_cells(523, 0, 8, false),
                tuple_cells(540, 0, 8, false),
                PoolV1PairCopyWeightV1::WithdrawalOnly,
            ),
            PoolV1PairCopyRowLinkKindV1::OutputPairSecond => (
                aux_tuple(970, 2, 8),
                tuple_cells(528, 8, 8, true),
                PoolV1PairCopyWeightV1::One,
            ),
            PoolV1PairCopyRowLinkKindV1::AppendCurrentLeft { level } => (
                tuple_cells(scheduled.producer_row as usize, 0, 8, false),
                tuple_cells(scheduled.consumer_row as usize, 0, 8, false),
                PoolV1PairCopyWeightV1::AppendCurrentLeft { level },
            ),
            PoolV1PairCopyRowLinkKindV1::AppendCurrentRight { level } => (
                tuple_cells(scheduled.producer_row as usize, 0, 8, false),
                tuple_cells(scheduled.consumer_row as usize, 8, 8, true),
                PoolV1PairCopyWeightV1::AppendCurrentRight { level },
            ),
        };
        let id = output.len() as u16;
        output.push(PoolV1PairCopyLinkV1 {
            id,
            tag: M31(POOL_V1_PAIR_COPY_TAG_BASE_V1 + u32::from(id)),
            kind: scheduled.kind,
            weight,
            producer,
            consumer,
        });
        ri += 1;
    }
    if output.len() != POOL_V1_PAIR_COPY_ROW_LINKS_V1 {
        return Err(PoolV1PairTraceErrorV1::CopyLayout);
    }
    Ok(output)
}
fn translate_aux_tuple(mut tuple: PoolV1PairCopyTupleV1) -> PoolV1PairCopyTupleV1 {
    if usize::from(tuple.row) >= 864 {
        tuple.row += 48;
    }
    let mut i = 0usize;
    while i < 16 {
        if let PoolV1PairTupleLimbV1::Cell { mut source, offset } = tuple.limbs[i] {
            if source.cell.row >= 864 {
                source.cell.row += 48;
            }
            tuple.limbs[i] = PoolV1PairTupleLimbV1::Cell { source, offset };
        }
        i += 1;
    }
    tuple
}

fn path_kind(kind: PoolV1PairCopyRowLinkKindV1) -> bool {
    matches!(
        kind,
        PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. }
            | PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. }
            | PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. }
    )
}
pub fn build_pool_v1_pair_forest_copy_registry_v1() -> Result<Registry, PoolV1PairTraceErrorV1> {
    let legacy = build_pool_v1_pair_copy_registry_v1()?;
    let schedule = match build_pool_v1_pair_forest_copy_row_schedule_v1() {
        Ok(schedule) => schedule,
        Err(_) => return Err(PoolV1PairTraceErrorV1::CopyLayout),
    };
    let mut output = Registry::new();
    let mut si = 0usize;
    while si < schedule.len {
        let scheduled = schedule_at(&schedule, si);
        let (producer, consumer, weight) = if path_kind(scheduled.kind) {
            match scheduled.kind {
                PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. } => (
                    tuple_cells(usize::from(scheduled.producer_row), 0, 8, false),
                    tuple_cells(usize::from(scheduled.consumer_row), 1, 8, false),
                    PoolV1PairCopyWeightV1::One,
                ),
                PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. } => (
                    tuple_cells(usize::from(scheduled.producer_row), 0, 8, false),
                    tuple_cells(usize::from(scheduled.consumer_row), 0, 8, false),
                    PoolV1PairCopyWeightV1::One,
                ),
                PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. } => (
                    tuple_cells(usize::from(scheduled.producer_row), 8, 8, false),
                    tuple_cells(usize::from(scheduled.consumer_row), 8, 8, true),
                    PoolV1PairCopyWeightV1::One,
                ),
                _ => return Err(PoolV1PairTraceErrorV1::CopyLayout),
            }
        } else {
            let mut found = None;
            let mut i = 0usize;
            while i < legacy.len && found.is_none() {
                if registry_at(&legacy, i).kind == scheduled.kind {
                    found = Some(registry_at(&legacy, i));
                }
                i += 1;
            }
            let old = match found {
                Some(value) => value,
                None => return Err(PoolV1PairTraceErrorV1::CopyLayout),
            };
            (
                translate_aux_tuple(old.producer),
                translate_aux_tuple(old.consumer),
                old.weight,
            )
        };
        if producer.row != scheduled.producer_row || consumer.row != scheduled.consumer_row {
            return Err(PoolV1PairTraceErrorV1::CopyLayout);
        }
        let id = output.len() as u16;
        output.push(PoolV1PairCopyLinkV1 {
            id,
            tag: M31(POOL_V1_PAIR_COPY_TAG_BASE_V1 + u32::from(id)),
            kind: scheduled.kind,
            weight,
            producer,
            consumer,
        });
        si += 1;
    }
    if output.len() != POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1 {
        return Err(PoolV1PairTraceErrorV1::CopyLayout);
    }
    Ok(output)
}
fn tuple_value(trace: &PoolV1PairForestTraceV1, tuple: PoolV1PairCopyTupleV1) -> [M31; 16] {
    let mut out = [M31::ZERO; 16];
    let mut i = 0usize;
    while i < 16 {
        out[i] = match tuple.limbs[i] {
            PoolV1PairTupleLimbV1::Zero => M31::ZERO,
            PoolV1PairTupleLimbV1::Cell { source, offset } => {
                let value = match source.bank {
                    PoolV1PairTraceBankV1::Stable => trace.stable.c1[source.cell.column as usize][source.cell.row as usize],
                    PoolV1PairTraceBankV1::Late => trace.late[source.cell.column as usize][source.cell.row as usize],
                };
                value.add(offset)
            }
        };
        i += 1;
    }
    out
}
fn compress_tuple(tag: M31, values: &[M31; 16], lambda: QM31) -> QM31 {
    let mut value = QM31::from_cm31(aspis_core::field::CM31::from_m31(tag));
    let mut power = lambda;
    let mut i = 0usize;
    while i < 16 {
        value = value.add(power.mul_m31(values[i]));
        power = power.mul(lambda);
        i += 1;
    }
    value
}

fn copy_weight(
    weight: PoolV1PairCopyWeightV1,
    append_index: u64,
    variant: PoolV1PairTraceVariantV1,
) -> M31 {
    match weight {
        PoolV1PairCopyWeightV1::One => M31::ONE,
        PoolV1PairCopyWeightV1::PrivateTransferOnly => M31(u32::from(
            variant == PoolV1PairTraceVariantV1::PrivateTransfer,
        )),
        PoolV1PairCopyWeightV1::WithdrawalOnly => {
            M31(u32::from(variant == PoolV1PairTraceVariantV1::Withdrawal))
        }
        PoolV1PairCopyWeightV1::AppendCurrentLeft { level } => {
            M31(1 - ((append_index >> level) & 1) as u32)
        }
        PoolV1PairCopyWeightV1::AppendCurrentRight { level } => {
            M31(((append_index >> level) & 1) as u32)
        }
    }
}

pub fn pool_v1_pair_forest_copy_rows_v1(
    trace: &PoolV1PairForestTraceV1,
    append_index: u64,
    lambda: QM31,
) -> Result<[CopyLogUpRow; 1024], PoolV1PairTraceErrorV1> {
    let empty = CopyLogUpRow {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [M31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [M31::ZERO; 2],
    };
    let mut rows = [empty; 1024];
    let registry = build_pool_v1_pair_forest_copy_registry_v1()?;
    let mut i = 0usize;
    while i < registry.len {
        let link = registry_at(&registry, i);
        let weight = copy_weight(link.weight, append_index, trace.variant);
        let mut side = 0usize;
        while side < 2 {
            let tuple = if side == 0 {
                link.producer
            } else {
                link.consumer
            };
            let row_index = tuple.row as usize;
            let mut row = rows[row_index];
            let mut weights = if side == 0 { row.producer_weights } else { row.consumer_weights };
            let mut values = if side == 0 { row.producer_values } else { row.consumer_values };
            let slot = if weights[0] == M31::ZERO {
                0
            } else if weights[1] == M31::ZERO {
                1
            } else {
                return Err(PoolV1PairTraceErrorV1::CopyLayout);
            };
            values[slot] = compress_tuple(link.tag, &tuple_value(trace, tuple), lambda);
            weights[slot] = weight;
            if side == 0 {
                row.producer_values = values;
                row.producer_weights = weights;
            } else {
                row.consumer_values = values;
                row.consumer_weights = weights;
            }
            rows[row_index] = row;
            side += 1;
        }
        i += 1;
    }
    Ok(rows)
}

pub fn build_pool_v1_pair_forest_copy_helper_v1(
    trace: &PoolV1PairForestTraceV1,
    append_index: u64,
    lambda: QM31,
    chi: QM31,
) -> Result<[QM31; 1024], PoolV1PairTraceErrorV1> {
    let rows = pool_v1_pair_forest_copy_rows_v1(trace, append_index, lambda)?;
    let mut helper = [QM31::ZERO; 1024];
    let mut r = 0usize;
    while r < 1024 {
        let row = rows[r];
        let mut value = QM31::ZERO;
        let mut slot = 0usize;
        while slot < 2 {
            let weight = row.producer_weights[slot];
            if weight != M31::ZERO {
                let inv = match chi.sub(row.producer_values[slot]).try_inv() {
                    Some(v) => v,
                    None => return Err(PoolV1PairTraceErrorV1::CopyImbalance),
                };
                value = value.add(inv.mul_m31(weight));
            }
            slot += 1;
        }
        slot = 0;
        while slot < 2 {
            let weight = row.consumer_weights[slot];
            if weight != M31::ZERO {
                let inv = match chi.sub(row.consumer_values[slot]).try_inv() {
                    Some(v) => v,
                    None => return Err(PoolV1PairTraceErrorV1::CopyImbalance),
                };
                value = value.sub(inv.mul_m31(weight));
            }
            slot += 1;
        }
        helper[r] = value;
        r += 1;
    }
    Ok(helper)
}
pub fn materialize_copy_helper(
    trace: &PoolV1PairForestTraceV1,
    append_index: u64,
    lambda: QM31,
    chi: QM31,
) -> Result<Vec<QM31>, PoolV1PairTraceErrorV1> {
    let helper = build_pool_v1_pair_forest_copy_helper_v1(trace, append_index, lambda, chi)?;
    Ok(helper.to_vec())
}

fn forest_path_aux_cell_is_used(row: usize, column: usize) -> bool {
    let mut level = 0usize;
    while level < POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
        let Some(base) = pool_v1_pair_forest_path_base_row_v1(level) else {
            return false;
        };
        if (row == base && column <= 8) || row == base + 1 {
            return true;
        }
        level += 1;
    }
    false
}

#[inline]
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
) -> Result<([TraceCell; 3803], usize), PoolV1PairHidingLayoutErrorV1> {
    let _ = build_pool_v1_pair_forest_copy_row_schedule_v1()?;
    let mut cells = [TraceCell { row: 0, column: 0 }; 3803];
    let mut len = 0usize;
    let mut column = 0usize;
    while column < POOL_V1_PAIR_TRACE_COLUMNS {
        let mut row = 0usize;
        while row < POOL_V1_PAIR_TRACE_ROWS {
            let poseidon = forest_poseidon_row(row);
            let padding = poseidon
                && row % POOL_V1_PAIR_TRACE_BLOCK_ROWS
                    >= POOL_V1_PAIR_RELATION_FREE_PADDING_LOCAL_ROW_START_V1;
            let auxiliary = !poseidon && !forest_aux_cell_is_used(row, column);
            if padding || auxiliary {
                cells[len] = TraceCell {
                    row: row as u16,
                    column: column as u8,
                };
                len += 1;
            }
            row += 1;
        }
        column += 1;
    }
    Ok((cells, len))
}

/// Allocation adapters retain the existing host caller interfaces. They are
/// outside the Drop-free extraction roots and preserve logical element order.
pub fn materialize_active_rows() -> Result<Vec<u16>, PoolV1PairHidingLayoutErrorV1> {
    let (rows, len) = pool_v1_pair_forest_copy_active_rows_v1()?;
    Ok(rows[..len].to_vec())
}
pub fn materialize_mask_cells() -> Result<Vec<TraceCell>, PoolV1PairHidingLayoutErrorV1> {
    let (cells, len) = pool_v1_pair_forest_relation_free_mask_cells_v1()?;
    Ok(cells[..len].to_vec())
}

// Owned read boundaries keep array-element loans out of caller loop joins.
#[inline(never)]
fn schedule_at(schedule: &Schedule, i: usize) -> PoolV1PairCopyRowLinkV1 {
    schedule.data[i]
}
#[inline(never)]
fn registry_at(registry: &Registry, i: usize) -> PoolV1PairCopyLinkV1 {
    registry.data[i]
}

#[inline(never)]
fn flag_at(flags: &[bool; 1024], i: usize) -> bool { flags[i] }

#[inline(never)]
fn append_forest_level(mut links: Schedule, level: usize) -> Result<Schedule, PoolV1PairHidingLayoutErrorV1> {
    let auxiliary = pool_v1_pair_forest_path_base_row_v1(level)
        .ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?;
    let target_block = pool_v1_pair_forest_membership_hash_block_v1(level)
        .ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?;
    let previous_block = if level == 0 {
        3
    } else {
        pool_v1_pair_forest_membership_hash_block_v1(level - 1)
        .ok_or(PoolV1PairHidingLayoutErrorV1::Shape)?
    };
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { level: level as u8 },
        previous_block * POOL_V1_PAIR_TRACE_BLOCK_ROWS + 11,
        auxiliary,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { level: level as u8 },
        auxiliary + 1,
        target_block * POOL_V1_PAIR_TRACE_BLOCK_ROWS + 12,
    ));
    links.push(link(
        PoolV1PairCopyRowLinkKindV1::PrivatePathRight { level: level as u8 },
        auxiliary + 1,
        target_block * POOL_V1_PAIR_TRACE_BLOCK_ROWS,
    ));
    Ok(links)
}
