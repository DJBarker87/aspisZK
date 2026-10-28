// Generated verbatim source cut; see control-cut-sources.json.
pub const POOL_V1_PAIR_PATH_AUX_BLOCKS: usize = 6;

pub const POOL_V1_PAIR_PATH_AUX_ROW_END: usize =
    POOL_V1_PAIR_PATH_AUX_ROW_START + POOL_V1_PAIR_PATH_AUX_BLOCKS * POOL_V1_PAIR_TRACE_BLOCK_ROWS;

pub const POOL_V1_PAIR_VALUE_AUX_ROW_START: usize = POOL_V1_PAIR_PATH_AUX_ROW_END;

pub const POOL_V1_PAIR_TRACE_BLOCK_ROWS: usize = 16;

pub const POOL_V1_PAIR_STABLE_POSEIDON_BLOCKS: usize = 34;

pub const POOL_V1_PAIR_PRIVATE_DIRECTIONS: usize = 21;

pub const POOL_V1_PAIR_LATE_APPEND_POSEIDON_BLOCKS: usize = 20;

pub const POOL_V1_PAIR_POSEIDON_BLOCKS: usize =
    POOL_V1_PAIR_STABLE_POSEIDON_BLOCKS + POOL_V1_PAIR_LATE_APPEND_POSEIDON_BLOCKS;

pub const POOL_V1_PAIR_POSEIDON_ROW_END: usize =
    POOL_V1_PAIR_POSEIDON_BLOCKS * POOL_V1_PAIR_TRACE_BLOCK_ROWS;

pub const POOL_V1_PAIR_PATH_LOCAL_ROW_OFFSET: usize = 1;

pub const POOL_V1_PAIR_PATH_AUX_ROW_START: usize = POOL_V1_PAIR_POSEIDON_ROW_END;

pub const POOL_V1_PAIR_OUTPUT_OCCUPANCY_AUX_ROW: usize = POOL_V1_PAIR_VALUE_AUX_ROW_START + 10;

pub const POOL_V1_PAIR_INPUT_OCCUPANCY_AUX_ROW: usize = POOL_V1_PAIR_VALUE_AUX_ROW_START + 9;

pub const POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1: usize = 24;

const POOL_V1_PAIR_FOREST_PATH_BASE_LOCAL_ROWS_V1: [[usize; 4]; 6] = [
    [1, 5, 9, 13],
    [1, 5, 9, 13],
    [1, 5, 9, 13],
    [1, 5, 9, 13],
    [1, 5, 9, 13],
    [1, 5, 9, 13],
];

pub const POOL_V1_PAIR_FOREST_PATH_AUX_ROW_START_V1: usize = 57 * 16;

pub const POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1: usize = 136;

pub const POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK: usize = 4;

pub const POOL_V1_PAIR_COPY_ROW_LINKS_V1: usize = 127;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairCopyRowLinkKindV1 {
    SpongeCarry {
        from: u8,
        to: u8,
    },
    OwnerOutput,
    NullifierKey,
    InputSaltHead,
    InputSaltTail,
    PrivatePathCurrent {
        level: u8,
    },
    PrivatePathLeft {
        level: u8,
    },
    PrivatePathRight {
        level: u8,
    },
    ValueSource {
        value: u8,
    },
    ConservationInput,
    ConservationRecipient,
    ConservationChange,
    ConservationPartial,
    InputSecondCommitment,
    InputSelectedSide,
    OutputSecondCommitment,
    OutputPairFirst,
    OutputPairFirstWithdrawal,
    OutputPairSecond,
    /// The two links at each level have complementary public weights
    /// `(1-bit, bit)`. Both rows remain in the fixed active-row inventory.
    AppendCurrentLeft {
        level: u8,
    },
    AppendCurrentRight {
        level: u8,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairCopyRowLinkV1 {
    pub kind: PoolV1PairCopyRowLinkKindV1,
    pub producer_row: u16,
    pub consumer_row: u16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairHidingLayoutErrorV1 {
    Shape,
    EndpointCapacity { row: u16 },
}

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

fn path_kind(kind: PoolV1PairCopyRowLinkKindV1) -> bool {
    matches!(
        kind,
        PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. }
            | PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. }
            | PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. }
    )
}

fn schedule_at(schedule: &Schedule, i: usize) -> PoolV1PairCopyRowLinkV1 {
    schedule.data[i]
}

fn flag_at(flags: &[bool; 1024], i: usize) -> bool { flags[i] }

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

pub const fn pool_v1_pair_forest_path_base_row_v1(level: usize) -> Option<usize> {
    if level >= POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
        return None;
    }
    Some(
        POOL_V1_PAIR_FOREST_PATH_AUX_ROW_START_V1
            + (level / POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK) * POOL_V1_PAIR_TRACE_BLOCK_ROWS
            + POOL_V1_PAIR_FOREST_PATH_BASE_LOCAL_ROWS_V1
                [level / POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK]
                [level % POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK],
    )
}

pub const fn pool_v1_pair_forest_membership_hash_block_v1(level: usize) -> Option<usize> {
    if level >= POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1 {
        None
    } else if level <= 20 {
        Some(4 + level)
    } else {
        Some(33 + level)
    }
}

pub const fn pool_v1_pair_path_base_row_v1(level: usize) -> Option<usize> {
    if level >= POOL_V1_PAIR_PRIVATE_DIRECTIONS {
        return None;
    }
    Some(
        POOL_V1_PAIR_PATH_AUX_ROW_START
            + (level / POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK) * POOL_V1_PAIR_TRACE_BLOCK_ROWS
            + POOL_V1_PAIR_PATH_LOCAL_ROW_OFFSET
            + 2 * (level % POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK),
    )
}
