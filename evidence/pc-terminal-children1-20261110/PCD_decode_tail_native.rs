    fn PCD_error_PoolV1TreeError()->aspis_statement::pool_v1::PoolV1TreeError {
        match kani::any::<u8>() % 13 {
            0=>aspis_statement::pool_v1::PoolV1TreeError::TreeFull,
            1=>aspis_statement::pool_v1::PoolV1TreeError::InsufficientCapacity,
            2=>aspis_statement::pool_v1::PoolV1TreeError::IndexOutOfRange,
            3=>aspis_statement::pool_v1::PoolV1TreeError::RootMismatch,
            4=>aspis_statement::pool_v1::PoolV1TreeError::NonCanonicalFrontier,
            5=>aspis_statement::pool_v1::PoolV1TreeError::WrongLength,
            6=>aspis_statement::pool_v1::PoolV1TreeError::WrongMagic,
            7=>aspis_statement::pool_v1::PoolV1TreeError::WrongVersion,
            8=>aspis_statement::pool_v1::PoolV1TreeError::WrongDepth,
            9=>aspis_statement::pool_v1::PoolV1TreeError::WrongTreeHash,
            10=>aspis_statement::pool_v1::PoolV1TreeError::WrongDigestEncoding,
            11=>aspis_statement::pool_v1::PoolV1TreeError::NonCanonicalDigest,
            _=>aspis_statement::pool_v1::PoolV1TreeError::NonZeroReserved,
        }
    }
    fn PCD_error_PoolV1PairForestAccountErrorV1()->aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1 {
        match kani::any::<u8>() % 21 {
            0=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::WrongLength,
            1=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::WrongMagic,
            2=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::WrongVersion,
            3=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::WrongLaneCount,
            4=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::WrongDigestEncoding,
            5=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::WrongDepth,
            6=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::WrongFormatBinding,
            7=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::NonZeroReserved,
            8=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::ZeroRequiredBinding,
            9=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::InvalidBoolean,
            10=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::InvalidMasterState,
            11=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::InvalidLane,
            12=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::LaneMasterMismatch,
            13=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::LaneOrderMismatch,
            14=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::LaneSequenceDecreased,
            15=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::DuplicateCheckpoint,
            16=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::CheckpointSequenceOverflow,
            17=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::NonCanonicalDigest,
            18=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::Identity,
            19=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::Policy,
            _=>aspis_statement::pool_v1::PoolV1PairForestAccountErrorV1::Tree(PCD_error_PoolV1TreeError()),
        }
    }
    fn PCD_error_PoolV1PaymentStatementFormatError()->aspis_statement::pool_v1::PoolV1PaymentStatementFormatError {
        match kani::any::<u8>() % 14 {
            0=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::WrongLength,
            1=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::WrongMagic,
            2=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::WrongVersion,
            3=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::WrongTransitionKind,
            4=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::WrongDigestEncoding,
            5=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::NonZeroReserved,
            6=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::ZeroRequiredBinding,
            7=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::InvalidAnchorSequence,
            8=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::NonCanonicalDigest,
            9=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::NonCanonicalAssetId,
            10=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::InvalidWithdrawalAmount,
            11=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::InvalidDestination,
            12=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::InvalidEnvelope,
            _=>aspis_statement::pool_v1::PoolV1PaymentStatementFormatError::EnvelopeMismatch,
        }
    }
    fn PCD_error_PoolV1PairLiveSnapshotErrorV1()->aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1 {
        match kani::any::<u8>() % 9 {
            0=>aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1::WrongLength,
            1=>aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1::WrongMagic,
            2=>aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1::WrongVersion,
            3=>aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1::WrongFormatBinding,
            4=>aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1::NonZeroReserved,
            5=>aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1::ZeroRequiredBinding,
            6=>aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1::SequenceIndexMismatch,
            7=>aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1::TreeFull,
            _=>aspis_statement::pool_v1::PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest,
        }
    }
    fn PCD_error_PoolV1PairVerifierTransportErrorV1()->aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1 {
        match kani::any::<u8>() % 15 {
            0=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::WrongLength,
            1=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::WrongMagic,
            2=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::WrongVersion,
            3=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::WrongStatementVersion,
            4=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::WrongDigestEncoding,
            5=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::InvalidTransitionKind,
            6=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::WrongSuccessCode,
            7=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::WrongPairFormat,
            8=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::ZeroRequiredBinding,
            9=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::InvalidProofBodyLength,
            10=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::InvalidStatementPayloadLength,
            11=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::InvalidLiveSnapshotPayloadLength,
            12=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::NonCanonicalOutputPair,
            13=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::InvalidAfterstateIndex,
            _=>aspis_statement::pool_v1::PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate,
        }
    }
    fn PCD_error_PoolV1PairLatePublicStatementErrorV1()->aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1 {
        match kani::any::<u8>() % 12 {
            0=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::WrongLength,
            1=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::WrongMagic,
            2=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::WrongVersion,
            3=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::WrongItemCount,
            4=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::WrongHeaderLength,
            5=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::WrongSnapshotLength,
            6=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::WrongAfterstateLength,
            7=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::WrongTotalLength,
            8=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::NonZeroReserved,
            9=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::Snapshot(PCD_error_PoolV1PairLiveSnapshotErrorV1()),
            10=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::Afterstate(PCD_error_PoolV1PairVerifierTransportErrorV1()),
            _=>aspis_statement::pool_v1::PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch,
        }
    }
    fn PCD_error_PoolV1PairForestTerminalFormatErrorV1()->aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1 {
        match kani::any::<u8>() % 22 {
            0=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::WrongLength,
            1=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::WrongMagic,
            2=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::WrongVersion,
            3=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding,
            4=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind,
            5=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::InvalidOutputLane,
            6=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding,
            7=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::NonCanonicalDigest,
            8=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch,
            9=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::MasterBindingMismatch,
            10=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::DeploymentBindingMismatch,
            11=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::HistoricalAnchorMismatch,
            12=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::CheckpointBindingMismatch,
            13=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::SelectedLaneBindingMismatch,
            14=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::LiveSnapshotMismatch,
            15=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::CandidateAfterstateMismatch,
            16=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::ResultBindingMismatch,
            17=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::WithdrawalDestinationMismatch,
            18=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::Payment(PCD_error_PoolV1PaymentStatementFormatError()),
            19=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::LaneTransition(PCD_error_PoolV1PairLatePublicStatementErrorV1()),
            20=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::Afterstate(PCD_error_PoolV1PairVerifierTransportErrorV1()),
            _=>aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1::Account(PCD_error_PoolV1PairForestAccountErrorV1()),
        }
    }
    fn PCD_decoded_request()->Result<PoolV1PairForestTerminalRequestV1,aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1> {
        if kani::any() {Ok(PCD_request_value())} else {Err(PCD_error_PoolV1PairForestTerminalFormatErrorV1())}
    }
    #[kani::requires(tag<14&&i<8&&j<32)]
    #[kani::ensures(|out| match reply {
        Err(_)=>matches!(out,Err(ProgramError::InvalidInstructionData)),
        Ok(_)=>out.is_ok(),
    })]
    #[kani::modifies()]
    fn PCD_decode_tail_segment(reply:Result<PoolV1PairForestTerminalRequestV1,aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1>,tag:u8,i:usize,j:usize)->Result<Box<PoolV1PairForestTerminalRequestV1>,ProgramError> {
        Ok(Box::new(
            reply.map_err(|_|ProgramError::InvalidInstructionData)?,
        ))
    }
    #[kani::proof_for_contract(PCD_decode_tail_segment)]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_decode_tail_contract() {
        let reply=PCD_decoded_request();let tag:u8=kani::any();let i:usize=kani::any();let j:usize=kani::any();
        kani::assume(tag<14&&i<8&&j<32);let out=PCD_decode_tail_segment(reply,tag,i,j);
        kani::cover!(out.is_ok());kani::cover!(out.is_err());
    }
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_decode_tail_control() {
        let reply=PCD_decoded_request();let tag:u8=kani::any();let i:usize=kani::any();let j:usize=kani::any();
        kani::assume(tag<14&&i<8&&j<32);
        let out=PCD_decode_tail_segment(reply,tag,i,j);
        let exact=match (reply,out) {(Err(_),Err(ProgramError::InvalidInstructionData))=>true,(Ok(_),Ok(_))=>true,_=>false};
        assert!(!exact);
    }
