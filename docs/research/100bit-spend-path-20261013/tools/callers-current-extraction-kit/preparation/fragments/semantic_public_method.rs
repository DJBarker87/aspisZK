    #[cfg(feature = "r0")]
    #[inline(always)]
    pub fn semantic_public(&self) -> super::pair_forest_semantic_terminal::r0::Public<'_> {
        use super::pair_forest_semantic_terminal::r0::Public;
        match self {
            Self::PrivateTransfer { common, public } => {
                Public::Transfer(public, &common.lane_transition)
            }
            Self::Withdrawal { common, public } => {
                Public::Withdrawal(public, &common.lane_transition)
            }
        }
    }