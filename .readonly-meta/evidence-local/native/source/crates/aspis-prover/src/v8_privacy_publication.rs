//! Fail-closed ownership boundary for the q22 privacy-repair candidate.
//!
//! No production path calls this module and no public constructor can create
//! a full-view review. Raw affine success can never authorize publication.

pub const V8_REPAIR_BODY_CAP: usize = 40_282;
const CANDIDATE_DOMAIN: &[u8] = b"aspis:v8:privacy-repair:candidate:v1";
const BINDING_DOMAIN: &[u8] = b"aspis:v8:privacy-repair:binding:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CandidateBinding {
    pub statement_digest: [u8; 32],
    pub source_profile_digest: [u8; 32],
    pub gate_version_digest: [u8; 32],
    pub mask_nonce: [u8; 32],
    pub schedule_digest: [u8; 32],
}

impl CandidateBinding {
    fn digest(self) -> [u8; 32] {
        crate::host_hashv(&[
            BINDING_DOMAIN,
            &self.statement_digest,
            &self.source_profile_digest,
            &self.gate_version_digest,
            &self.mask_nonce,
            &self.schedule_digest,
        ])
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum PublicationReviewError {
    EmptyBody,
    OversizedBody,
    RawPrecheckRejected,
    CompleteFullViewCoverageUnsupported,
    StaleOrMutatedCandidate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RawAffinePrecheck {
    Pass,
    Reject,
}

pub struct PrivateCandidate {
    body: Vec<u8>,
    binding: CandidateBinding,
    body_digest: [u8; 32],
}

impl PrivateCandidate {
    pub fn from_private_memory(
        body: Vec<u8>,
        binding: CandidateBinding,
    ) -> Result<Self, PublicationReviewError> {
        if body.is_empty() {
            return Err(PublicationReviewError::EmptyBody);
        }
        if body.len() > V8_REPAIR_BODY_CAP {
            return Err(PublicationReviewError::OversizedBody);
        }
        let body_digest = crate::host_hashv(&[CANDIDATE_DOMAIN, &binding.digest(), &body]);
        Ok(Self {
            body,
            binding,
            body_digest,
        })
    }
}

/// Unforgeable outside this module. A future source-linked complete-view
/// checker may receive a private constructor after semantic review.
pub struct FullViewReview {
    binding_digest: [u8; 32],
    body_digest: [u8; 32],
    _private: (),
}

pub struct ApprovedCandidate {
    candidate: PrivateCandidate,
}

/// Current research review is intentionally terminal on unsupported scope.
/// Retrying cannot turn missing mathematical coverage into authorization.
pub fn review_for_publication(
    _candidate: PrivateCandidate,
    raw: RawAffinePrecheck,
) -> Result<ApprovedCandidate, PublicationReviewError> {
    match raw {
        RawAffinePrecheck::Reject => Err(PublicationReviewError::RawPrecheckRejected),
        RawAffinePrecheck::Pass => Err(PublicationReviewError::CompleteFullViewCoverageUnsupported),
    }
}

fn bind_full_view_review(
    candidate: PrivateCandidate,
    review: FullViewReview,
) -> Result<ApprovedCandidate, PublicationReviewError> {
    if review.binding_digest != candidate.binding.digest()
        || review.body_digest != candidate.body_digest
    {
        return Err(PublicationReviewError::StaleOrMutatedCandidate);
    }
    Ok(ApprovedCandidate { candidate })
}

/// The sole byte-emission function consumes the reviewed immutable candidate.
pub fn publish_approved<E>(
    approved: ApprovedCandidate,
    sink: impl FnOnce(&[u8]) -> Result<(), E>,
) -> Result<(), E> {
    sink(&approved.candidate.body)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binding(seed: u8) -> CandidateBinding {
        CandidateBinding {
            statement_digest: [seed; 32],
            source_profile_digest: [seed + 1; 32],
            gate_version_digest: [seed + 2; 32],
            mask_nonce: [seed + 3; 32],
            schedule_digest: [seed + 4; 32],
        }
    }

    fn test_review(candidate: &PrivateCandidate) -> FullViewReview {
        FullViewReview {
            binding_digest: candidate.binding.digest(),
            body_digest: candidate.body_digest,
            _private: (),
        }
    }

    #[test]
    fn raw_pass_and_reject_cannot_authorize() {
        for raw in [RawAffinePrecheck::Pass, RawAffinePrecheck::Reject] {
            let candidate = PrivateCandidate::from_private_memory(vec![1; 32], binding(1)).unwrap();
            assert!(review_for_publication(candidate, raw).is_err());
        }
    }

    #[test]
    fn candidate_shape_and_stale_review_fail_closed() {
        assert!(matches!(
            PrivateCandidate::from_private_memory(vec![], binding(1)),
            Err(PublicationReviewError::EmptyBody)
        ));
        assert!(matches!(
            PrivateCandidate::from_private_memory(vec![0; V8_REPAIR_BODY_CAP + 1], binding(1)),
            Err(PublicationReviewError::OversizedBody)
        ));
        let first = PrivateCandidate::from_private_memory(vec![1; 32], binding(1)).unwrap();
        let review = test_review(&first);
        let second = PrivateCandidate::from_private_memory(vec![2; 32], binding(1)).unwrap();
        assert!(matches!(
            bind_full_view_review(second, review),
            Err(PublicationReviewError::StaleOrMutatedCandidate)
        ));
    }

    #[test]
    fn approved_bytes_have_one_consuming_sink() {
        let candidate = PrivateCandidate::from_private_memory(vec![9; 32], binding(7)).unwrap();
        let review = test_review(&candidate);
        let approved = bind_full_view_review(candidate, review).unwrap();
        let mut observed = Vec::new();
        publish_approved(approved, |bytes| {
            observed.extend_from_slice(bytes);
            Ok::<_, ()>(())
        })
        .unwrap();
        assert_eq!(observed, vec![9; 32]);
    }
}
