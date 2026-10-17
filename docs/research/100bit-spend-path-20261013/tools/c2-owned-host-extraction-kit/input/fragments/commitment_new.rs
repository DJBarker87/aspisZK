    pub fn new(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
    ) -> Result<Self, Error> {
        Self::build(hash, domain, time, messages, variant, None)
    }