    pub fn new_salted(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        salts: PrivateSalts,
    ) -> Result<Self, Error> {
        Self::build(hash, domain, time, messages, variant, Some(salts))
    }