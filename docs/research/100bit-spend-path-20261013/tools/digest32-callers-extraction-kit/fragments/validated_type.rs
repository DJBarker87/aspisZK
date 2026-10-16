/// A record whose framing and every field limb were checked by
/// `parse_record`. Tokens are issued only from a successfully parsed Prefix;
/// callers cannot supply a row separately from its bytes.
#[derive(Clone, Copy)]
pub(crate) struct ValidatedRecord<'a> {
    row: u8,
    framed: &'a [u8],
}