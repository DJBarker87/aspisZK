#[inline]
fn digest_is_canonical(digest: &Digest) -> bool {
    digest[0].0 < P
        && digest[1].0 < P
        && digest[2].0 < P
        && digest[3].0 < P
        && digest[4].0 < P
        && digest[5].0 < P
        && digest[6].0 < P
        && digest[7].0 < P
}