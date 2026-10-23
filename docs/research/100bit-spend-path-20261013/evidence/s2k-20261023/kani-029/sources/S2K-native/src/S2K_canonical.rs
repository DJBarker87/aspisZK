pub(crate) fn digest_is_canonical(value: &Digest) -> bool {
    let mut i = 0;
    while i < value.len() {
        if value[i].0 >= P {
            return false;
        }
        i += 1;
    }
    true
}
