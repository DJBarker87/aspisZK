const fn order() -> [u16; MESSAGE_LEN] {
    assert!(PAD_ROWS.len() == PADS);
    let mut out = [0; MESSAGE_LEN];
    let mut used = [false; MESSAGE_LEN];
    let mut j = 0;
    while j < PADS {
        let r = PAD_ROWS[j] as usize;
        assert!(r < PIVOT && r != 1014 && !used[r]);
        out[j] = PAD_ROWS[j];
        used[r] = true;
        j += 1;
    }
    let mut r = 0;
    while r < PIVOT {
        if !used[r] {
            out[j] = r as u16;
            j += 1;
        }
        r += 1;
    }
    assert!(j == PIVOT);
    out[PIVOT] = PIVOT as u16;
    out
}