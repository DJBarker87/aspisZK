pub fn note_input(owner_key: [u32;8], value: u32, asset_id: u32, salt: [u32;8]) -> [u32;18] {
    [ owner_key[0], owner_key[1], owner_key[2], owner_key[3], owner_key[4], owner_key[5], owner_key[6], owner_key[7], value, asset_id, salt[0], salt[1], salt[2], salt[3], salt[4], salt[5], salt[6], salt[7] ]
}
