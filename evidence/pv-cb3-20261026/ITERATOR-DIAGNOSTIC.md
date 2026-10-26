# Iterator frame diagnostic

Kani `kani-iterator-frame-001` failed the final array equality. Concrete playback
`kani-iterator-frame-playback-004` printed a witness with remaining=8.
The exact witness passed optimized native Rust (`rust-iterator-native-witness-001`):
read=Some(16), final=[15016073,1086431253,5242880,750403596,2752530,1178599424,20,2050].
This is a Kani/native discrepancy, not a checked counterexample against shipped Aspis source.
No source was changed to mask the failure. The frame property is not credited as verified.
Playback002/003 were CLI rejections (required feature/single-worker flag);
playback001 was a reservation refusal. All raw receipts are retained.
