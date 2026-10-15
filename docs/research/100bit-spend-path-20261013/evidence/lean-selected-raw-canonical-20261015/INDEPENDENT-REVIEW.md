# Independent evidence review

Reviewed the green SelectedRawCanonical target and its bundle without rebuilding.

- All bundle entries pass `SHA256SUMS`.
- The source under test, its final-source snapshot, and the recorded attempt snapshot match at SHA-256 `f84ea3ad25ff6d037eb13b6cb823fdf00cc524073ef6e60292a8d52d1823f458`.
- Both direct-import source copies match the current worktree files. All three object archive members match their manifest SHA-256 values and byte sizes.
- The receipt records target `R1SelectedRawCanonical`, attempt `a`, exit 0, 1.44 s, peak RSS 3,563,168 KiB, zero swap, and cgroup limits 4G/6G/0 with TasksMax 128.
- There are exactly two axiom reports. `dec_sound` reports `[propext]`; `encode_of_decode` reports `[propext, Classical.choice, Quot.sound]`. No `sorryAx` appears.
- `dec_sound` specializes the selected bounded message codec: successful decode implies `enc m = bs`. `encode_of_decode` applies the generic `RawRoundCanonical.encode_of_decode` with that explicit canonicality fact. The result says successful decoding preserves the original raw record list under this selected codec; it makes no source-correspondence or acceptance claim.
