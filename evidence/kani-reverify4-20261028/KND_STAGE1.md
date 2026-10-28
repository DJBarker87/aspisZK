# Fixed profile schedule

KND_Schedule.lean compiles in KND_L001 (exit 0). `exact_schedule`, `data_independent`, `append_count`, `final_length`, and `no_growth` are audited in the receipt. The source-order model transcribes frozen verifier.rs:326–340; KND_writer.txt retains the excerpt. The machine-readable ordered schedule has 116 entries, every capacity 1768, final length 1768. Scalar weights begin at 712 and end at 1736; checksum appends 32.

Scope: this is a manually transcribed value/metadata model, not an extracted Rust execution equivalence proof. It assumes the 64-weight profile. The public checkpoint function itself accepts arbitrary weights lengths and other variants. These preconditions must not be silently generalized. No runtime or heap credit is awarded here.

116 distinct triples require 232 Kani runs with controls, exceeding the authorized 90. The actual writer preallocates 1768; array1736→3472 from earlier cut harnesses is a different constructor. The original arbitrary-length rows cannot be reconstructed universally from only reachable writer lengths. Both remaining obligations stay explicit.
