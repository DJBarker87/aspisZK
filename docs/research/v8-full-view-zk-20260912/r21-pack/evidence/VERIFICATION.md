# Local verification

Compiled and executed with g++ -O2 -std=c++17, assertions enabled,
-fsanitize=undefined -fno-sanitize-recover=all.

The transport/control executable uses full QM31 inputs and checks 1024
coordinate-basis inverse/dual identities, 89 exact balanced-pad images, and
128 arbitrary permutation-correction pairings. The generator reconstructs
both signed matrices exactly over integers, certifying correction ranks by
cycle decomposition (153 versus 89).

Preliminary compatible-image screens: seeds 1 and 2 over M31 and separately
seeds 1 and 2 over QM31. All give H1=540 and G=601 in the RETAINED R18-style
screening model. This is NOT the full R19 626-row source map (whose reported
rank is 602), NOT actual q22 schedules, and NOT a witness-affine solve.

`run_checks.py --ranks` was executed after packaging-source assembly and
all these checks passed. Source-independent arithmetic model provenance is
recorded in SHORT_CYCLES.md. No Rust or Lean toolchain is installed here.
No SBF CU test was run, no actual stage ORDER file was locally supplied,
and no helper proof was implemented. Its performance and security remain
research targets. R20 CU evidence is explicitly source-reported.
