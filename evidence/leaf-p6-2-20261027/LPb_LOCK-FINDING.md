# Active harness dependency-lock finding

Final inspection found the standalone Cargo harness used its generated
LPb_crate/Cargo.lock, NOT the immutable dependency checkout's root Cargo.lock.
The direct native source files and the immutable root lock match release4bb3b3f;
that does not pin the active harness graph. The exact active lock is retained
as LPb_Cargo.lock, hashed in LPb_final_dependency_manifest.json.

- cfg-if: frozen ['1.0.4']; active harness ['1.0.5'].
- libc: frozen ['0.2.186']; active harness ['0.2.191'].

The extra lpb-leaf-stages package is the standalone harness itself. No other
package tuple (name,version,source) is new relative to the frozen lock.
The two external-version differences are not silently replaced after the run.
All20 invocations and their outcomes remain evidence for the recorded HOST
harness graph; they are not a frozen-dependency/release-ELF P6 certificate.
No whole leaf was claimed CLOSED before or after this finding. The source-level
helper observations are recorded within this additional explicit limitation.

Next native replay must pin the harness graph to the release dependency
versions (and record the active lock as an input before launch), then obtain
a new Kani allowance. Zero Kani runs remain, so this job cannot perform that
replay. Do not relabel the historical outputs as runs against a corrected lock.
