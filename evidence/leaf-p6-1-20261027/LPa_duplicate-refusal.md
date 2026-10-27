A second local orchestration invocation accidentally reused LPa_K001. The
first Kani invocation had completed. The unchanged runner refused the existing
output directory before launching a compiler/prover (FileExistsError); its
launcher log is retained. The original successful receipt is unchanged. No
simultaneous own compiler scope and no second Kani verifier invocation. This
is not new validation, and the ID must never be reused.
