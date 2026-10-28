35518 failed at import resolution, before elaborating ReserveFacts. Lean resolves
the R1Z directory from the first LEAN_PATH prefix and does not fall through for
a missing module. The wrapper verified the shared object but omitted the local
link needed for this namespace rule. Charged, no credit. 35519 changes the
private environment by linking only the complete source-pinned R1Z dependency
closure into this job's private object directory. Every linked source/hash and
object/hash is recorded, with h4 external pins unchanged. No shared object or
source is overwritten. This is another own-input correction under rule 11;
there is no unchanged proof/source retry on unchanged inputs.
