# Retained input corrections

Before KNF_K001: the local transport import initially omitted __file__; corrected
before SSH or prover submission. A single oversized python -c upload then hit
/bin/bash: Argument list too long after successful admission, before any prover.
The transfer uses scp now; the same initial attempt identifier was admitted again
because no attempt had been submitted. No compiler/solver run was duplicated.

KNF_K001: kani-driver rejects a CLI --edition flag. KNF_K002 removes that flag,
but the default2015 edition cannot compile the actual frozen2021 field source.
KNF_K003 selects --edition=2021 through RUSTFLAGS; compiler succeeds, but goto-cc
is absent from the supplied PATH. Its installed executable is present under the
Kani bin directory. KNF_K004 corrects our PATH and passes. These were own task
inputs, not host/launcher faults. All three terminal error receipts are retained
and conservatively count toward the50 Kani budget. No cap or timeout was changed.
