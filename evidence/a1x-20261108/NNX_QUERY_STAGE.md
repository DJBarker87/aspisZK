# X2 query dictionary transport

NNX_QueryLoop.generic is the shared invariant induction over an arbitrary
query dictionary and interval. It reuses NNU_QueryInduction.finite; it does
not duplicate the induction. NNX_QueryValues.source generalises the scalar
and accumulation-slot association. NNX_CurrentQuery.slots/source instantiate
these at the current dictionary on the original 0-to-10 invariant and next=0.
All body conclusions are full Result equalities. Accepted: L002-L004,
standard axioms only; caps unchanged, no repeated failed resource shape.

Still open: transport to LIBC_QueryLoop's dictionary and evaluator and derive
the caller's complete original Domain. LIBC's selected decoder is
NFS_ReadCanonical.read (wrapping field indexing) whereas the current/NJJ
one is SAQ_Decoder.read (checked indexing). Global slot equality must not be
assumed; the actual closure indices are bounded by four, so use a bounded
callback law and gather congruence. This is a local Lean association gap,
not a new runtime trust item or top premise. No A1 credit claimed.
