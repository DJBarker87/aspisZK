# Stage 3: remove native-local finish law inputs

FIs_OnRun.strengthen derives both RoundLaws and dot from the same native
Calls/Aux/Shape, source parser/data and successful saved-reader decode.
FIs_Literal.strengthen obtains saved64 from Tx2N_Reader.saved_ten on the SAME
checkpoint and writer value. FIs_Caller.strengthen derives proof/checkpoint
byte identity from the reached tx2 S2CallerFacts. FIs_Result.strengthen retains
the original existential f/s/run/tx2 and all non-finish conjuncts while consuming
those derived laws. The final output exports original Cons_Native.Calls;
Aux/Shape are not replacement premises hidden in an exported contract.

The native finish continuation now takes FIs_Pair.Law, matching, and the
three semantic endpoint equations. It no longer takes either RoundLaws or
dot. FIs_Finish.forget converts that stronger outcome to the original one
using the original callback's Pair field and preserving its successful values.

Attempts030/031/035–039 pass with standard axioms only. The three failed
attempts032–034 and their replacements are documented in FIs_FAILURES.md.
No caps increased; the timed-out proof was split before retry. These are
focused proofs, not a package replay or release claim. Exact receipts include
all AGENTS section6 target/artifact/revision and build metrics.
