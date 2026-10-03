# R490 literal candidate b failure

This archived attempt is a translation failure, not a proof. The exact LLBC
has SHA-256 `236078d52602ab801ae95ba28a0dba8d0cd595090b365d259405550ab838d186`.
The recorded run exited 2 in 0:00.17 with peak RSS 57,200 KiB and zero swaps.

The raw log records a missing function at core slice source lines 4465:21-31,
reported by `llbc/FunsAnalysis.ml:134`. The next candidate is outside this
archive; this failure does not establish a source or proof result.
