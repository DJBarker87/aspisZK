# Rejected draft carrier correction

41567 rejected PV_Src_PortFinalRounds.source before the theorem existed: the
actual final loop returns Result(State × F), whereas the draft incorrectly used
Result(State × F × U8 × State). The exact rejected bytes remain in
sources/41567.lean.txt and its error log. The corrected draft projects the
symbolic four-field recurrence to state and trace through an explicit
Result-valued projection, retaining failures. No accepted theorem is changed,
renamed or withdrawn. The three accepted single-step statements are unchanged.
