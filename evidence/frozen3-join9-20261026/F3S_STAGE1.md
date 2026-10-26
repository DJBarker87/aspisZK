# Stage 1: TX1 chronological splice

UNADOPTED frozen3 CANDIDATE; option-B owner decision pending. S2 OPEN;
target not yet established.

`F3S_FirstSplice.split` derives, from successful erasure of the actual
`GExq_FirstCode.code`, a reached preparation, batch0 and checkpoint writer,
whose issued logs concatenate in exactly that order to the entire TX1 code
log. It retains duplicates and introduces no log-equality premise.
The witnesses are on the same source continuation. Further alignment with
`Tx1Q_Execution.Run` and the containing native pair remains to be composed.

Validation: F3S_007 exit0, wall2.436775412s, peakRSS5263996KiB, swap0;
source revision and dirty source hash are in its receipt. Standard axioms
only: propext, Classical.choice, Quot.sound. The tail is independently
checked in F3S_006. Existing coherent SInt2 objects were reused.
F3S_001 hit default heartbeat limits: the replacement isolates the literal
continuation in FirstTailCode/FirstTail, with no cap or heartbeat increase.
F3S_002 was an excluded incomplete literal extraction; F3S_004 corrects it.
F3S_005 was an excluded missing pure-log reduction; F3S_006 corrects it.
No shipped source/artifact changed; no ELF rebuild trigger. Inherited pins:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
These artifact pins were not newly reproduced. No assumption or release
headline is changed. No key/account/fund operation. No push.
