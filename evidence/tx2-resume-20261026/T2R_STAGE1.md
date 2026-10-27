# Stage 1: actual Cons specialisation and reader predecessor

T2R_ParamTop.deployed preserves Cons_Top's conclusion and all installed/native
witnesses, while dropping free M,Cv,N,p and applying Par_Parameters.deployed.
L085-L087 cease to be caller-supplied arbitrary-Params laws. No implementation
or security-metric change. T2R_Public.on_cuts constructs Par's public Input and
transports fit to any transcript under the original same-public-byte equation,
from exactly the supplied cuts, without selecting a second accepted pair.
Its integration into the final shared existential is the next stage.
L151/L152 remain intrinsic LinearMap fields; Par's lemmas discharge their
instances without native arithmetic claims. L153 for arbitrary unassociated
transcripts is not discharged by this intermediate theorem.

Validation: T2R_001 pass; T2R_002 development failure (missing Array.make and
slice-index reductions); changed source T2R_003 passes; T2R_004 passes.
Each receipt records target/status/time/RSS/swap/source revision/hash/dependency
fingerprint and full axioms. The failed elaboration's sorryAx output is excluded.
All passing audits use only propext, Classical.choice, Quot.sound. No timeout,
OOM, cap change, dependency build or unchanged rerun. 4/80 Lean, 0 Kani.
No shipped source/cfg(kani) change, so no ELF rebuild trigger. Inherited pins
remain default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
S2 open; target not yet established.
