# NOM remaining

Target not yet established. Both NOM goals are closed as model lemmas (NOM_HANDOFF.md). What they do not close:

1. 345 public binding (for NOC X8). `NOM_TerminalDomain.reached` needs `a.1 = NNH_Libraries.C.semanticPublic
   (NNH_S1DecodeOk.carrier st)` for the statement `st` the installed op47 returned. The model body passes
   `PoolV1PairForestTerminalStatementV1.semantic_public val2` to first_decoded, and the NOC ports are stated at
   `FirstComposition.toCurrentPublic pub`. The equation `semantic_public st = ok (toCurrentPublic
   (C.semanticPublic (carrier st)))` is part of the 345 composition, not proved here. The rfl slot lemma
   `(S_host sdk).op21 = NNH_S1HostCodec.validate` was also not re-checked by me.
2. Batch domain on the 094 path. `NOM_MerkleParent.model0` takes `LIBC_BatchMerkle.Domain a` (k = 0, 57607-byte
   proof, canonical queries, committed roots), exactly as the forward model0 does. Deriving it on the reached path
   remains NOC's open item ("no NOC lemma does this yet").
3. Everything after the converse ports: 094/345 forward and converse compositions, X9 assembly, raw ax2 audit.

21 of the 28 NOM scopes are unused.

target not yet established
