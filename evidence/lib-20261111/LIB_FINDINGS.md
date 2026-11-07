Target not yet established. No new finding. The LIB0 F1–F8 inventory is retained.

LIB-F01: cache precedence. Initial LIB_L001–L009 selected pre-rev2 RSL_Base/Pool/241 through NND_objects (same older objects in NNC seeds). These successful compilations are supporting historical checks, not frozen-rev2 validation. No field credit or principal consumption occurred. LIB_SPEC_PINS.json checks canonical rev2 sources against NMS_L282–288 source hashes, and copies their closure-pinned objects into private LIB_specs first. Replay affected own modules under this changed environment before use. NND_CheckpointLaw and similar pre-rev2 getter theorems must not be imported as unrestricted rev2 laws.

LIB-F02: LIB_L016 fails at import NND_AccountCarrier: duplicate old lazy equation RSL.OwnedAccount.data.eq_1 with canonical rev2. NND getter/CheckpointLaw statements use the old pure-Except type, so importing them is not a rev2 bridge. Replacement LIB_Transcribed isolates the already-rev2 NMS getter and passes L017. LIB_ResultTotal and decoder-total/value support are retained NND proof bodies with prefix/import substitutions; original paths/hashes are in LIB_REUSE.json. No existing proved module is edited.

L051 input-statement correction: require_zero returns AccountAlreadyInitialized, as the frozen source and RSL.requireZero specify. The first LIB_Zero statement mistakenly said InvalidAccountData; excluded failure, corrected exact error constructor before retry. No spec/source modification.

L052: corrected zero-error statement was proved by rw; the leftover rfl produced No goals to be solved. Retire rewrite-then-rfl script shape after these two failures. Replacement uses the existing zero_source equation directly with only the byte-map equality, no unfolding or loop replay.

L068 symbolic digest-word proof: bv_decide abstracted the unreduced U32 projection as an independent value and reported a potentially spurious counterexample. This is not a digest/source counterexample. Replacement exposes four BitVec byte variables and normalizes literal list lengths before the reflected proof.
