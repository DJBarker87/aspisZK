# Stage 5: fresh-query replay and concrete account cuts

SCF_FrameReplay.recorded removes the global known-address restriction from
frame replay. It proves replay through an arbitrary consistent recording
agrees with H whenever the actual sampler reads occur in that recording.
This uses the maintained transcript replay and state-only frame theorem;
fresh outer addresses need not occur in the source log.
016:exit0,wall2.921607661s,RSS5381768KiB,swap0,standard axioms.

SCF_AccountCuts.delete_choice specializes the cut argument to the ORIGINAL
SCE account program and its actual response-selected TX2 inputs. Removing
second-choice queries preserves every cut already reached in TX1. No TX2
acceptance is required, so rejecting suffixes are covered. The right log is
an H-dependent deletion, not a newly constructed free-query ByteProver.
This is not identification with the headline's standalone verifier log.

The remaining concrete causal premise is sampler-read containment in the
actual first-wrapper prefix (on the submitted public/proof), plus the
accepted second-input/source association or its charged-collision branch.
SCE_SourceReadFrames establishes source-model frames, not this ORIGINAL
first-wrapper prefix lemma. No extra containment/association hypothesis is
installed as a retained source-refinement law.

017 failed because a second reassociation grouped the extra choice with the
shared prefix and prevented cut_append from matching.018 removes that second
rewrite and passes; no new premise or limit change.018:exit0,
wall3.028441394s,RSS5377380KiB,swap0,standard axioms only.
