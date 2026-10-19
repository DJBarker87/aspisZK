# Executable finite-byte sampler into retained WideExact

The actual finite sixteen-word retry sampler is run for eight limbs, checks the Option success tags, and packs successful values through a computable equivalence to the retained WideExact field. Its successful output fiber has exactly the proved eight-limb count, giving conditional uniform output mass 1/P31^8. Its actual abort event is identified with the previously proved eight-limb abort event, with exact mass 1-(1-2^-496)^8 and upper bound 8*2^-496.

The finite-tape theorem lifts the actual sampler to Fin n indexed inputs. Explicit product fiber equivalences prove exact tape success/output counts and conditional output mass 1/P31^(8*n). This is extractor randomness, not a source-correspondence theorem for Fiat-Shamir challenges or privacy masks.

Open: paired-tape pushforward to the decoder bank, total tape rejection bound, executable point/input construction, complete extractor and spend witness, bit-cost, protocol/ROM and source/runtime composition. Focused Lean 4.32 receipts contain exact source/import/object pins, commands, revisions, status, time, RSS, swap and standard-only printed axioms. No package-wide replay or full 100-bit security claim.
