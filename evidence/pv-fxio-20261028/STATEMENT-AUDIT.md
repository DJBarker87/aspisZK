# Original carrier check

Frozen callback signature (ProverRwFullExternalFuns.lean, op22):

```
op22 {P : Type} (AsRef : core.convert.AsRef P std.path.Path) :
  std.fs.OpenOptions → P →
  Result (core.result.Result std.fs.File std.io.error.Error)
```

ExternalFuns is a Lean class of pure functions. The signature has no world
argument/output. Fixing the class, AsRef, options and path fixes the entire
outer Result, not merely its value projection. In particular, it cannot be
both an outer `.ok (.Ok file)` and an outer `.ok (.Err error)`.

The shipped reserve_fallible suffix creates OpenOptions, sets write and
create_new to true, sets Unix mode 0o600, opens the reservation path, writes
magic/digest/nonce, syncs the file, syncs the directory, and returns true.
The error path tests Error.kind against AlreadyExists and returns false.
The corresponding extraction clears self.last_error and returns self with
last_error := none on both success and AlreadyExists. Its directory carrier
is unchanged, and no filesystem world is returned. Reusing the SAME dictionary
and SAME argument values therefore cannot represent the reached first/second
create_new boundary results. A dictionary per pre-world or a path/options
carrier that encodes a world changes these quantifiers; it is a possible
repair route and needs a proved caller-level threading/transport theorem.

PV_FXI_RepeatCreate formalizes the obstruction for arbitrary option/path
carriers and arbitrary complete result carrier with a fixed observation
projection. It does not claim to refute every effect-aware interpretation,
the existing conditional privacy endpoint, or the shipped Rust algorithm.
The finite native fixture is needed to show the differing outcomes are real
for the selected source boundary, rather than only a chosen reference model.

No row closure will be credited from this obstruction. If the fixture confirms
it, the counterexample is to the proposed fixed-dictionary universal source
association in the ORIGINAL pure carrier. It is not a privacy attack.
