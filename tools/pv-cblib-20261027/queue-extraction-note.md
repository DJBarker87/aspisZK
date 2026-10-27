The serial Lean queue calls the existing launcher once per module, through the
same per-job tally and resource gates. It does not alter any host launcher,
reservation, monitoring, or build infrastructure. It never retries a Lean
compiler error; only reservation refusals get the prescribed wait and a new ID.
