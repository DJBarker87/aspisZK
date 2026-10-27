# Process record

Initial SBF source archive omitted Cargo path dependencies under docs/refine. The first scope failed metadata loading before compilation (exit1,0.095s,35728KiB,swap0); no ELF existed or pin comparison ran. The corrected archive adds the research Cargo dependency closure.

At 12:16:43 UTC the staging-dependency reservation refused (projected reservation above55GiB). The archive transfer nevertheless ran because the staging shell did not assert admission: a staging-order deviation, with no capped scope launched. The subsequent build reservation also refused and no scope ran. All further transfers must explicitly assert admission. Required three-minute wait starts at the later build refusal; use a fresh labelled output.

Evidence collection reservation at12:21:14 refused; after more than three minutes, collect-retry1 admitted and transferred only JSON/log receipts. No further build/proof scope ran. All generated program keys remain mode0600; compiled cache cleanup is in cleanup.json.
