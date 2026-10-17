# Historical C2 model context audit

The nine archived `C2OwnedHostConstruction` and four
`C2RecordedExperimentConstruction` reports are **HISTORICAL_CONTEXT_ONLY**.
They do not count as current accepted semantic-model results. Their original
sources, receipts, axioms reports, and archives are retained unchanged.

`audit.json` records three explicit source-import witness paths, exact source
snapshots and the first object selected by the archived `LEAN_PATH`. This is a
read/hash audit, not an exhaustive closure enumeration or a new Lean check.
Both models reach historical `FS2.Duplex` object
`fd269bd4a532a728a2a4acc58796513ccd052fd7b876074622b329551473da9e` and
`UniformStateFirstHit` object
`b0d7a10701d65195c78b88d18fedff25a81eba87e353d7ca489cb4fa119d9cac`.
Their repaired counterparts are
`4b1b91be1594807cbde6893ec7fd22a43f08a6a30c489566e21228dc064dbe30` and
`5c8215454529102226f974b7d80b36f0a7554c590effa872dedc262820cd890f`.
The resolved Circle object is repaired
`05c7d259551e4a362c99a4dc9913848d589a94a0c06f9325dad0099a58045461`,
not rejected `39ea3fa6eb53446ecf6cd4a3856219165b247c4175cf79a28313a55958b15597`.

The current Aeneas-only embedding checkpoint checks the six generic construction
core lemmas again in a fresh namespace. The literal-word and recorded-experiment
semantic bridges have not been rebound to the repaired closure. Actual
Backend/build ownership, complete execution recording, packing, salt paths,
custody, and checkpoint obligations remain open.

Run `tools/c2-owned-host-extraction-kit/check-historical.py` from the research
folder to validate this report without launching Lean or a build.
