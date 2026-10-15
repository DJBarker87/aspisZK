# Independent evidence review

The mass module applies the existing independent-answer mass bounds to the
selected staged sets. `gamma_mass` maps row 27 through the nonzero gamma
sampler and invokes `OpeningSamplerBound.gamma_mass_le`; `gamma_ne_zero`
records the corresponding nonzero fact. Rows 28, 29, and 30 map through the
ordinary field sampler and invoke `kappa_mass_le`, `first_mass_le`, and
`second_mass_le`, respectively. The earlier payloads and challenge values
remain explicit inputs to each theorem. The degree premises for rows 29 and
30 come from the degree-at-most-6 theorems for the typed coefficient
payloads.

The successful attempt is `R1SelectedOpeningEventMass-a`: exit 0, 2.04 s,
3,582,272 KiB peak RSS, zero swap, cgroup 4G/6G/0. Its source SHA-256
`5c7ad8017e7dcca60c517d82cad5739cceea3491e7ab5e8b990f401042b46302` agrees
with the receipt and final snapshot. All five public axiom reports list only
`propext`, `Classical.choice`, and `Quot.sound`. The three archived objects
match their manifest names, sizes, and hashes.

The manifest initially referred to its two import snapshots without their
actual `R1` filename prefixes. Those paths now match the files in
`import-sources/`; source hashes and Lean sources were not changed. The
source-path validator checks all three manifest target sources successfully,
and the complete bundle checksum list verifies.

These are fixed-input independent-answer bounds. This review does not infer
causal availability of the inputs, a D2 result, or source correspondence.
