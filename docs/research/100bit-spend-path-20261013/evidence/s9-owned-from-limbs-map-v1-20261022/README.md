# S9 owned `from_limbs` source map

`from_limbs_maps` proves that the source-shaped `WideExact.from_limbs` decoder result commutes with the explicit nominal structure map from the owned generated field types to the parser field types. The theorem keeps the eight limb range checks and the `Option` result visible. Its transitive `#print axioms` report is standard Lean axioms only.

The owned `Types` and `Funs` modules are separately recorded as successful compile-only dependencies. They did not emit `#print axioms` reports, so this packet makes no standalone axiom claim for them; the main map theorem's transitive audit covers the definitions it uses. Direct import object pins and full selected profiles are retained for all three targets.

`source-identity.json` pins the normalized `from_limbs` body and field structures to the committed [candidate field decoder source-cut packet](../s9-candidate-field-decoder-sourcecut-v1-20261022/README.md). The normalized declarations match exactly after the namespace/import retargeting. This is source identity evidence, not a Rust runtime or compiler binary refinement. The source-cut packet separately records remaining foreign core children.

No compiled objects are included. Verify this packet with `python3 -B check_packet.py` and `shasum -a 256 -c SHA256SUMS`.
