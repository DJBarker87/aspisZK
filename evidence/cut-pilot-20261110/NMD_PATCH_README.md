# Harness configurations

NMD_HARNESSES.patch is the canonical ACTUAL parser/marker configuration against frozen4bb3b3f5. Apply only in a private scratch copy, together with the exact canonical KMX_copy_stubs.patch. It is not a shipped-source change. The parser contracts have NO passing full-allocation proof; marker has the restricted controlled certificate. Do not use the proposed parser contract as verified evidence.

Shape, constructor, generic-record, ProgramResult and informational K-3 configurations are mutually exclusive private overlays, selected by the NMD_ runners. Every executed configuration is preserved once by content hash in NMD_INPUTS.json/NMD_INPUTS, indexed per attempt. Separate NMD_*.rs templates and scripts reproduce those overlays. No compiler, binary, ELF, object or dependency-source change is committed. NMD_K3_* files are byte-identical imports of the NEF_K002 reproducer with original names; their writable statics are informational only.
