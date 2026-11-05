# Domains

NHP_K001: every 3-byte backing array, every prefix length 0..3, actual splitter, exact InvalidInstructionData, unchanged backing. No account metadata/borrow/PDA/entry interpretation is established.

The production caller must supply valid AccountInfo provenance, aliases, borrow prestate, metadata, admitted lists, decoded request and callee domains from the SAME state. No stronger fixed input bound is adopted.
