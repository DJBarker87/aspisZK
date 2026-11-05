# Domains

NHP_K001: every 3-byte backing array, every prefix length 0..3, actual splitter, exact InvalidInstructionData, unchanged backing. No account metadata/borrow/PDA/entry interpretation is established.

The production caller must supply valid AccountInfo provenance, aliases, borrow prestate, metadata, admitted lists, decoded request and callee domains from the SAME state. No stronger fixed input bound is adopted.

K006..025: actual master/checkpoint/lane terminal wrapper rejection cuts on independently allocated accounts with arbitrary keys/flags/lamports/three payload bytes. Owner and permission guards, master/checkpoint signer ordering, all three failed-borrow paths, master/checkpoint wrong-length mapping; every successful observation has a wrong-error control. The lane borrow path allows either signer flag, matching stored-bump-before-signer source order. No three-byte production precondition is adopted. Native same-account/PDA success domains and arbitrary aliases remain open.
