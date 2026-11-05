# Domains

NHP_K001: every 3-byte backing array, every prefix length 0..3, actual splitter, exact InvalidInstructionData, unchanged backing. No account metadata/borrow/PDA/entry interpretation is established.

The production caller must supply valid AccountInfo provenance, aliases, borrow prestate, metadata, admitted lists, decoded request and callee domains from the SAME state. No stronger fixed input bound is adopted.

K006..025: actual master/checkpoint/lane terminal wrapper rejection cuts on independently allocated accounts with arbitrary keys/flags/lamports/three payload bytes. Owner and permission guards, master/checkpoint signer ordering, all three failed-borrow paths, master/checkpoint wrong-length mapping; every successful observation has a wrong-error control. The lane borrow path allows either signer flag, matching stored-bump-before-signer source order. No three-byte production precondition is adopted. Native same-account/PDA success domains and arbitrary aliases remain open.

K086 domain finding: System-owned empty-marker classification calls infallible data_is_empty. A valid Rust live exclusive data guard causes a panic, not Err(AccountBorrowFailed). Production reachability is unproved; parent borrowability/cleanup after preceding decoder or CPI calls is an explicit obligation. No new runtime assumption was adopted.

Final iterator cuts K087..094 cover complete arbitrary32/36/82/165-byte backing, every residual begin..end and every whole-backing frame cell. The actual all/any-to-step association and source caller domain remain separate. Packer cuts cover all32-byte digest/seed contents, chunk<4, byte<7/group<8, word<2^56 and arbitrary frame query; they do not certify the complete function.

Dynamic account cuts K106..113 quantify allocation descriptors0..isize::MAX and one arbitrary prefix cell with otherwise-zero storage; they do not quantify arbitrary whole heap contents. Stored-bump tests include exact-size byte72 and failed-borrow classes. No sparse-data, successful malloc, zero borrow counter, fixed-size metadata witness or independently selected state is silently adopted as a production premise. Returning valid allocations describe those local probes only.

Only the CLOSED height and54-error helper certificates have no additional caller-domain obligations. All other physical/loop/value observations are explicitly partial. No new runtime assumption was added; RuntimeCpiReadonlyEntry7 is unused.
