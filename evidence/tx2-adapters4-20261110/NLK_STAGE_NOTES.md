# NLK stage notes

NLK_L001: own source used reserved keyword `local`; corrected to `caller` in
L002; no infrastructure change. L002 compiles, standard axioms.
NLK_L003 compiled the local allocator composition with a provisional size 728.
K001 checks the actual frozen lane layout: 720 bytes, alignment 8. That draft
is NOT a release result; source corrected to 720 for the next compile. No
native verdict was renamed. Local support only; row217 remains OPEN.

All native submissions use the inherited frozen graph/edge validator offline,
exact KMX mitigation and source-erasure checks. No function contracts or
Ref/RefMut-return substitution. Each source/log input retained by sha256.
