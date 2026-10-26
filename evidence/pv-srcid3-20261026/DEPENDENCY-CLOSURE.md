# Source dependency closure prepared for host audit

`dependency-closure.json` is the exhaustive per-module inventory. Every theorem
listed in a module's `theorems` entry imports that module's `direct_imports` and
`research_dependency_closure`. External/unresolved module paths are listed
separately rather than silently treated as locally available research sources.
The inventory pins the exact source SHA-256, including proposed audit `.lean.txt`
sources. It covers all 129 PV_Src modules considered by the first audit,
549 theorem declarations, and 575 unique `#print axioms` requests (including
existing definition checks). The standalone final audit imports them all.

Key theorem dependency roots:

- `PV_Src_NativeIdentification.{public_eq,build_eq,transport_eq,identification}`:
  ForestCompilation, NativePremises and Transport; the build proof further
  consumes ForestBanks/ForestTrace and the five original premise families.
- `PV_Src_CheckedCanonical.{checked,words}`: CanonicalRequest, CheckedEncoding,
  RecordDynamic and RecordReference. These prove encoding and reference-side
  range facts; no installed input selection follows from the imports.
- `PV_Src_SelectedThree.complete` and `PV_Src_ThreeConsumer.builder_premises`:
  FrozenPublic/FrozenInput, CanonicalRoots/CanonicalSnapshot, NativeIdentification
  and the unchanged consumer. The Records dictionary is the fixed-root reference;
  compiler success, admission and installed transport are retained.
- `CanonicalNormalize.{public_eq,transfer,withdrawal}`:
  WithdrawalRecipient and its BuilderCanonical admission relation.
- `CanonicalTransferRecord.witness`: RecordAdmission, CanonicalRequest,
  ReferenceTransfer, PathBits/PathSiblings and CanonicalSibling.
- `PackedSelection.{public_preserved,index_bound,checked,bits,primitive}`:
  CanonicalNormalize, CheckedCanonical and PathBits. This generalized carrier
  allows arbitrary supplied snapshots and proves record-stage existence plus
  WitnessOk for every root table; it does not import the frozen bank stages.
- `CanonicalWithdrawalRecord.{request,witness}`: ReferenceWithdrawal,
  CanonicalRequest and CanonicalSibling. Admission supplies the actual request
  amount, without altering the public input.

FocusedAudit 27432 imports the first three new proof modules and successfully
prints 153 axiom sets, all standard. FinalAudit 27431 stopped before Lean on
missing imports; the final read-only inventory still finds 92 absent objects
among 470 research modules in the proposed closure. `final-missing-objects.json`
names them. The corrected combined CanonicalPrivateRecord draft is excluded
from this accepted-module cone and all accepted-theorem claims.

This is a source dependency note, not a coherent release replay, an object
fingerprint, or an axioms result. The focused receipts record actual imported object hashes; the full branch
audit still requires its missing objects and all accepted axiom reports. `runjoin-resume-read-only.json` separately pins the
read-only RunJoin interfaces; no foreign branch is implicitly imported into
the current proof closure. The withdrawal module is accepted at 27435; the combined private/admission
follow-on remains an unaccepted draft.
