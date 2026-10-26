# Source dependency closure prepared for host audit

`dependency-closure.json` is the exhaustive per-module inventory. Every theorem
listed in a module's `theorems` entry imports that module's `direct_imports` and
`research_dependency_closure`. External/unresolved module paths are listed
separately rather than silently treated as locally available research sources.
The inventory pins the exact source SHA-256, including pending `.lean.txt`
sources. It covers all 127 PV_Src modules considered by the first audit,
547 theorem declarations, and 573 unique `#print axioms` requests (including
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
- Pending `CanonicalNormalize.{public_eq,transfer,withdrawal}`:
  WithdrawalRecipient and its BuilderCanonical admission relation.
- Pending `CanonicalTransferRecord.witness`: RecordAdmission, CanonicalRequest,
  ReferenceTransfer, PathBits/PathSiblings and CanonicalSibling.
- Pending `PackedSelection.{public_preserved,index_bound,checked,bits,primitive}`:
  CanonicalNormalize, FrozenInput, PathBits and FrozenStages; primitive existence
  uses CheckedPipeline and BanksTotal with the explicit reference dictionaries.

This is a source dependency note, not a coherent release replay, an object
fingerprint, or an axioms result. Once the restoration gate opens, the focused
receipts must record actual imported object hashes and the audit must report
all accepted axiom sets. `runjoin-resume-read-only.json` separately pins the
read-only RunJoin interfaces; no foreign branch is implicitly imported into
the current proof closure. The independent withdrawal follow-on draft is
excluded until its family-stage host check.
