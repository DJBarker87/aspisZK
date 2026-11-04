# NGF chain B families

Selected in NFY bottom-up order: 54 modules; 52 prefix copies and two independent emitted leaves reused. No chain A dependency in this nonreused closure.

- NEX_AfterDecodeOracle → NGF_NEX_AfterDecodeOracle
- NEC_Reference.Types → NEC_Reference.Types
- NEC_Reference.Funs → NEC_Reference.Funs
- NEC_AfterstateBox → NGF_NEC_AfterstateBox
- NED_AfterBoxComposition → NGF_NED_AfterBoxComposition
- NEX_AfterstateBox → NGF_NEX_AfterstateBox
- NEX_BoxValueExt → NGF_NEX_BoxValueExt
- NEX_CommonOracle → NGF_NEX_CommonOracle
- NEX_DecoderDomains → NGF_NEX_DecoderDomains
- NEX_ReadDomains → NGF_NEX_ReadDomains
- NEX_DigestCallDomains → NGF_NEX_DigestCallDomains
- NEX_FirstError → NGF_NEX_FirstError
- NEX_LaneOracle → NGF_NEX_LaneOracle
- NEX_LateOracle → NGF_NEX_LateOracle
- NEX_SnapshotBoxOracle → NGF_NEX_SnapshotBoxOracle
- NEX_SnapshotPart16 → NGF_NEX_SnapshotPart16
- NEX_SnapshotPart12 → NGF_NEX_SnapshotPart12
- NEX_SnapshotPart8 → NGF_NEX_SnapshotPart8
- NEX_SnapshotPart4 → NGF_NEX_SnapshotPart4
- NEX_SnapshotPart0 → NGF_NEX_SnapshotPart0
- NEX_SnapshotParent → NGF_NEX_SnapshotParent
- NEX_StatementExt → NGF_NEX_StatementExt
- NEX_TerminalDomain → NGF_NEX_TerminalDomain
- NEY_Field00 → NGF_NEY_Field00
- NEY_Field01 → NGF_NEY_Field01
- NEY_Field02 → NGF_NEY_Field02
- NEY_Field03 → NGF_NEY_Field03
- NEY_Field04 → NGF_NEY_Field04
- NEY_Field05 → NGF_NEY_Field05
- NEY_Field06 → NGF_NEY_Field06
- NEY_Field07 → NGF_NEY_Field07
- NEY_Field08 → NGF_NEY_Field08
- NEY_Field09 → NGF_NEY_Field09
- NEY_Field10 → NGF_NEY_Field10
- NEY_Field11 → NGF_NEY_Field11
- NEY_Field12 → NGF_NEY_Field12
- NEY_Field13 → NGF_NEY_Field13
- NEY_Field14 → NGF_NEY_Field14
- NEY_Field15 → NGF_NEY_Field15
- NEY_Field16 → NGF_NEY_Field16
- NEY_Field17 → NGF_NEY_Field17
- NEY_Field18 → NGF_NEY_Field18
- NEY_Field19 → NGF_NEY_Field19
- NEY_Field20 → NGF_NEY_Field20
- NEY_Field21 → NGF_NEY_Field21
- NEY_Field22 → NGF_NEY_Field22
- NEY_Field23 → NGF_NEY_Field23
- NEY_Field24 → NGF_NEY_Field24
- NEY_Field25 → NGF_NEY_Field25
- NEY_ReachedResultDomains → NGF_NEY_ReachedResultDomains
- NEY_ResultConstants → NGF_NEY_ResultConstants
- NEY_ResultStores → NGF_NEY_ResultStores
- NEY_ResultProjection → NGF_NEY_ResultProjection
- NEY_TerminalGeometry → NGF_NEY_TerminalGeometry

NEX contributes 27 formerly missing certificate declarations in 14 direct auxiliary modules (plus five snapshot-part dependencies). NEY contributes 36 formerly missing declarations in 31 direct modules. NED/NEC supply the afterstate Box composition and independent emitted reference closure. No shared owner is redefined.

Every theorem record in all 89 selected certificates is inventoried before any loaded-module lookup, in NGF_CERT_INVENTORY.json. Certificate admission is governed exclusively by NGF_CERT_CHECK.json, NGF_AUDIT.json, NGF_SCAN.json and NGF_LEDGER_DELTA.json; compilation alone supplies no row credit.
