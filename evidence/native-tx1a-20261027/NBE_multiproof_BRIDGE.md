# NBE multiproof native P6 bridge

**OPEN. No headline premise removed.** The target is the native binary
`multiproof::node_count` and `multiproof::verify_in_place` of frozen Rust
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Headline remains
AspisR1.RPx_Deployed.deployed; L154 remains a statement parameter. This is an
obligation of narrowed D188. S2 / deployed100-bit target not established.

## Single joint statement and source association

For Arity::Two, arbitrary32-byte oracle replies, root, increasing distinct
idx[..d]<262144, 1<=d<=16, arbitrary matching val scratch and physical node
slice<=5504 bytes, native count returns the installed count and native
verification returns the same Boolean, complete idx/val poststate and ordered
attempted digest log as Port4B_CountInstall.nodeCount and
Port4B_VerifyInstall.verify. Rejects retain their actual partial scratch and
issued-prefix log. The same statement covers TX1 n10 and TX2 n12; d<=10 is
NOT imposed. Success does not imply ignored padding is zero; the batch caller
must supply exactly the counted prefix after checking its slot padding.

Exact full-file/body pins and cohort owners are NBE_SOURCE_ASSOCIATION.json
(F118–F128). The native verify_in_place body is unchanged. NBE_K005 directly
calls it through mutable borrows; the new row cuts are source partitions,
not direct calls to the whole native function. SDY's fixture/emission checks
are not promoted to this native bridge. Arity Eight and its parent_with_digest
are outside the release binary call domain.

## Established local pieces

- K010 checks actual occupied_binary_parent and sibling_binary_parent calls,
  all component lengths/header, arbitrary selected input bytes and arbitrary
  reply coordinate, exactly one call. Occupied index<15; sibling index<15.
- K013 supplies the missing sibling index15 case with the same arbitrary
  input-byte/reply/call observations. K010+K013 cover the complete callback
  index domains; no fixed-array fixture is used.
- K005 checks actual verify_in_place n=0 or n>16: false, no hash, all scratch
  coordinates unchanged by arbitrary coordinate observation. This is a
  rejection-path theorem and does not validate the sorted-index admission scan.
- NBE_ROW_ASSOCIATION.json pins one exact binary arm plus its chronological
  idx[w],val[w],w writes. K011 combined state/address observation timed out
  and is EXCLUDED. NBE_TIMEOUT_SPLIT.json records the changed projection.
  K012 state-only projection also timed out and is EXCLUDED; K015–K017
  partition its three disjoint branches (NBE_K012_SPLIT.json).
  K015 paired-child and K017 short-sibling rejection state/cursor/frame passed;
  K016 supplied-sibling branch
  timed out and is EXCLUDED. This is the smallest isolated timed-out member: a
  supplied sibling with enough bytes, arbitrary mutable prestate, and one
  selected poststate coordinate. No timeout increase or unchanged rerun.
- Inherited MultiproofConeP6Composition.rows_eq/level_eq and
  MultiproofConeP6Verify.verify_in_place_owned provide induction ONLY after
  their actual NodeGate is instantiated; they are not that instantiation.

## Exact open members

`NBE_NativeCountScan`: native well_formed and index-only nested count loops,
including arbitrary same-parent scans and in-place unread-tail preservation,
refine MultiproofConeCountLevels.sourceCount / Port4B_CountInstall.nodeCount.
No native count gate was launched in this packet.

`NBE_NativeNodeGate`: for EVERY RowDomain physical state with physical<=5504,
active i<n, w<=i, natural scalar ports and SAME mutable scratch/physical buffer,
the native binary row has exactly MultiproofConePhysicalProgram.node's Result,
poststate and ordered address/reply log. A <=64-byte local window check alone
is insufficient: prove physical-window rebase, cursor translation and address
identity, then associate scalar/array ports with the reference row.

`NBE_NativeVerifyControl`: derive each next row/height domain, associate native
well_formed and n=w updates and final n/index/root/cursor conjunction to the
installed wrapper, retaining rejected partial scratch. Then consume the
inherited18-level induction. No whole-buffer Kani attempt is authorized.

No existing native gate, successful model import or independently selected
accepted state is substituted for these members. No SHA or field multiplication
is unwound; NBE_STUBS.md records observers and no function stubs.

## Validation and retained boundaries

See NBE_HANDOFF.md and NBE_ATTEMPTS.json for all exact targets, source/tool/deps
pins, exits, wall/RSS/swap, axioms audits, excluded failures and budget accounting.
No shipped file changes; no ELF rebuild. The inherited default f8c0ec72…,
devnet63ad3e9c… and Pool121f3e29… pins are not newly reproduced. All new top
theorems have a co-imported standard-axioms audit. No headline trust item,
carrier, event, metric or runtime/source-to-ELF admission is discharged.
