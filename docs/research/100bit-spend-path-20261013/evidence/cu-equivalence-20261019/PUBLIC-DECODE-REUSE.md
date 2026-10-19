# Public-decode reuse: caller equivalence and preparation transfer

Production source remains 39c2971dd16c95858a4cfd2c9ae35da052eacfa9.
Candidate 6 is e5a93db5c9a4883245dc575eaa94742f9adeb629. This checkpoint
connects that change to the reference's existing caller interpretation. It
does not claim that the other retained optimizations or final security transfer
are finished.

## Checked consuming results

- CuSavingsPublicDecode.adapter_context_eq removes the repeated decode for an
  arbitrary surrounding context, with no decoder-success premise. The earlier
  decode supplies its own result by case analysis. Selector, tx1 and error
  mapper failure/divergence remain observable; original public bytes reach tx1.
- CuSavingsPublicDecodeSource.original_first_eq binds the entire prior emitted
  FirstCaller.first body to that model. actualBoundaries uses the checked actual
  decoder and selector, with only the original downstream globals parameterized.
- CuSavingsPublicDecodeTransfer.source_adapter_context_eq checks the source
  call-site replacement for every observer value, including None. The same
  context retains all validation and checkpoint processing.
- CuSavingsPublicDecodeTransfer.entry_success consumes the original
  FirstCaller.first_success. Successful reused entry supplies the same actual
  raw decoder result, semantic public value and downstream tx1 success. No hd,
  chosen-public equality, or downstream-success premise is added.
- CuSavingsPublicDecodePreparation.entry_helper_parsePublic consumes the
  original FirstHelperBinding.first_helper_parsePublic. It supplies the same
  actual helper serializer, parsed public value and initial transcript facts,
  under exactly that theorem's existing tx1/preparation boundaries. It does
  not attribute this older tx1 model to all the optimized Rust bodies.

The last theorem instantiates the historical observer form (Some mark), as
the original helper theorem does. The general call-site equality holds for
all observers; candidate 2's logging/observer equivalence remains a separate
obligation.

## Source bindings and their scope

check-public-decode-source.py pins complete old/new first and stage1 bodies,
the new first_decoded body, and the unchanged boxed decoder. The full stage1
bodies differ at exactly one call. Inlining the exact new wrapper recovers the
old first body. The complete old emitted caller body matches sourceFirst after
explicit boundary substitutions; sourceDecoded is its unchanged tx1/map_err
suffix. The source checker also pins the immutable account-data binding that
supplies the same public byte slice to both decoder occurrences.

These are mechanical source-span/inlining checks, not a formal Rust or SDK
semantics proof. The Box projection, account borrowing/runtime interpretation
and faithful source translation retain the reference's explicit boundary.
The boxed decoder was already called by stage1 before this optimization and
its body is unchanged. Completion of the overall optimized implementation
still requires the remaining source/caller bindings and final composition.
Logical equivalence uses sufficient resources, not identical out-of-CU/heap
failures.

## Coherent reference cache

The recovered original successful-target receipts supply the existing compiled
caller/helper closure. Their target source bytes match the current retained
reference sources. No dependency build or manifest compilation was started.
The focused runner validates the receipt, target source/object and direct
import-object pins, and preserves the original search-root order after the new
CU-only modules. Namespace owner objects are pinned explicitly:

| Owner | SHA-256 |
| --- | --- |
| AspisR1PublicPreparation.Types | e1d3e2db77e3e3730db804bb1a32d75546a18b4929a4e38a3017afd489450922 |
| AspisR1PublicPreparation.Funs | 063480804f71daba2bf1775526611da2bbe0d3e943ba865f571fc91039420359 |
| Aeneas | d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d |

Initially appending those cache roots after the current integration overlay
selected different PublicPreparation.Types/Funs owners. The original helper's
verifier carriers then became unavailable. The failed preparation-a and the
mixed-cache source-b/c/d and transfer-a attempts are archived, excluded from
this release checkpoint, and superseded. This environment change justified
rechecking the affected caller/source targets. No shared integration path or
root checkout was changed.

Accepted receipts: cu-public-decode-a, cu-public-decode-source-e,
cu-public-decode-transfer-b, cu-public-decode-preparation-b. All print only
standard Lean axioms, have zero process/cgroup swap, and use serialized idle-
host jobs capped at 6GiB high/8GiB max/no swap. Peak RSS is below 3.8GiB;
wall times are 1.8–3.5 seconds. Exact commands, revision, feature list, source
snapshots, cache pins and individual metrics are retained in those receipts.
check-public-decode-evidence.py validates these facts without re-running Lean.
