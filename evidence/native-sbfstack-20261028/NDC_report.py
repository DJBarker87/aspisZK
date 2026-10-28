from pathlib import Path
import json,re
E=Path(__file__).parent
warnings=json.loads((E/'NDC_WARNINGS.json').read_text())
def name(s):
 s=s[3:];parts=[]
 while s and s[0].isdigit():
  m=re.match(r'\d+',s);n=int(m[0]);s=s[len(m[0]):];parts.append(s[:n]);s=s[n:]
 return '::'.join(parts).replace('aspis_core','C').replace('aspis_statement','S').replace('aspis_r1_cost_probe','R').replace('Vec$LT$T$C$A$GT$','Vec<T,A>')
text='''# Frozen SBF stack-frame finding

**None of the 34 warned function instances is linked into any of the three
pinned deployed ELFs. No TX1, TX2, or Pool instruction can call those omitted
instances. No source/build change or additional P7 qualification is warranted
by these 34 diagnostics.** This is a bounded finding about the reported
functions, not a proof of all SBF stack/pointer safety or compiler correctness.

## Target and exact evidence

Frozen shipped source revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
All following artifact hashes were freshly measured in NDC_I001; the successful
SBF builds themselves are reused from NCR_B003 / NCY_B001 / NCY_B002. No SBF
build or live-cluster readback was performed by NDC_.

| ELF | SHA-256 | Bytes | SBF version |
|---|---|---:|---|
| default | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 | 1563728 | V0, e_flags=0 |
| devnet | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 | 1563728 | V0, e_flags=0 |
| Pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 605704 | V0, e_flags=0 |

The release files are stripped: their `.dynsym` tables alone cannot answer the
question. NDC_I002 recovered complete `.symtab` tables from retained Low2
**unstripped linked outputs**, not relocatable library symbol lists. NDC_I003
compared the complete `.text` byte strings and virtual addresses: default and
devnet match the retained verifier output exactly, and Pool matches the retained
Pool output exactly. Their ELF hashes differ because of non-text data/stripping.
[NDC_LINKAGE.json](NDC_LINKAGE.json), [NDC_UNSTRIPPED.json](NDC_UNSTRIPPED.json)
and [NDC_EXACT_SYMBOLS.json](NDC_EXACT_SYMBOLS.json) retain the association and
exact symbol searches. This also rules out confusing an emitted-but-unlinked
library routine with deployed code.

Platform-tools v1.52 `llvm-objdump -d --demangle` supplied the actual disassembly
of all three final files and both unstripped outputs. Text, symbol and readelf
transports are committed as `.txt.xz` with original SHA-256 sidecars; see
[NDC_TEXT_PINS.json](NDC_TEXT_PINS.json). Tool executable hashes/version outputs
are in [NDC_TOOLS.json](NDC_TOOLS.json). The pinned SBF compiler remains
rustc1.89.0-dev/LLVM20.1.7, cargo-build-sbf3.1.13 (reused NCY/NCR provenance).

## Reachability method and source cross-check

The 34 rows below are **function identities**, collapsing the two builds'
crate-disambiguator hashes only for presentation. The full 62 exact diagnostic
symbols and all diagnostic offsets/frame sizes remain in
[NDC_WARNINGS.json](NDC_WARNINGS.json). Searches use exact full symbols first.
Every one is absent from both complete linked symbol tables. For non-generic
functions, searching without the final hash also finds no alternate instance.
The two generic families require the instance distinction described below.

[NDC_CALLGRAPH_FINAL.json](NDC_CALLGRAPH_FINAL.json) contains disassembly-derived
call edges and functions: 299 verifier and 420 Pool functions, respectively.
After applying ELF call relocations, direct entrypoint closures contain 268
verifier and 351 Pool functions, with zero unresolved **direct** calls. External
syscalls are named from `.rel.dyn`/`.dynsym`; relocation placeholders are not
mistaken for calls to self. There are 36 verifier and 80 Pool indirect-call
instructions; they are explicitly retained, not resolved by guessing targets.
An omitted code instance cannot become reachable by resolving an indirect call.
The earlier NDC_I003 graph is provisional: its 12/24 unresolved calls were
relocation placeholders and its reachability counts included those false nodes;
NDC_I009 is authoritative. No complete function-pointer or inline semantic
refinement is claimed by a direct call graph.

Release features are those in NCY/NCR: verifier
`pool-adapter,private-leaf-salts` plus dependency `optimized-terminal,program-build`;
Pool `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`
and their recorded defaults/transitive features. The frozen source route is:

- Verifier `entrypoint -> process_r1_cost_probe_instruction -> pool_route::admitted
  -> r1_pool_adapter::process`. Admission accepts exactly `[3,10]`, `[3,11]`,
  or an `ASQ8` prefix. TX1 uses `owned::stage1 -> stage1_owned -> first_decoded
  -> verifier::tx1`; TX2 uses `owned::stage2 -> stage2_owned -> verifier::tx2_authenticated`.
  `verifier.rs:517` reexports these from **candidate**, not `aspis_core::r0::verifier`.
- Pool `entrypoint -> processor::process_instruction` dispatches its feature-selected
  instruction handlers; selected verifier dispatch and split-checkpoint transport
  use the Pool/R1 path. The R0 full prover/opening verifier family is not this path.
- The three by-value `Prefix::point_claims` methods, by-value
  `state_only_verify::r0::verify_semantics`, and `r0::semantic_handoff` are distinct
  from boxed/heap variants. Frozen `aspis_statement::r0` imports
  `verify_semantics_heap` and calls `semantic_handoff_heap`. By-value methods
  have no callers in their retained optimized crate IR; their definitions are
  generated in libraries and then discarded from the final programs.
- The two generic diagnostics are reached in the **unused R0 library**:
  32768-byte `try_from_fn` from `r0::prover::Commitment::new`, and
  `Vec::extend_trusted` from `r0::prover::prove`. Their parent instances are absent.

[NDC_SOURCE_SLICES.json](NDC_SOURCE_SLICES.json) retains frozen source bytes,
hashes and paths; [NDC_DIAGNOSTIC_IR.json](NDC_DIAGNOSTIC_IR.json) records the
original generated LLVM definitions/signatures and immediate IR callers. The
latter is a source/call-shape cross-check, not an exhaustive cross-crate IR
reachability proof. Inlining and dead-code elimination mean a warning in a
library compilation does not imply a deployed out-of-frame access.

## Per-function, per-ELF results

Aliases: `C=aspis_core`, `S=aspis_statement`, `R=aspis_r1_cost_probe`.
`D`/`P` in the diagnostic column names the verifier-devnet/Pool compilation;
values are **diagnostic maximum offset / estimated total frame size**, in bytes.
A reused D diagnostic in a Pool row does not claim Pool emitted that diagnostic.
All reported offset magnitudes exceed 4096, but none is a deployed access.
`—` for ELF access means no such function body exists, rather than offset zero.
Classification `omitted` is outside (a)/(b)/(c): there is no reachable warned
function to classify. The reachable (a), (b) and (c) sets are all empty.

Native codes: `Y-C`, `Y-S`, `Y-R` = named x86-64 library body observed in the
corresponding freshly built native core/statement/R1 library; `Y-G` = generic
family observed, not a hash-equivalent SBF instance; `Y-IR` = native encoder
LLVM definition and generic MIR observed even though the original library's
standalone symbol was optimized away. None is a native binary equivalence proof.

| ID / function | ELF | Warned instance present? | TX1/TX2 or Pool path? | Diagnostic offset / frame | ELF access beyond 4096 | Class | Native client |
|---|---|---|---|---:|---|---|---|
'''
rows=[]
for i,w in enumerate(warnings,1):
 n=name(w['identity'])
 native='Y-G' if i in [3,4] else ('Y-IR' if 'EncodingDomain' in n else ('Y-R' if n.startswith('R::') else ('Y-S' if n.startswith('S::') else 'Y-C')))
 for mode in ['default','devnet','pool']:
  key='pool' if mode=='pool' and 'pool' in w['diagnostics'] else 'devnet';d=w['diagnostics'][key];tag='P' if key=='pool' else 'D'
  text+=f"| {i:02d} `{n}` | {mode} | No | No | {tag}: {d['offset']} / {d['frame']} | — | omitted | {native} |\n"
  rows.append({'id':i,'function':n,'identity':w['identity'],'elf':mode,'present':False,'reachable':False,'diagnostic_source':key,'diagnostic':d,'deployed_stack_access':None,'classification':'omitted','native':native})
text+='''
### Generic-name collision checked explicitly

The verifier contains three **different** `core::array::try_from_fn` instances:
`hf04b4717f2c37ef7` at `0x47190`, `h56e27f14e3d6ca3f` at `0xcd658`, and
`hc0f6e83f55d88d96` at `0xcd988`. Their largest direct `r10` load/store negative
offsets are respectively 256, 168, and 168 bytes. These are syntactic direct
access measurements, not bounds on every derived pointer or callee access.
[NDC_GENERIC_DISASSEMBLY.json](NDC_GENERIC_DISASSEMBLY.json) retains the exact
instructions. The warned hashes are `hade86b1f9a78d42d` (D) and
`h947f9a3583a5e08e` (P), neither present. Pool has no `try_from_fn` instance.
There is no linked `Vec::extend_trusted` instance in either program output.
Across all linked functions the largest direct negative `r10` memory operand
is 4096; this is supporting disassembly evidence, not an alias/dataflow proof.

## Runtime stack model and limits of the runtime pin

The ELF version is determined: all three have `e_flags=0`, mapped to V0 by
[SBPF elf.rs:1276–1292](https://github.com/anza-xyz/sbpf/blob/5a386e65b6b0ff8a71ea9f38a807e931451ef09b/src/elf.rs#L1276).
The pinned compiler version alone does **not** identify a validator release or
its active feature set. The supplied ELF/build receipts do not pin a deployed
runtime executable or `virtual_address_space_adjustments` activation. No chain
query was authorized/performed. Consequently an unconditional claim about the
actual deployed frame-gap setting would be unsupported.

For a concrete offline source reference, the repository's existing local
LiteSVM harness lock (`results/pool-v1-one-terminal-runtime-20260827/harness/Cargo.lock`)
resolves Agave4.2.1 and `solana-sbpf`0.21.1. The host contains those exact registry
sources (package labels/VCS records, not freshly authenticated archives): SBPF commit `5a386e65b6b0ff8a71ea9f38a807e931451ef09b` and Agave commit
`c4b48df969a9e4f121e14a389bd7bec34c752507` (registry VCS records).
[NDC_RUNTIME_SOURCES.json](NDC_RUNTIME_SOURCES.json) pins their individual source
hashes and text. Optional NDC_I010 package-checksum verification could not run
because the local SBPF registry copy has no `.cargo-checksum.json`; that attempt
failed and consumed the final scope. No archive authenticity claim is supplied.
This is a conditional runtime analysis of those inspected sources,
**not evidence that a live validator runs them**.

- The standard frame size is 4096 bytes, maximum call depth64. See
  [SBPF vm.rs:47–98,158–175](https://github.com/anza-xyz/sbpf/blob/5a386e65b6b0ff8a71ea9f38a807e931451ef09b/src/vm.rs#L47)
  and [Agave execution_budget.rs:73–82](https://github.com/anza-xyz/agave/blob/c4b48df969a9e4f121e14a389bd7bec34c752507/program-runtime/src/execution_budget.rs#L73).
  The optional SBPF `conf-stack-frame-size` build feature can override the default;
  it is not justified to silently assume arbitrary test settings are production.
- V0 has automatic fixed frame bumps and permits gaps; V1/V2 manual-frame rules
  do not apply. See [program.rs:25–38](https://github.com/anza-xyz/sbpf/blob/5a386e65b6b0ff8a71ea9f38a807e931451ef09b/src/program.rs#L25).
  Agave constructs `enable_address_translation=true`, and sets
  `enable_stack_frame_gaps` and `aligned_memory_mapping` to the negation of
  `virtual_address_space_adjustments`; see
  [syscalls/src/lib.rs:347–380](https://github.com/anza-xyz/agave/blob/c4b48df969a9e4f121e14a389bd7bec34c752507/syscalls/src/lib.rs#L347).
  That same constructor can disallow V0 execution via `disable_sbpf_v0_execution`
  unless `reenable_sbpf_v0_execution` is set: rejection precedes execution.
- With gaps enabled, the mapped 4096-byte frames alternate with **4096-byte
  unmapped gaps**. `configure_program_regions` supplies exactly that gap size:
  [Agave vm.rs:78–104](https://github.com/anza-xyz/agave/blob/c4b48df969a9e4f121e14a389bd7bec34c752507/program-runtime/src/vm.rs#L78).
  Calls increase the frame pointer by8192; local allocations use negative offsets
  from that pointer. With gaps disabled, the bump is4096 and frames are adjacent.
  See [interpreter.rs:132–163](https://github.com/anza-xyz/sbpf/blob/5a386e65b6b0ff8a71ea9f38a807e931451ef09b/src/interpreter.rs#L132).
  The initial pointer is stack-base+4096 for V0 (vm.rs:380–393).
- Mapping checks the **whole mapped stack**, not ownership by the current frame.
  An access starting in a gap, or failing backing-stack bounds, returns an error; interpreter memory operations
  propagate it and execution stops. Depending on address, the error is
  `StackAccessViolation` or `AccessViolation`. See
  [memory_region.rs:214–250,819–856](https://github.com/anza-xyz/sbpf/blob/5a386e65b6b0ff8a71ea9f38a807e931451ef09b/src/memory_region.rs#L214)
  and [Agave vm.rs:355–449](https://github.com/anza-xyz/agave/blob/c4b48df969a9e4f121e14a389bd7bec34c752507/program-runtime/src/vm.rs#L355).
  The translator checks the starting address gap bit and backing-buffer end;
  this is not a per-frame interval checker for a span crossing a boundary.
  An address in another mapped frame is not rejected merely because it belongs
  to that other frame. Such an access can change compiled behaviour.

For example, with gaps enabled and depth sufficient to have a caller, bytes at
`fp-4097` through `fp-8192` lie in the preceding gap, whereas `fp-8193` through
`fp-12288` lie in the preceding mapped frame. Thus a large offset can jump over
a gap: the warnings are **not generally guaranteed fail-closed**. With gaps off,
negative offsets beyond4096 can directly reach previous frames. This is a source
model implication, not a concrete execution of any warned routine.

Because every warned instance is omitted, these runtime alternatives do not
change any row in the table. There are zero class-(b) functions in the pinned
artifacts, so the requested conditional local frozen-ELF test has no target.
**No local SBF VM run was executed and no output/source agreement is claimed.**
If a future build links any warned body, it requires fresh frame/dataflow
analysis and class-(b) VM testing; the old omission result must not be reused.

## Native client/prover implications

NDC_B005 freshly built `aspis-r1-cost-probe` with defaults plus
`prover,optimized-terminal`, including `aspis-prover`, `aspis-core/r0` and
`aspis-statement/r0,pool-v1-kernel`, on **x86_64-unknown-linux-gnu**.
Native rustc1.94.1/LLVM21.1.8 is explicitly distinct from the SBF compiler.
The optimized build used offline locked dependencies and j2 in an admitted
6G/8G/Swap0/Tasks64 scope. Cargo.lock SHA256 remained
`5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
391 native-source `.rs`/`.toml` hashes match frozen Git bytes exactly, with zero
mismatches: [NDC_NATIVE_SOURCE_CHECK.json](NDC_NATIVE_SOURCE_CHECK.json).
No prover execution, rank computation, soundness gate or privacy proof ran.

[NDC_NATIVE_SYMBOLS.json](NDC_NATIVE_SYMBOLS.json) gives per-library native
symbol membership and library hashes; raw `nm` outputs are retained.
All 31 non-generic/non-encoder identities have named emitted native bodies.
The two generic families are also emitted in native libraries, with different
monomorph hashes; exact SBF-to-native generic-instance equivalence is not claimed.
NDC_B008 exposes both native M31 and QM31 `EncodingDomain::encode` LLVM
instances plus generic MIR: [NDC_NATIVE_GENERIC_HEADERS.json](NDC_NATIVE_GENERIC_HEADERS.json),
[NDC_NATIVE_EMIT.json](NDC_NATIVE_EMIT.json). Thus **all34 source families are
also compiled in client/prover libraries**, with the two generic-instance caveats.
That does not establish which bodies survive a particular final client binary's
link, or whether an honest/private proof generation path executes each one.
The x86-64 stack does not have SBF's 4096-byte per-frame limit; no native privacy
or total-stack-safety conclusion follows from this SBF warning analysis.

## Recommendation and retained boundaries

No change to the three frozen programs is indicated **for these34 warnings**:
the warning-producing library instances were eliminated. This is stronger for
this question than finding a reachable fail-closed body, and different from
claiming every warning is class(a). Retain the diagnostic/linkage evidence in
the P7/S10 release packet. Keep compiler/linker semantic preservation, runtime
admission/ABI/memory, SDK/std assumptions and all source/model/security joins.
No assumption was discharged, added or reclassified. S2 and the100-bit per-attempt
release target are not established by this analysis.

The remaining runtime-pin obligation is explicit: a future unconditional
live-runtime gap claim needs the validator executable/source pin, execution
budget, SBPF build features and active Agave feature set. It cannot be recovered
from an ELF alone. This uncertainty does not require a P7 qualification for
code that is absent. No deployment, RPC, transaction, key or account operation
occurred. The only network transport was authorized SSH/SCP to the build host.
'''
(E/'NDC_STACK_FINDING.md').write_text(text)
(E/'NDC_TABLE.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Wrote',len(rows),'per-function/per-ELF rows')
