# NMN cut map under (bl)

Target not yet established; ledger24 baseline 581/0/18. Frozen candidate.rs327–331.

| Call | Recorded arguments | Reply / havoc | Closed Lean root |
|---|---|---|---|
| parse_shape(proof) | proof pointer/length through proof allocation's harness-local UnsafeCell context; both alternate allocations have the same valid layout | all 3 Variant successes and all 8 deployed Error variants; no &mut arguments | NLE_ParseInstall.parse / success |
| mark(None,Parsed) | Parsed asserted in exact-signature cut; deployed None is literal in parent call | unit; no &mut arguments | NHV_ReleaseOps.mark |
| tx2_common(public,proof,checkpoint,hash,None) | pointers/lengths through H's already-received local data pointer | full Result<(),Error>; no &mut arguments | NLT_CompleteRoot.root |

Planned native relation: actual parent returns parser Err unchanged, otherwise common reply unchanged; same arguments at each reached call; no parent account writes or return-data emissions between calls. All buffers retain original allocations and arbitrary bytes at 1880/57607/1768. Parser response is independent of buffer contents in native cuts; its CLOSED law is instantiated later in Lean.

## (bl)(4) classifications

- The common child's internal allocations are fresh. Allocator internals are excluded under (bl)(3), with existing allocator/std trust retained. No four-cell substitute heap is a certificate.
- Child internal digest/return-data events are passed through as an opaque ordered child stream. The parent has no such event between the three calls. Common's exact stream comes from NLT, including C04 stopped prefix.
- A stopped child is nonreturning panic with its prefix only. No returned Result, cleanup, post-abort heap or suffix is claimed. SBF's absence of catch means no extra propagation fact is required by (bl)(3).
- No &mut formal arguments occur in any of the three signatures. The required byte havoc set is therefore empty at this parent boundary. Harness-local logs are instrumentation, not fabricated account state. Controls must still check a deliberately added observable write rather than calling four artificial cells the common footprint.
- Observer is deployed literal None. No function-pointer comparison, arbitrary callback, writable static or Option<fn>-dependent success claim is admitted. Marker phase is checked without inspecting an Option value.
- 57607 follows from SAME successful parse. Public<=1880 and Root0 concern 064's own inputs and are recorded as 241 caller clauses. NMF supplies the accepted headline occurrence outside the existing charged collision event, never an unrestricted failed-prefix fact.

The064 entries passed native controls and worker gates L015–L021; ledger promotion is pending.241 entries below remain diagnostics.

## Native domain completeness classification

The native certificate uses original57607/1768 proof/checkpoint allocations. NMN_064.Domain explicitly records those exact extents, public<=1880 and Root0 as064 OWN-input predicates under(bf)(2). No all-length native claim is made.241 must discharge both exact extents from SAME getter/checked_add/range facts (NLW_StartScope/NLM_ReadExtent) and public bound from encoder1880. Parser success independently implies57607 at the common call. These clauses are never endpoint or success hypotheses. All original bytes are arbitrary, including malformed headers.

## Current native receipts

K014/K015 PASS on actual parent returning/rejection paths. K016/K019 ignored-reply controls FAIL; K017/K020 alternate-allocation argument controls FAIL; K018/K021 required local-log write omissions FAIL. K022 common panic branch reaches the intended panic (not a passing-return theorem);(bl)(3) provides no-catch propagation, retaining only child prefix. K023/K024 stability PASS/FAIL agrees with original names. K025/K026 canonical exact KMX pointer checks PASS/FAIL. All13 runs have identical current parent/stub source hash in NMN_CONTROLS.json. No writable static, function-pointer value assertion, field-product proof, own copy stub, or claimed post-abort world.

Parser log is reached through its ORIGINAL proof allocation's data pointer: NMN_Frame contains an UnsafeCell local record preceding the proof subobject; subtracting the known field offset stays inside that same allocation. Both normal and alternate control frames have this layout. The shared proof slice never overlaps the UnsafeCell log. Pointer/length assertions occur after return. Common logs the exact three original slices through the received generic H data pointer. Marker has unit reply/empty footprint; its Parsed argument is checked at the exact-signature cut. The deployed literal None is fixed syntactically and never compared; NMN_Observer supplies the erased model phase law.

## 241 independent work (not a certificate)

NMN_241ValueFold quantifies the full Aeneas242 Result/ValidatedAsqa value and instantiates it at the SAME source call; its source theorem at the named headline installation compiles. It is expressly a value/control component, not a full242 packet or full241 fold. NMN_242Interface separates returned full typed values/world/events from stopped prefix/pending, with no post-abort world.

The first native241 experiment covers validate_asq8 returning Err, with all26 deployed ProgramError variants constructed safely (Custom payload arbitrary; BorshIoError payload one arbitrary ASCII character). Input owned-account buffers are empty/unread on this branch, slot is Ok. These are explicit DIAGNOSTIC restrictions, stronger than the full caller domain; they are a finding under rule D, not native241 credit. General String payloads, original owned buffers and Ok(ValidatedAsqa) still require work. No bounded String model may silently become a full-type packet.

A fresh-allocation channel is being tested for the Box statement returned by242: a cfg(kani)-only stateless GlobalAlloc adds per-allocation LOCAL UnsafeCell owner cells and retains its own allocations until scope exit. No static is written and no other worker's allocation, directory, cache or runtime is touched. This is an unvalidated harness experiment, not new allocator trust. It cannot be cited unless allocator support, real typed constructors and matched controls pass; allocation internals/ordinary non-observable cleanup are classified under(bl)(3), never actual account/return-data writes.

Allocator isolation after K028: the Box::new header back-step failed provenance. Direct NMN_Allocator.alloc and Box::new are tested separately before any parent use. A proposed direct-allocator Box::from_raw uses a real initialized typed value and its actual selected global allocator; deallocation alone is stubbed to retain fresh harness-only instrumentation under(bl)(3). This is NOT a statement about allocator internal equality, post-abort heaps, account writes, SDK counters or keys. These stubs have no body memory write and are not copy or field stubs. Full native controls and typed validity remain required; no credit is inferred from pointer integers alone.

K029 direct allocation PASS; K030 omitted header-owner write and K031 corrupted scalar payload FAIL their semantic checks. K032 repeats the Box::new provenance failure on u64, isolating the mismatch from statement size. K033 direct typed allocation + Box::from_raw + retained nonobservable deallocation PASS; K034 omitted owner FAIL. This validates that limited constructor/channel, not Box::new or241. The next parent experiment replaces only the oracle's safe initialized Box construction with that validated path and keeps the original NMN_241_box_constructor name. Its full statement constructor is arbitrary over both enum variants/all scalar fields; its account-buffer/slot class remains diagnostic, not a full241 packet. Allocation failure still stops before any reply. No account/return-data effect is erased.

K038 non-String union PASS on actual241; K039 reply, K040 argument, K041 required local write controls FAIL as intended. This covers all25 non-String ProgramError variants (Custom u32 arbitrary) in the explicitly restricted input class. Box constructor stretch now cuts the two diagnostic empty getters and all unexpected suffix calls; no whole-input-buffer, full242 packet or241 credit is inferred. These cuts isolate constructor/checked_add propagation from callee expansion and prevent cryptographic unwinding.

## Further241 allocation isolation
K058: CBMC139 on raw full-buffer parent. K059: arbitrary Box proof-buffer isolated constructor reached outer180s guard without verdict. K060: zero-initialized fixed-window proof-buffer constructor also CBMC139. Each is retired, earns no native credit, and is retained with its original source snapshot. The replacement does not claim full arbitrary buffers: only one initialized fixed byte is arbitrary and the remaining bytes are zero. The spare-capacity owner cell is a fresh LOCAL UnsafeCell outside every logical shared slice; no account/return-data write is erased. A smaller checkpoint constructor is an independent size isolation, not an unchanged proof-buffer rerun.

K061 checkpoint fixed-window PASS / K062 corruption FAIL. K063/K067 Unicode-scalar242 rejection/clock-error input PASS with reply/argument/write controls K064–66/K068–70 FAIL. K071/K073/K075/K079 count/short/magic/clock-error guards PASS with K072/K074/K076/K080 semantic negative controls FAIL. K077/K078 exact KMX copy PASS/FAIL on the SAME final program source/configuration. These partitioned guard/String/constructor checks are diagnostic only, never full241 or242 packets. Full unbounded String and arbitrary full account buffers remain open.

Harness bodies are delivered only in NMN_HARNESSES.patch (hash sidecar); full historical source inputs are content-addressed receipts. Own runners reconstruct only added artifact files and verify each hash in NMN_HARNESS_SOURCES.json. Frozen source/feature/lock/offline checks are unchanged or stricter. Raw development .rs files have been removed from the final repository tree; compiled scratch originals remain retained on the host.
