# NJN retained failed steps

Target not yet established. No rejected receipt is a certificate.

* L001: Charon exit 0, Aeneas exit 2, InterpBorrows.ml:2731 on
  NJN_reference.rs line 23 (guard drop's same-cell counter branch).
  All twelve roots were supplied in the single extraction. No Lean output.
  One authorized extraction consumed; no rerun or tool modification.
* K001–K004: compiler E0597 in the wrong-cell control: both AccountInfo
  arguments unnecessarily shared the payload lifetime. No semantic verdict.
  Corrected the control to quantify the two accounts' payload lifetimes
  independently; K005–K008 use the corrected source and unchanged properties.
  The initial queue incorrectly continued after compile rejection; later queues
  stop on missing VERIFICATION, and all four rejected attempts count as spent.
* L003/L004/L005/L010: own record-layout/parser and frame simplification
  errors. Failed output contains elaborator sorryAx placeholders and is EXCLUDED.
  No source contains sorry/admit/axiom. L012 replays the repaired complete file.
* L008: simplifier normalized the numeral before matching symbolic hypotheses.
  Replaced broad simp with exact if_pos/if_neg rewrites; L011 passes.

The native SDK contracts currently target exact one-call wrappers, not attributes
on registry methods. They preserve actual typed Ref/RefMut across the call and
exercise actual Drop. This distinction and the bounded constructed prestate
remain explicit; no universal SDK substitution certificate is claimed.

* K009: own cfg-erasure checker rejected reversed sidecar registration order;
  no Kani process started. Reordered the two sidecars to match suffix erasure;
  the validation remains byte-exact, and K010 reached Kani.
* K010/K011: full u64 ProgramError conversion and its original mutation timed
  out at 90s. No credit; split into builtin, custom and Borsh coordinate shapes.
* K014/K015: KMX typed guard-array prestate timed out. K015 was already submitted
  as the matched mutation when K014 was reviewed. An owned local prelaunch
  interlock blocked K016 before admission, then the array was replaced by
  straight-line fixed-count safely constructed guard states; no cap/time raise.
* L015 preflight: own copied config named cleaned NJK_objects rather than its
  retained export. No Lean process started. Added the exact NJK retained export
  to LEAN_PATH and submitted L015 normally; imported objects are pinned.
* L016: own native C output directory was absent. Added its creation to the own
  uploader; L017/L018 compile the drivers without changing their audit logic.
* L024: own multiline record-expression parser error. L025 compiles the fixed
  KMX copy-induction consumer; rejected placeholders are excluded.
* K020: first builtin mutation (which constructed and dropped the full actual
  error before replacing it) timed out. Changed only the mutation to corrupt
  the returned error directly; K021 is a semantic FAIL. This is a new mutant,
  never an unchanged rerun or a renamed target.
* K024: proof-for-contract on the Borsh String carrier coordinate timed out;
  no credit. Any later direct one-coordinate native interface is explicitly
  separate support and cannot stand in for that contract proof.

NJN-F1: native wrapper contracts so far are not full f_ref equality contracts.
The guard partitions use two-byte payloads with safely constructed live guards,
not every admitted three/seven-account heap; their postconditions do not encode
the entire owned-reference frame. They must not be applied at stronger caller
inputs. Full typed SDK substitution and arbitrary payload/handle frames remain
OPEN. Extra partitions do not change this classification. The exclusive-copy
window and large-payload error prestate are separately scoped evidence.

NJN-F2 (specification limit): Live is a LOCAL token/counter predicate, not the
full ownership ledger invariant. Two distinct token indices can both contain
an exclusive Guard for the same cell at counter -1 and each satisfy Live.
Such a heap cannot represent two valid simultaneous unsplit RefMut owners.
The Rust reference's public carrier fields likewise permit constructing invalid
specification states unless a global validity domain is supplied. The current
model laws are equations for those explicit transitions, not a consistency or
SDK-validity theorem. A successor must state and prove the global unique-token /
shared-count correspondence and admissible moves; it must not use local Live
as the full library interpretation. This is an additional missing obligation,
not a problem solved by rerunning extraction alone.

NJN_PROPOSED_EXTRACTION_REPAIR.patch only outlines the failing drop assignment
into before/after locals, ending the read before the mutable indexed write.
It is NOT applied to the pinned extracted input and has NOT been tested or
extracted. It is a concrete next candidate, not a claim that the extractor
accepts the rest of the twelve-root job. Global validity/frame work remains.

* K016: the 58295-byte exclusive-conflict proof-for-contract interface timed
  out. K017 then isolated an inline local-record error cut (same original
  target name), which also timed out. Both are excluded; no increase or retry.
  The queued controls were not submitted on those timed-out interfaces.
* K068/K070: a DIFFERENT, direct Borsh byte-window interface passes/fails as
  intended. The original K024 contract remains OPEN; no name was changed to
  obtain a verdict and no contract credit is inferred from the direct check.
* K018/K069: independent actual Clock::default output initialization contract:
  all five fields equal clock_ref(0,zero); native size40/alignment8 and an
  arbitrary output byte is zero. Slot corruption is a semantic FAIL. This is
  initialization support, not Clock::get's syscall/reply/frame association.
* Own orchestration hygiene: failed formal excerpts are now JSON-escaped to a
  single line. Validation is unchanged. Exact raw host bytes were recovered for
  all202 stdout/time logs; no normalization correction or prover rerun needed.
