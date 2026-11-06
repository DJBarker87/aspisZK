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

K019/K020 owned chain own-input compile errors: trailing comma injection and
non-Copy PDA reply; repaired in call parser / explicit Clone. K021 setup copy
unwind failed; zero-copy Box-slice into_vec setup replaced it (same arbitrary
owned payload). K022/K023 V1 PASS/intended assertion FAIL. K024 full V2 TIMEOUT;
K026/K027 registry half and K028/K029 entry half PASS/intended FAIL, same caps.
K025 complete lane invocation TIMEOUT, retired. K030/K031 initially restrict
length to1, so no credit for metadata beyond the checkpoint gate. K032 expanded
whole metadata TIMEOUT; K033/K034 front and K035/K036 owners halves pass with
intended controls. K037 combined lane suffix TIMEOUT; split by field. K038
scalar PASS but K039 control TIMEOUT: no paired credit. K040/K041 root,
K042/K043 frontier and K044/K045 owner have matched assertions per strict
NLK_validate_native.py. Exit1 alone is NEVER a matched control; the queue's
initial exit-only check was insufficient and is superseded by that validator.

L005/L007 source-support drafts fail only on missing namespace import / let
unfolding; L008 passes. L013 adds the returned-Err Drop lemma. L014 rebuilds
DriverFold because that direct dependency changed; not an unchanged regression.
L012 PDA-domain draft had finite-list proof syntax errors; L015 corrected,
L016 concrete site domains and L017 actual-owner suffix allocation law pass.

Stage 3: native allowance exhausted at K060. Strict stdout validation reports
26 passes and 26 matched assertion failures; five timeouts, two compile/gate
rejections and one unwind failure receive no credit. Expanded lane and V2
shapes were split after timeout; no timeout/cap increase. K039 timeout is NOT
a passing negative control; K046's changed result-mutation control pairs K038.
L018..L042 develop original-input lane header, digest, literal empty table,
per-occurrence loop, complete conditional invocation/allocation schema and
concrete registry callee installation. L041 had local decidability/name errors;
L042 repairs them and prints only standard axioms. No row promotion.

Stage4 semantic source commit256baac6480:25 current modules,95 public theorem
roots. L054 combined import exits0 (19.67s,6493068KiB,swap0); fixtures L055
exit0. The one full extended audit imports ledger21+NLA+NLF with the deployed
headline and traverses11035 roots in31 groups. Eight completed groups have
exit0; audit peak so far6780468KiB,swap0. Resource review: this is explicit
final axiom traversal, not arithmetic normalization; every group emits new
root results. Focused predecessors are green. No cap/timeout is raised and no
unchanged full regression is repeated. Final counts/verdicts supersede this
in-progress note in NLK_AUDIT.json.

Stage5 audit gate: first30 raw batches cover10720 inherited roots. L086's
missing-import finding is retained without partial credit; L087 adds NLF's
combined module and L088 rechecks315 added roots plus headline/known finding.
Only the known NHC_DecodeModel.decoder_error collector disagreement remains.
NFX scan L091 exits0 (51.39s,7740184KiB,swap0); closure pins L092 exit0
(37.01s,131380KiB,swap0), with no inherited object/sidecar mismatch. One full
raw traversal, two combined imports and one import-repair delta recheck; no
second unchanged full manifest replay. L085's allowed:false admission was
waited out and allowed:true/exit0 obtained before launch. No row promotion.
