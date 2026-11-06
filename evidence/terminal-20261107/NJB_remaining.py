from pathlib import Path
import json,lzma
E=Path(__file__).resolve().parent;rows=json.loads(lzma.decompress((E/'NJB_OBLIGATIONS.json.xz').read_bytes()));ledger=json.loads(lzma.decompress((E.parent/'ledger13-20261107/NIU_LEDGER.json.xz').read_bytes()));byfun={r['function']:r for r in ledger['rows']};ours={r['function']for r in rows}
reasons={
208:'K044/045 proves deployed forwarding identity, but209 still lacks the single positive native-cut composition root; cannot discharge the callee clause with model equality alone.',
209:'High64/low7 raw induction, exact masks, full reference/cohort Result and seven native partitions exist. Need native low trace/cut discharge and the complete source-ordered high+low invocation root, including initialization/counters/abort frames.',
214:'Full103-cell endpoint shape K072 timed out. Split genuine136-link lookup and one-cell add pass/control; need both source writes and binary-weight Result joined at the proved disjoint indices with full103-cell frame and caller binary-weight provenance.',
215:'Native17-operation record and full emitted value Result exist; instantiate every same-argument actual field Result through the typed residual cut in one root, rather than leave trace binding as prose.',
216:'Read/raw-add/reduce windows, exact U64 product law and symbolic at-most-four bound exist. Need frozen272-term/31-offset registry association and inner/chunk/limb/outer native-step induction to the cohort, including partial last chunks and final four-word constructor.',
217:'Deployed function forwards to216. Root cannot discharge its child until216 is CLOSED. Nondeployed scratch-index arm is not substituted for the deployed dot arm.',
218:'Requires composed endpoint/selector tensor finish220 and pattern223 packets (plus their caller domains); native source-order parent cuts and all early abort prefixes are unfinished.',
219:'Inner and outer native windows and complete four-cell raw fold Result exist. Need full typed outer invocation cut, same-array state/frame composition, and association to the adopted pattern-basis meaning.',
220:'Finish tensor needs219, tag-coordinate217 and the dot dispatcher225. The latter reaches OPEN out-of-slice field helpers. Parent root and rejection/loop frames are unfinished.',
223:'Deployed windowed child224 is unfinished; remaining literal/selector parent meaning must use the actual selected feature arm, not the old emitted helper name.',
224:'Native power/callback/window/tail observations are attempted separately. Need powers8 and actual prepared-array map association, four SAME windows, complete14-output composition and retained pattern-model equality. Callback-slot prototype alone does not establish Std array::map.',
225:'SLICE BOUNDARY: counts2/3/4 call field::qm31_sum_products2/3/4, baseline TX1:040/041/043 OPEN outside this job. Do not author their proofs or replace products with an unpaired oracle. Count1 uses the closed multiplication law; other arms prevent the whole dispatcher closing.',
227:'Full16-array raw reference/cohort Result and actual9-word native prologue/lane records exist. Need the single positive root consuming all typed prologue/lane/array-construction cuts with complete frames. Reduced-token K016–019 is excluded.',
228:'Requires occupancy244 and full preweighted/shared231 call Results at their same actual arguments, plus source-ordered lane-adder cuts. The generic CLOSED add_preweighted230 alone does not supply the optimized factored caller.',
229:'Requires path247 and the preweighted/shared caller-domain composition, with mutable packed-state and abort frames.',
231:'Deployed N33/start49 gather/group/control passes and full24-state reference exist; need complete typed cuts, same-array carrier, selector-pack distributivity instantiated against the adopted add_preweighted/selected contribution meaning.',
232:'Requires add_occupancy228, add_path229 and add_value233 (and any actually selected parent branches). Native parent cuts and full Result/early-abort frames remain unfinished.',
233:'Requires deployed shared-selector231 with N33/start49, same input packing/value lanes and complete packed-state frame. Reference-only231 is not a CLOSED callee.',
234:'Independent leaf was extracted with the common batch but no new Lean body emitted. Still needs native append-level branch, empty_root239/lift243/pack039/prepared/m31-tweak clauses on their actual domains, two returned arrays and the level<20 caller fact. No external open callee is invented.',
235:'Requires234, then one actual append-level iteration over the SAME frontier/opened/powers arrays and Lean finite level induction, full returned/mutable state and reject prefixes.',
237:'Requires semantic_packed261 and terminal/base composition children; no root may assume those successful Results or an endpoint equality. Complete source-ordered cuts and return-state assembly are missing.',
242:'K054 timed out; K060 timed out and also interleaved the global order. Both excluded. Atomic residual and pack/prepared windows pass/control; need all eight subtractions before both products, constructor/array-return cuts and exact full cohort Result.',
244:'Independent context/head/arbitrary-lane/tail native windows use the actual prepared type and no bit assumption. Need typed-cut composition, finite digest-lane induction and equality to the retained occupancy literal, including all12 outputs.',
245:'Branch-only observation can establish carry<20 versus zero and exact callback payload/reply. True-body arithmetic/copy cuts must still compose all residuals/products and full2-array Result; do not treat the opaque body reply as a proved child.',
246:'Option<Digest> branch-only observation is not Option<fn> and uses no function contracts. Still need actual Some-body constructor/group loop induction, zero None branch and full two-array source/model Result.',
247:'Prologue passes/control. Combined left/right K082 timed out; split one-side windows are attempted separately. Need all eight unrolled pair blocks composed with actual same caches, head bit residual, complete17-cell frame and retained path meaning; arbitrary canonical bit is allowed.',
250:'Requires public_digest_packed_selector_tensor251 and digest helpers including242/245/246 at the SAME public values. No acceptance-only or guessed output premise is allowed.',
251:'Requires packed helper rows242/245/246 and their actual caller domains, plus all unchanged CLOSED semantic/append children. Complete branch/state cuts remain unfinished.',
260:'Requires initial/absorption child227/228 plus actual selected public/claim domains and source-order composition. Root abort prefixes and full returned packed array are unfinished.',
261:'Requires schedule232, values233, levels235, public digest250 and initial/absorption260 as selected by deployed features. Cannot replace those child Results with hypotheses.',
263:'Requires composition_parts237 and actual equality/terminal children. Parent native invocation and full Result/early-error frame remain OPEN.',
268:'Sole unconditional getter candidate: full typed variant/borrow identity and complete cohort Result, no hypotheses beyond typed input. Local combined/raw/scan gate and then next authoritative ledger gate determine admission; enclosing codec/native interpretation obligations remain.'}
s=['# NJB remaining obligations','', 'Target not established. All32 explicitly listed occurrences are retained; TX1:256 remains NIX-owned and is not touched. Authoritative baseline stays432 CLOSED /0 QUALIFIED /167 OPEN until a new ledger replay.','', 'The terminal budget/attempt totals are in NJB_AUDIT.json. No unspent allowance in one resource can turn an unfinished Lean/cut/caller obligation into a CLOSED row. No timed-out or killed native shape is replayed unchanged, no cap/timeout is raised, and no outside-slice field helper is authored.','']
for r in rows:
 n=int(r['row'].split(':')[1]);s+=['## '+r['row']+' '+r['function'].split('::')[-1], '',reasons[n],'']
 own=[byfun[c]['row']for c in r['canonical_callees']if c in ours and c in byfun]
 boundary=[(byfun[c]['row'],c)for c in r['canonical_callees']if c not in ours and c in byfun and byfun[c]['status']!='CLOSED']
 if own:s+=['Real in-job child occurrences: '+', '.join(own)+'.','']
 if boundary:s+=['Open slice boundaries: '+ '; '.join(a+' '+b for a,b in boundary)+'.','']
(E/'NJB_REMAINING.md').write_text('\n'.join(s))
print('member-by-member remaining obligations recorded for32 rows')
