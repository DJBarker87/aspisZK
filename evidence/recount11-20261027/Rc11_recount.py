"""Read-only recount from fresh kernel inventories; no proof or adoption."""
from pathlib import Path
from collections import Counter
import copy
import difflib
import hashlib
import json
import re

E = Path(__file__).resolve().parent
R = E.parents[1]
BASE = R / 'evidence/recount10-20261026'
norm = lambda s: re.sub(r'\s+', ' ', s).strip()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def save(name, data):
    (E / name).write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')

b = json.loads((BASE / 'Rc10_premises.json').read_text())
fresh = (E / 'Rc11_002/stdout.log').read_text()
assert 'error:' not in fresh
boundary = (E / 'Rc11_003/stdout.log').read_text()
assert 'error:' not in boundary
for name in ['P1Realization', 'RuntimeSyscall', 'Agrees', 'Consistent',
             'admittedMean', 'chargeOn', 'StoredCarrierBinding', 'failureModel',
             'total', 'collisionLoss', 'accountLoss', 'margin', 'maxQueries']:
    assert name in boundary, name
attempts = [json.loads(p.read_text()) for p in sorted(E.glob('Rc11_*/receipt.json'))]
assert len(attempts) == 3 and all(a['exit_status'] == 0 for a in attempts)
wall = sum(a['wall_seconds'] for a in attempts)
peak = max(int(a['peak_rss_kib']) for a in attempts)
assert norm((E / 'Rc11_BEFORE.lean.txt').read_text()) == norm((BASE / 'Rc10_AFTER.lean.txt').read_text())
# Each printed definition/type/proof must recur verbatim modulo whitespace.
# Deduplicated directives can make an old module's output non-contiguous.
split = r'(?m)(?=^(?:structure |def |theorem |@\[|@Aspis|\x27Aspis|AspisR1\.))'
inventories = []
for module in json.loads((E / 'Rc11_inventory-plan.json').read_text()):
    receipts = []
    for p in BASE.glob('Rc10_*/receipt.json'):
        d = json.loads(p.read_text())
        if d['exit_status'] == 0 and module + '.lean' in d['sources']:
            receipts.append(p)
    assert len(receipts) == 1, module
    old = receipts[0].parent / 'stdout.log'
    blocks = [x for x in re.split(split, old.read_text()) if x.strip()]
    assert all(norm(x) in norm(fresh) for x in blocks), module
    inventories.append(dict(module=module, retained_output=str(old.relative_to(R)),
                            sha256=sha(old), blocks=len(blocks), fresh_match=True))
save('Rc11_inventory-check.json', inventories)

before_src = (R / 'lean/Rc10_Top.lean').read_text()
after_src = (R / 'lean/ARX_Root.lean').read_text()
before = before_src.split('theorem deployed', 1)[1].split(' := by', 1)[0]
after = after_src.split('theorem deployed', 1)[1].split('\n := by', 1)[0]
# Verify the entire statement, not just selected constants or visible binders.
expected = before.replace(
    '(D : LiteralByteProtocol.Decoder) (P : F3T_ByteCarrier.ByteProver) (Q0 Q1 : Nat)\n'
    '    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)\n'
    '    (runtime : F3T_Runtime.Runtime)',
    '(D : LiteralByteProtocol.Decoder) (a : SCE_Experiment.Adversary A) (Q0 Q1 : Nat)\n'
    '    (queries : ∀ H : Bytes → State,\n'
    '      (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)')
expected = expected.replace(
    '    (binding : F3T_Runtime.StoredCarrierBinding\n'
    '      (FIp_Install.configuration indexError c reservation) D\n'
    '      (F3T_Installed.source (FIp_Install.configuration indexError c reservation) hashv) P runtime)\n', '')
expected = expected.replace('    let select :',
    '    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;\n'
    '    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c indexError reservation native1 native2 hashv a;\n'
    '    let select :', 1)
assert expected == after
assert before.split('    let select :', 1)[1] == after.split('    let select :', 1)[1]
(E / 'Rc11_statement.diff').write_text(''.join(difflib.unified_diff(
    before.splitlines(True), after.splitlines(True), fromfile='Rc10_Top.deployed', tofile='ARX_Root.deployed')))
save('Rc11_statement-check.json', dict(
    full_source_statement_whitelist_match=True, fresh_Rc10_kernel_matches_retained=True,
    conclusion_from_select_byte_identical=True,
    source_before_sha256=sha(R / 'lean/Rc10_Top.lean'),
    source_after_sha256=sha(R / 'lean/ARX_Root.lean'),
    literal_kernel_types_identical=False,
    reason='ARX specializes P and runtime to defined terms and rewrites the same L154 budget using ARW_Induced.queries. No direct application of Rc10 is asserted.',
    constants_carrier_types_event_constructor_conclusion_schema_changed=False,
    runtime_argument_changed=True, prover_argument_changed=True,
    global_unfiltered_mean_equality_claimed=False))

removed = {'L159', 'L181', 'L185'}
assert {r['id'] for r in b['rows'] if r['id'] in removed} == removed
rows = copy.deepcopy([r for r in b['rows'] if r['id'] not in removed])
for r in rows:
    r['Rc11_evidence'] = 'Rc11_001 complete roots; Rc11_002 fresh expanded families; Rc11_inventory-check.json'
    if r['id'] == 'L154':
        r['Rc11_specialization'] = '∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1'
        r['Rc11_equality'] = 'ARW_Induced.queries at P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a'

def tally(rs):
    return dict(rows=len(rs), classes={c:sum(r['classification']==c for r in rs) for c in 'TPGC'},
        owners={o:{c:sum(r['classification']==c and r['owner']==o for r in rs) for c in 'TPGC'}
                for o in ['external','session A','lead']})
def totals(rs):
    return {s:tally([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']} | {
        'deployment-inclusive non-alias':tally([r for r in rs if r['scope']!='deployment alias'])}
bt, at = totals(b['rows']), totals(rows)
assert bt['actual antecedent']['classes'] == dict(T=83,P=12,G=13,C=0)
assert at['actual antecedent']['classes'] == dict(T=83,P=11,G=13,C=0)
assert bt['deployment-inclusive non-alias']['classes'] == dict(T=89,P=16,G=13,C=0)
assert at['deployment-inclusive non-alias']['classes'] == dict(T=89,P=14,G=13,C=0)
diff = []
for r in b['rows']:
    diff.append(dict(id=r['id'], name=r['name'], classification=r['classification'], owner=r['owner'],
        scope=r['scope'], meaning=r.get('meaning'), definition=r.get('definition'),
        disposition='absent' if r['id'] in removed else ('specialized, same atomic family' if r['id']=='L154' else 'unchanged'),
        counted=r['scope']!='deployment alias'))
save('Rc11_premises.json', dict(
    before_theorem='AspisR1.Rc10_Top.deployed', after_candidate='AspisR1.ARX_Root.deployed',
    adopted_theorem_unchanged=True, baseline_sha256=sha(BASE / 'Rc10_premises.json'),
    method=b['method'], before=bt, after=at, rows=rows,
    removed=['L159','L181'], removed_aliases=['L185'], added_atomic_rows=[], reclassified=[],
    actual_delta=dict(T=0,P=-1,G=0,C=0), deployment_inclusive_delta=dict(T=0,P=-2,G=0,C=0),
    adopted_delta=dict(T=0,P=0,G=0,C=0), aliases_before={'L185':'L159'}, aliases_after={}))
save('Rc11_row-diff.json', diff)

lines = ['# Rc11 mechanical recount', '',
    'Candidate `AspisR1.ARX_Root.deployed` is proved and remains unadopted. '
    'Actual adopted root: `AspisR1.Rc10_Top.deployed`. No proof was added. '
    '**The deployed 100-bit target is not yet established.**', '',
    'The complete fresh kernel types are [before](Rc11_BEFORE.lean.txt) and '
    '[after](Rc11_AFTER.lean.txt); the named ARX declaration and full axioms lines '
    'are in Rc11_001/stdout.log. Rc11_002/stdout.log reprints all 44 Rc10 inventories '
    'and expands the changed account/runtime definitions. Every retained printed '
    'block matches modulo whitespace (Rc11_inventory-check.json).', '',
    '## Counting method', '',
    'One row is one quantified atomic law family. Split conjunction leaves; '
    'preserve shared existentials, SAME returned execution witnesses, implication '
    'guards and installation slots. Do not multiply a Fin22 law into 22 rows. '
    'Count conditional finish laws even when hidden in returned continuations. '
    'Native-local L142–L146 and source-global F3Y_G_L142–L146 are ten independent '
    'families. Returned facts are not assumed premises. Data-only fields are '
    'inventoried below and add no atomic law. T=adopted external trust; '
    'P=proof/budget condition; G=approved game/accepted-event clause; C=vacuity-suspect. '
    'Owner means accountable cone, not completed work.', '',
    '## Fresh side-by-side totals', '',
    '| Basis | Rc10 T/P/G/C | ARX candidate T/P/G/C | Delta |',
    '|---|---|---|---|']
for scope in bt:
    def fmt(t): return '/'.join(str(t['classes'][c]) for c in 'TPGC')
    delta='/'.join(str(at[scope]['classes'][c]-bt[scope]['classes'][c]) for c in 'TPGC')
    lines.append(f'| {scope} | {fmt(bt[scope])} | {fmt(at[scope])} | {delta} |')
lines += ['', 'Raw and distinct counts coincide within each root after excluding '
    'deployment alias L185=L159. Raw totals including that alias are '
    '89T/17P/13G/0C before and 89T/14P/13G/0C after: −3 raw P rows but '
    '**−2 distinct P families**. Independent runtime/P data binders earn no P '
    'deletion credit. Actual adopted delta is **zero**.', '',
    '| Owner (deployment-inclusive, non-alias) | Rc10 T/P/G/C | ARX T/P/G/C |',
    '|---|---|---|']
for o in ['external','session A','lead']:
    vals=lambda ts:'/'.join(str(ts['deployment-inclusive non-alias']['owners'][o][c]) for c in 'TPGC')
    lines.append(f'| {o} | {vals(bt)} | {vals(at)} |')
lines += ['', '## Every row absent from the candidate', '',
    '| Row or binder | Before | After | Class/owner/count |', '|---|---|---|---|',
    '| L159 `binding` | `F3T_Runtime.StoredCarrierBinding ... P runtime`: entire accepted runtime run equals canonical annotated installed-source experiment | No root hypothesis; admitted account observer and derived charge domination | P, lead, −1 actual |',
    '| L185 | Deployment alias of L159 | Absent with L159 | P, lead, alias only |',
    '| L181 | Residual experiment/native-prefix and ordered-query association | Account/admitted query and rejected-prefix transport composed | P, lead, −1 deployment |',
    '| `runtime : F3T_Runtime.Runtime` | Independent data argument | Defined `ARX_AdmittedRuntime.runtime ... a` | Data-only experiment binder, lead; 0 atomic rows |',
    '| `P : F3T_ByteCarrier.ByteProver` | Independent data argument | Defined `ARW_Induced.program ... a` | Data-only experiment binder, lead; 0 atomic rows |', '',
    'L181 credit concerns the admitted experiment/native-prefix association only. '
    'It does not establish source-to-ELF correspondence or L166 complete native '
    'Result/effects fidelity. L166, L187 and L188 remain P. This is no global '
    'exact frozen2 log equality claim.', '',
    '## Every candidate-only or specialized binder', '',
    '| Exact binder | Definition/classification | Atomic addition |', '|---|---|---|',
    '| `a : SCE_Experiment.Adversary A` | Arbitrary data, game-role (lead), fixed before H. Fields: `first : Program Bytes State (FirstInputs A)` and `second : FirstInputs A → Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A)`. No Prop law fields. | 0 T/P/G/C |',
    '| `let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a` | Defined ByteProver; data-only game specialization (lead). Retains both reached adversary phases; returns original first submission. | 0 |',
    '| `queries : ∀ H : Bytes → State, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1` | L154, P/external, unchanged budget family at induced P by `ARW_Induced.queries`; Q=Q0+Q1 is an upper bound, not exact per-path work. | 0 |',
    '| `let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c indexError reservation native1 native2 hashv a` | Defined admitted-image observer; data/game definition (lead), not a trusted universal support premise. | 0 |', '',
    'There is no independent Q function binder in ARX. `Q0 Q1 : Nat` are retained '
    'verbatim. The induced-P/issued-Q relationship is the printed theorem '
    '`ARW_Induced.queries`. Labeling data as game-role does not invent extra '
    'class-G atomic assumptions; the existing thirteen G rows remain thirteen.', '',
    '## Statement and semantic comparison', '',
    '**No new propositional premise is added that is not an Rc10 specialization.** '
    'L154 is exactly the old query inequality at induced P. All other retained '
    'antecedents and all conditional continuation laws are unchanged. '
    'Rc11_statement-check.json checks the complete source declaration against '
    'an explicit replacement whitelist, and checks byte identity from `let select` '
    'through the final conclusion. Rc11_statement.diff records every edit.', '',
    'No constant, carrier TYPE, collision-event constructor, extractor or conclusion '
    'SCHEMA differs. Literal closed propositions do differ: P and runtime are now '
    'defined terms; the failure functional is evaluated on the admitted observer '
    'rather than an independently supplied runtime, and the event is instantiated '
    'at induced P. Thus this is not a proof that ARX is a direct instantiation of '
    'Rc10 (its removed binding is not supplied), nor equality with arbitrary '
    'unfiltered runtimes. The draft amendment makes that definition choice explicit.', '',
    'The observer returns the original RunView on exactly the cylinders with their '
    'OWN `ARU_Support.At` witnesses. Unfolded membership includes two runtime '
    'admissions, both native successes, their own bank/game/RuntimePersistence '
    'tuple and first/second query-restricted source agreement. They are body '
    'membership data, not new universal root antecedents. The unrelated fixed '
    'native tuple in the root is not asserted to be the outcome of every a. '
    '`ARX_Domain.range` proves the exact image; `ARX_AdmittedRuntime.on_admitted` '
    'and `ARX_LawEquivalence.observations/work/mean/failure_mean` establish '
    'equality on admitted executions and original-weight zero extension. '
    'Outside admission the returned option is None; all issued logs remain '
    '(`ARX_RejectedPrefixes.cost`) and source rejection has zero mass '
    '(`ARX_RejectedPrefixes.mass`). No conditioning/renormalization is performed. '
    '`ARX_OldClassPoison.differs` rules out equating the two observers even for '
    'the old pure-second-choice class. No unfiltered global mean equality is claimed.', '',
    '## Every retained atomic row, side by side', '',
    'Each row below is present in both roots. L154 is marked specialized; all '
    'other 115 retained row statements/families are unchanged. The JSON retains '
    'the original exact definition references, jobs, guards and blocker notes.', '',
    '| ID | Class | Owner | Scope | Rc10 meaning | ARX disposition |',
    '|---|---|---|---|---|---|']
for r in rows:
    meaning=r.get('meaning', r['name']).replace('|','\\|').replace('\n',' ')
    disp='same L154 at induced P (issued equality)' if r['id']=='L154' else 'same family and guards'
    lines.append(f"| {r['id']} | {r['classification']} | {r['owner']} | {r['scope']} | {meaning} | {disp} |")
lines += ['', '## Non-vacuity and remaining gates', '',
    '`ARX_Nonvacuity.conditional` (freshly printed and standard-axiom audited) '
    'derives an accepted admitted RunView with exactly JFx_NativeBytes proof/public '
    'bytes, conditional on a SAME installed native SupportedEntry and consistent '
    'native/H cylinder. It does not construct that pair or jointly inhabit all '
    'root premises. Rc10_Nonvacuity.composed and Rc10_Clean.exists_world are '
    'retained evidence, not new full ARX release fixtures. Exact partial fixture '
    'predecessors and the still missing full accepted pair are listed in '
    '../account-rejoin9-20261026/ARX_ROOT_COMPARISON.md. No new proof round or '
    'fictional fixture premise is introduced by this audit.', '',
    'Remaining actual P: native L142–L146, global F3Y_G_L142–L146 (session A), '
    'L154 (external query budget). Deployment P: L166 (native/source Result and '
    'ordered effects, including rejected prefixes), L187 (coherent release replay), '
    'L188 (final artifact/trust/dependency audit). Owner adoption and the full '
    'joint real-byte native pair remain open. The source-to-ELF release claim '
    'is not inferred from focused cached printing.', '',
    '## Validation and scope', '',
    '2/20 Lean attempts, both exit 0; 0/0 Kani. Wall 5.822825815994293 s total; '
    'maximum RSS 5558572 KiB; swaps 0. One own capped scope at a time; '
    'MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, -j1 -M7000. '
    'Complete commands/revision/source and dependency hashes, resource and axioms '
    'receipts: Rc11_attempts.jsonl and Rc11_00*/. Both roots and the printed '
    'ARX consumers use only propext, Classical.choice, Quot.sound. '
    'No new theorem, dependency build, package replay, Rust/Kani/SBF run or '
    'shipped/cfg(kani) change. Unchanged cached objects and historical ELF pins '
    'were reused; no fresh ELF rebuild is claimed. No adoption, push, authoritative '
    'ledger edit or security-contract edit occurred. The separately requested '
    'amendment is a draft only.']
# Keep generated resource totals tied to the exact receipts.
lines = [l.replace('2/20 Lean attempts', f'{len(attempts)}/20 Lean attempts')
          .replace('Wall 5.822825815994293 s total', f'Wall {wall:.9f} s total')
          .replace('maximum RSS 5558572 KiB', f'maximum RSS {peak} KiB') for l in lines]
lines += ['', 'The separate Rc11_003 boundary print unfolds the admitted mean, charge, '
    'query agreement, old binding, failure functional and exact constants. '
    'It also confirms L081 is STILL the global `P1Realization` at the fixed '
    'native root in both statements (`∀ bytes, sha256 bytes = H bytes`); '
    'RuntimeSyscall is success-conditioned. The new account coverage theorem '
    'uses query-restricted agreement and does not require that global equality '
    'for every consistent world. The retained global fixed-root antecedent '
    'has not been discharged or silently weakened by this recount.']
(E / 'Rc11_LEDGER.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(before=bt, after=at, fresh_inventories=len(inventories), retained_rows=len(rows)), indent=2))
