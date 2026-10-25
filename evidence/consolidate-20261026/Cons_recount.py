"""Recount from fresh Lean statement/field transcripts, using Ledger_003-005's
law-family convention. Classifications and correspondence decisions are explicit
reviewed audit data, not inferred from worker closure reports. No Lean replay.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
baseline=json.loads((ROOT/'evidence/premise-ledger-20261025/premises.json').read_text())['rows']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Mechanical inventory: extract complete printed fields, before constructor repetition.
catalog={}
for n in [7,8,10,39]:
 text=(OUT/f'Cons_{n:03}/stdout.log').read_text()
 for block in re.split(r'(?=^structure )',text,flags=re.M):
  if not block.startswith('structure '):continue
  name=re.match(r'structure (\S+)',block)[1]
  fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
  catalog[name]={'attempt':f'Cons_{n:03}','fields':fields,'field_names':re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M)}
(OUT/'Cons_field_catalog.json').write_text(json.dumps(catalog,indent=2,ensure_ascii=False)+'\n')
assert len(catalog['AspisR1.S2Trust.S2TrustedSdkBorrow']['field_names'])==15
assert len(catalog['AspisR1.DrvC_Installation.Configuration']['field_names'])==9
assert len(catalog['AspisR1.Port5Q2_Prepared.PreparedFields']['field_names'])==9
statement=(OUT/'Cons_039/stdout.log').read_text()
assert '∃ f s, ⋯' not in statement
assert all(x not in statement for x in ['saved_ten','authenticated_S1','(twelve :'])
# Complete instantiated signatures, including binder names, are also source-pinned.
retained=set(range(1,88))|set(range(94,100))|set(range(110,149))|set(range(151,155))|{157,159}
rows=[]
def blocker(i):
 if i<=82:return 'Retained adopted SDK/std/runtime/extraction/hash-value boundary; pin its concrete source/runtime instance.'
 if i in [83,84]:return 'Successful native pair at the exact installed source and runtime; remains a success-conditioned theorem.'
 if 85<=i<=87:return 'Unchanged FS2.Params data-carrier law (unused parameter); not an implementation/security closure.'
 if 94<=i<=96:return 'Prove protection and version provenance of the actual saved Pool checkpoint across transactions.'
 if 97<=i<=98:return 'Prove actual account proof/public binding, or its collision-event transport; digest equality alone is insufficient.'
 if i==99:return 'Associate the actual accepted proof with its reached parsed transcript on this pair.'
 if 110<=i<=121:return 'Supply the two actual round return/evaluation laws from S3/S5/S9.'
 if i in [122,123,124,126]:return 'Derive the exact resumed Prepared variant and alpha/slice observations from the accepted source calls.'
 if i in [125,127,128]:return 'Supply the same native newWeights/pair/dot primitive return and its model interpretation.'
 if 129<=i<=132:return 'Join the same transcript, queries, matching-data reads and decoded query bytes with the source execution.'
 if 133<=i<=142:return 'Instantiate same-call S3/S5/S9 pairing and round laws, not merely generic algebra.'
 if i==143:return 'Prove actual S4/S7 matching relation for all selected queries.'
 if 144<=i<=146:return 'Bind same source semantic/initial/chain/terminal equations from S3/S9.'
 if i==147:return 'Prove actual S5 dot product equals the selected opening/accumulator model.'
 if i==148:return 'Prove same source round/pair/dot/rhs canonical observation roundtrips.'
 if i in [151,152,153]:return 'Structural law of the unchanged model carrier; no arbitrary source arithmetic follows from it.'
 if i==154:return 'Prove total ByteProver query budget in the chosen oracle work model.'
 if i==157:return 'Raw canonical accepted source/frozen2 equality, including complete ordered oracle log; RawJ_ owner work is not imported.'
 if i==159:return 'Identify complete accepted runtime RunView with this same source program and oracle world.'
 raise ValueError(i)
for old in baseline:
 i=int(old['id'][1:])
 if i in retained:
  rows.append({**old,'scope':'actual antecedent','status':'still present','blocker':blocker(i),'evidence':'Cons_039/stdout.log; Cons_007/stdout.log'})

def add(name,meaning,owner,blocker,definition,field=None):
 if field:
  structure,member=field
  assert any(x.endswith('.'+member) for x in catalog['AspisR1.'+structure]['field_names']),(structure,member)
 rows.append(dict(id=f'N{sum(r["id"].startswith("N") for r in rows)+1:03}',name=name,
  meaning=meaning,classification='P',owner=owner,scope='actual antecedent',status='newly present',
  blocker=blocker,definition=definition,evidence='Cons_008/stdout.log; Cons_010/stdout.log; Cons_039/stdout.log'))
prepblock='Session A S1/S3/S4/S5/S9 must instantiate the immutable preparation contract on the constructed installed dictionary; this is the replacement boundary behind writer admission.'
limbs4=['c0.a','c0.b','c1.a','c1.b']
limbs8=[c+'.'+l for c in ['c0','c1'] for l in limbs4]
# Split every conjunction leaf, leaving j:Fin22/2/10/4 quantified as in the baseline.
for field,limbs in [('variant',[None]),('queries',[None]),('gamma',limbs8),('kappa',limbs8),('alpha',limbs8),('rho',limbs4),('semanticAlpha',limbs4),('coordinates',limbs4),('claim',limbs8)]:
 for limb in limbs:
  name='prepareOwner.accepted.'+field+('.'+limb if limb else '')
  meaning='Every successful actual preparation has '+(field+' limb '+limb+' < 2147483647' if limb else ('variant S2' if field=='variant' else 'all 22 query words below 262144'))+'; all success guards and p/scratch witnesses stay shared.'
  add(name,meaning,'session A',prepblock,'Port5Q2_Prepared.PreparedFields.'+field,('Port5Q2_Prepared.PreparedFields',field))
queryblock='Session A S3/S4/S5/S9 must supply the exact local primitive laws for the installed query dictionary; generic kernel algebra does not instantiate native helpers.'
for f in ['s3_s4_mul','s3_s4_sub','s3_s4_double','zero','one']:
 add('primitiveOwner.basis.'+f,'Exact installed query basis primitive equation; universal helper instance.','session A',queryblock,'Port4C_BasisOuter.SessionABasis.'+f,('Port4C_BasisOuter.SessionABasis',f))
for f,ls in [('s3_s4_s5_mulE',limbs8),('s3_s4_s5_addE',limbs8),('s3_s4_s9_mulK',limbs4)]:
 add('primitiveOwner.arithmetic.'+f+'.value','Exact decoded arithmetic output under all original canonical/input/result guards.','session A',queryblock,'Port4C_QueryArithmetic.SessionABackends.'+f,('Port4C_QueryArithmetic.SessionABackends',f))
 for limb in ls:
  add('primitiveOwner.arithmetic.'+f+'.canonical.'+limb,'Same output limb '+limb+' < 2147483647; not an independent output witness.','session A',queryblock,'Port4C_QueryArithmetic.SessionABackends.'+f)
for f in ['multiply','double','one','subtract']:
 add('primitiveOwner.m31.'+f,'Decoded M31 primitive result agrees with the model on its actual successful return.','session A',queryblock,'Port5Q1_NodeModel.SessionAM31.'+f,('Port5Q1_NodeModel.SessionAM31',f))
add('primitiveOwner.decoder.decode','Every successful bounded four-wide opening decode agrees with the selected wire slice.','session A',queryblock,'Port5Q1_OpeningValues.SessionAS3.decode',('Port5Q1_OpeningValues.SessionAS3','decode'))
add('primitiveOwner.line','Actual op16 line result equals lineWithInverses on the same values and inverse carrier.','session A',queryblock,'Port5Q1_QueryPorts.SessionAPrimitives.line',('Port5Q1_QueryPorts.SessionAPrimitives','line'))
for limb in limbs8:
 add('primitiveOwner.line_canonical.'+limb,'Same successful op16 output limb '+limb+' < 2147483647.','session A',queryblock,'Port5Q1_QueryPorts.SessionAPrimitives.line_canonical')
geoBlock='Session A S3/S4/S5 must instantiate the actual geometry primitive/canonical domain and inverse bindings on this installed dictionary.'
for f,leaves in [('point',['x','y']),('line',['value']),('multiply',['value']),('double',['value']),('one',['value']),('subtract',['value'])]:
 for leaf in leaves:
  add('geoLeaves.'+f+'.'+leaf,'Geometry primitive successful output '+leaf+' is canonical, with every original guard.','session A',geoBlock,'Port5Q1_GeometryCanonical.SessionAPrimitives.'+f,('Port5Q1_GeometryCanonical.SessionAPrimitives',f))
for f,leaves in [('fibre',['identity','bound']),('point',['x','y']),('line',['value']),('multiply',['value']),('double',['value']),('one',['value']),('subtract',['value'])]:
 for leaf in leaves:
  add('domain.'+f+'.'+leaf,'Actual geometry '+f+' output '+leaf+' has the exact model-domain meaning; same result witness.','session A',geoBlock,'Port5Q1_Domain.SessionADomain.'+f,('Port5Q1_Domain.SessionADomain',f))
for f in ['multiply','one','inverse']:
 add('geometry.'+f,'Exact geometry helper equation in the conditional source/model composition.','session A',geoBlock,'Cons_Top.deployed; Cons_Ten.Outcome')
prepareBlock='Session A S1 must bind the same returned TX1 Prepared to the chosen model data/rho/query map; lead still must join the complete context and saved encoding.'
for f,leaves in [('queries',[None]),('rho_eq',[None]),('rho_canonical',limbs4),('alpha1',[None])]:
 for leaf in leaves:
  add('prepare_S1.'+f+('.'+leaf if leaf else ''),'Same TX1 preparation-to-model law '+f+(' limb '+leaf if leaf else '')+'; shared data/rho/q and actual run.p.','session A',prepareBlock,'Port5Q1_QueryPorts.SessionAPrepare.'+f,('Port5Q1_QueryPorts.SessionAPrepare',f))
add('tx1_saved','The ACTUAL saved Vec equals Tx2N_Reader.writer H stored publicBytes of prepared Context/data/rho/q and the model ten-state accumulator.','lead','Derive the full Context, Prepared and physical writer encoding equation on this same TX1 run. Cons_Ten proves the accumulator under preparation/read laws but does not prove this complete Vec equation.','AuS1_Finish.Outcome; Tx2N_Reader.writer')
add('ten.parseReached','The particular transcript used for the strengthened ten-state conclusion parses the same authParsed; distinct from mere existence in entry.parsed.','lead','Associate the selected transcript with the same source proof and matching-data read; existential parser success alone does not identify an arbitrary transcript.','Cons_Ten.Outcome')
for f in ['prefixBound','choiceBound']:
 add(f,'Universal query-budget bound for '+('adversary before TX1' if f=='prefixBound' else 'chooseSecond on every input and saved Vec')+'.','external','Provide the source-experiment budget association; no resource/work normalization credit is inferred.','Cons_Top.deployed')
assert len([r for r in rows if r['id'].startswith('N')])==118

# Row-by-row diff includes the original separate deployment inventory E. A row
# absent from the theorem is NOT automatically discharged as a release obligation.
removed={88:'Constructed SdkD child port; erasure is a theorem, not a supplied ChildConeJoin.',
89:'Old unguarded FirstMarks is not a premise; success-conditioned concrete marks consumed internally.',
90:'Old unguarded SecondMarks is not a premise; concrete marks consumed internally.',
91:'Writer.header is derived and exported on the exact cut.',92:'Writer.size is derived and exported.',93:'Reader.checkedHeader is derived and exported.',
149:'No saved_ten input in the sole finish branch; derived internally from same saved encoding and reader success. See retained tx1_saved.',
150:'No twelve input in the sole finish branch; derived by Tx2N under primitive/geometry/read/preparation laws.',
155:'Superseded arbitrary-logical-input domain, not proof of that contradictory/global statement.',156:'Superseded unrestricted annotated interface; canonical domain used instead.',
158:'Derived two-pass canonical annotation from raw verifier join and constructed Physical.',
160:'Constructed implementation/source and proved Program equality on all inputs; SDK identities checked, not assumed.',
161:'Carried.statement is derived for canon(lift P); no independent Carried hypothesis.',162:'Carried.stored is derived for canon(lift P).',163:'Carried.rows is derived for canon(lift P).',
164:'One checked CPhy/T2Nat/AuS1 dictionary and shared f,s/run construction.',
167:'Indexed authentication is derived with a collision alternative on the same trace; no authenticated_S1 input. SessionAPrepare remains.',
169:'Native ten-step query instance and collision-or-model ten state on the same run; preparation/read/geometry leaves remain.',
170:'Native flush materialization on the same run.',171:'Actual writer and native-writer results derived on same run; full Context/physical encoding still tx1_saved.',
172:'Native reader/OnRun/helper composition exported; no native-reader equality hypothesis.',
173:'Installed same-return powers uses Tx2N_Powers and existing checked early_powers, no new powers hypothesis.',
174:'Installed initial/pending constructor derived on the exact run.',175:'Complete successful finish silent-effects law exported; session A pairing/dot/round laws retained.',
183:'Two canonical annotation passes derived from raw verifier join and Physical.',184:'Corrected canonical PerAttempt Claims and repeated/adaptive bound plus zero-query corollary proved conditionally.'}
for i in range(100,110):removed[i]='Concrete physical node/y1 ranges derived and exported on same f,s; no independent range/join premise.'
# Open deployment items are deliberately separate from literal theorem antecedents.
residual={165:'Header/shape value installed; full source semantic/transcript association remains in L129-L132 and raw join.',
166:'Installed source batch effects are identified by driver construction; native lowering/adoption/effect association still required.',
168:'Same Context/data/preparation and saved-byte association remains as N preparation laws and tx1_saved; not discharged by state arithmetic.',
176:'Semantic source getters/cuts compose, but native ownership/error/cleanup/adoption remains outside the kernel statement.',
177:'Arbitrary Claims reserve/intoBox data dictionary has no full native ownership/abort/effects interpretation.',
178:'Covered explicitly by N001-N114 primitive/preparation law leaves; do not add another count for this umbrella.',
179:'SDK borrow trust retained; concrete allocator/library/native frame and source association remain deployment obligations.',
180:'Specific cross-transaction history protection remains L094-L096; runtime rollback semantics alone is insufficient.',
181:'Complete source Program equality is proved; ordered source-to-frozen2 model event/projection association remains raw L157/GExq work.',
182:'Same obligation as literal L157 at this installed source, not a second independent gate.',
185:'Same obligation as literal L159 at this installed source, not a second independent gate.',
186:'Source-to-SBF/artifact association for the exact frozen ELFs remains; no new binary proof.',
187:'Only coherent cached focused composition audited; full frozen dependency release replay not run.',
188:'Current top standard-axiom audit passes; final release dependency/trust/adoption audit remains.',
195:'Actual native total-oracle/source association remains, distinct from success-only RuntimeSyscall; no P6-boundary binder in this top.',
196:'Actual native binary-parent callback/log lowering remains a deployment association, not a top antecedent.',
197:'Actual native occupied-parent callback/log lowering remains a deployment association, not a top antecedent.',
198:'Actual native sibling-parent callback/log lowering remains a deployment association, not a top antecedent.',
199:'Actual native leaf callback/source association remains a deployment obligation; no leaf gate binder here.'}
diffs=[]
for r in baseline:
 i=int(r['id'][1:])
 if i in retained:status='still present';reason='Literal expanded antecedent, at the constructed installed instance.';scope='actual antecedent'
 elif i in removed:status='removed';reason=removed[i];scope='derived/superseded'
 elif i in residual:status='still present';reason=residual[i];scope='deployment only'
 elif 189<=i<=194:status='still present';reason='Retained release/tool/runtime/cryptographic trust; not an additional explicit Lean binder.';scope='deployment only'
 else:raise ValueError((i,r['name']))
 diffs.append(dict(id=r['id'],name=r['name'],classification=r['classification'],owner=r['owner'],status=status,scope=scope,reason=reason))
# Every remaining deployment P row has its owner and next blocker. Umbrella aliases
# to counted antecedents are flagged so that totals do not pretend independent gates.
aliases={168,178,180,182,185}
for d in diffs:
 if d['scope']=='deployment only':
  rows.append(dict(id=d['id'],name=d['name'],classification=d['classification'],owner=d['owner'],
   status='still present',scope='deployment alias' if int(d['id'][1:]) in aliases else 'deployment only',
   meaning=d['reason'],blocker=d['reason'],definition=baseline[int(d['id'][1:])-1]['definition'],evidence='Cons_039/stdout.log; Cons_STAGE1.md'))

def counts(rs):
 return dict(classes=dict(Counter(r['classification'] for r in rs)),owners=dict(Counter(r['owner'] for r in rs)),
  by_owner={o:dict(Counter(r['classification'] for r in rs if r['owner']==o)) for o in ['lead','session A','external']},rows=len(rs))
summary={s:counts([r for r in rows if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
summary['all retained audit rows']=counts(rows)
summary['deduplicated actual plus non-alias deployment']=counts([r for r in rows if r['scope']!='deployment alias'])
(OUT/'Cons_premises.json').write_text(json.dumps(dict(method='Fresh Lean statement and field printing, explicit reviewed classification and law-family deduplication; not an automated logical discharge checker.',baseline_sha256=sha(ROOT/'evidence/premise-ledger-20261025/premises.json'),counts=summary,rows=rows,diff=diffs),indent=2,ensure_ascii=False)+'\n')

# Incremental append: preserve every byte of all previous ledger sections.
marker='\n## Recount on Cons_Top (2026-10-25)\n'
doc=ROOT/'design/PREMISE-LEDGER-20261025.md'
original=doc.read_text().split(marker)[0]
text=marker+'''
**Actual theorem: `AspisR1.Cons_Top.deployed`. Target not yet established.**
Branch `codex/cx-consolidate-20261026`; receipts: `evidence/consolidate-20261026/`.
Date is the actual UTC/UK audit date; the job/branch retains its assigned 20261026 name.

This is a fresh application of Ledger_003–005's method: kernel-print the full
ACTUAL statement, print structures/definitions, split conjunctive law leaves,
keep quantified families and shared existential witnesses/guards, then manually
classify and deduplicate with a reproducible renderer. The classifications are
reviewed audit decisions; Python does not prove implications or discharge rows.
`Cons_039/stdout.log` contains the actual top plus every factored conclusion,
the shared TX2 tuple/calls, and shared Cons_Finish/Cons_Ten outcomes;
`Cons_007` repeats the original field inventory on this coherent selection;
`Cons_008` expands all newly exposed preparation/query/geometry contracts;
`Cons_010` expands canonicality and the remaining data carriers. The initial Cons_006 print hid deep terms; Cons_009 fixed that
display issue for Stage1. Cons_039 freshly audits the final shared-tuple top. Only proof-irrelevant subtype witnesses are hidden.
`Cons_field_catalog.json` mechanically extracts every printed structure field.
The before statement/field evidence and baseline remain Ledger_003–005 and
`premises.json`; the named-binder after sources are `lean/Cons_Top.lean`, `Cons_Result`,
`Cons_Base`, `Cons_Caller`, `Cons_Continuation`, `Cons_Finish` and `Cons_Ten`.

Counting unit remains an atomic law FAMILY, not byte cells or independent
proof gates. Fixed canonicality conjunctions are split into their four/eight
limb laws; Fin22/Fin2/Fin10/Fin4 quantified families are not enumerated. Payload
and whole-vector equalities remain one family. Repeated primitiveOwner,
queryLeaves and Cons_Ten ports refer to the same dictionary and are counted
once. Read/prepare model families repeated in the ten/finish continuations
are deduplicated; existential entry.parsed and the particular ten.parseReached
guard are distinct. Params/Functional/initFits remain structural carrier laws,
not assertions of actual source correctness. No new typeclass is required.
Configuration, FinishOps, query/geometry Ops, B, std, Context and Runtime are
data-only dictionaries/carriers; arbitrary functions are not source proofs.

The old ledger mixed actual antecedents with additional deployment items E
and historical endpoints D. The tables distinguish them. “Deployment alias”
means an umbrella for already counted antecedent leaves; it adds no independent
gate. An absent deployment item is not silently credited as a proof. Counts
measure neither a security percentage nor unconditional release progress.

| Scope | T | P | C | lead | session A | external |
|---|---:|---:|---:|---:|---:|---:|
'''
for scope,c in summary.items():
 text+='| '+scope+' | '+' | '.join(str(c['classes'].get(k,0)) for k in ['T','P','C'])+' | '+' | '.join(str(c['owners'].get(k,0)) for k in ['lead','session A','external'])+' |\n'
text+='''
| Actual antecedent owner | T | P | C |
|---|---:|---:|---:|
'''
for owner,c in summary['actual antecedent']['by_owner'].items():text+='| '+owner+' | '+' | '.join(str(c.get(k,0)) for k in ['T','P','C'])+' |\n'
text+='''
The expanded P total increases because this theorem EXPOSES previously
uninventoried preparation/primitive and saved-encoding boundaries. This is
not evidence of protocol regression, nor permission to subtract job reports
from the baseline. L149/L150 disappear as inputs, but `tx1_saved` remains a
strong same-Vec/Context/model ten-state equation. A root/state observation is
not that equation. AuS1 removes the authenticated_S1 input by proving a
collision OR indexed-recovery branch under SessionAPrepare. No collision-free
unconditional authentication theorem is claimed.

The same f,s,outer,pre,middle,fs,ss and the same TX1 run supply every native,
writer, preparation-trace and finish output. Fresh first_run is derived from
THAT SourceCuts, not supplied by the caller. Writer admission is reconstructed
on THAT run from immutable prepareOwner and primitiveOwner, not assumed.
Old weaker TX2 finish and TX1 authentication continuations are not exported.
Cons_Ten returns collision OR the ten-state result. Cons_Finish.Outcome retains
AuS1's strongest branch on ONE shared TX2 tuple; Cons_FinishProof derives
saved_ten/twelve internally and retains the original round/pair/dot/semantic
laws. The shared native/finish tuple is constructed once from the accepted source
common call, including Op5T's installed batch. Cons_Base/Caller/Continuation/Result
only factor conclusions; they add no top hypothesis. Native Witness has ten
data fields and no Prop field. The SDK installation equality is a proved output and CPhy is definitionally
the same sdk; complete driver/source Program equality is a proved output.
The headline uses this same installed source/dictionary. It does NOT identify
the arbitrary GExp adversary/project with the accepted native pair; the global
experiment/event/source association remains L157/L159/L181 and the bounds.
Carriers, failure game, Q quantifiers, metric and collision constants are unchanged;
the arbitrary driver/dictionary family is specialized to DrvC's constructed
release installation, explicitly rather than via a compatibility assumption.

### Row-by-row baseline diff

| Baseline | Name | Class / owner | Status | Actual location or reason |
|---|---|---|---|---|
'''
for d in diffs:
 vals=[d['id'],d['name'],d['classification']+' / '+d['owner'],d['status']+' ('+d['scope']+')',d['reason']]
 text+='| '+' | '.join(v.replace('|','\\|') for v in vals)+' |\n'
text+='''
### Newly present expanded antecedents

Every row below is P. This includes the replacement boundaries behind the
reported removals; these are not new external cryptographic assumptions.

| ID | Law family | Owner | Meaning | Blocker |
|---|---|---|---|---|
'''
for r in rows:
 if not r['id'].startswith('N'):continue
 text+='| '+' | '.join(str(r[k]).replace('|','\\|') for k in ['id','name','owner','meaning','blocker'])+' |\n'
text+='''
### All remaining P rows and accountable blockers

This list includes actual antecedents and remaining deployment rows, explicitly
labelled; aliases are not independent gates. Ownership is accountable owner,
not a claim about a concurrent worker's completion.

| ID | Scope | Owner | Remaining law / deliverable | Waiting on |
|---|---|---|---|---|
'''
for r in rows:
 if r['classification']!='P':continue
 text+='| '+' | '.join(str(r[k]).replace('|','\\|') for k in ['id','scope','owner','name','blocker'])+' |\n'
text+='''
### Requested removal claims: statement-level reconciliation

| Reported row / claim | Recount finding / discrepancy |
|---|---|
| L089 | Absent: old unguarded FirstMarks removed. No discrepancy on this top; it does not prove the old unguarded law. |
| L090 | Absent: old unguarded SecondMarks removed. No discrepancy on this top. |
| writer admission | Admitted is an OUTPUT, not a premise. Qualified: immutable prepareOwner's 46 atomic laws plus primitiveOwner remain; not unconditional native writer certification. |
| L164 | Removed: one checked dictionary and same f,s/run, no compatibility premise. |
| L091 | Removed: writer header derived. |
| L092 | Removed: writer size derived. |
| L093 | Removed: reader checkedHeader derived. |
| L100 | Removed: batch0 physical start derived. |
| L101 | Removed: batch0 physical finish derived. |
| L102 | Removed: batch0 physical bound derived. |
| L103 | Removed: batch0 physical index derived. |
| L104 | Removed: batch1 physical start derived. |
| L105 | Removed: batch1 physical finish derived. |
| L106 | Removed: batch1 physical bound derived. |
| L107 | Removed: batch1 physical index derived. |
| L108 | Removed: y1 length derived. |
| L109 | Removed: y1 index derived. |
| authenticated_S1 | Absent in the sole finish and strengthened ten branch. Removal confirmed with the documented collision alternative; seven prepare_S1 laws remain. |
| L158 | Removed: canonical annotation derived; raw L157 remains. |
| L183 | Removed: two passes derived; raw L157 and runtime L159 remain. |
| L184 | Removed: corrected conditional PerAttempt endpoint is an actual conclusion, including the zero-query bound. It is not an unconditional deployed guarantee. |
| L175 | Successful finish effects are an output. Removal confirmed on the shared tuple; source/runtime/artifact association and round/pair/dot laws remain as documented. |
| L172 | Native/helper reader and exact OnRun effects are outputs. Removal confirmed on the shared tuple; extraction/native source association remains as documented, and saved_ten depends on tx1_saved. |
| L160 | Removed at this constructed instance: Program equality and dictionary identities proved. No claim that every arbitrary Implementation is installed. |
| L149 saved_ten | Removed as an input. Material replacement boundary: tx1_saved remains a whole saved-Vec/model encoding equation. |
| L150 twelve | Removed as an input. Primitive/domain/read/preparation and saved-Vec boundaries still needed. |

Direct comparison with `DrvC_HANDOFF.md`, `auth-s1-20261026/HANDOFF.md` and
`T2Nat_HANDOFF.md` finds no disagreement with their SCOPED named-removal claims.
The material qualifications above are retained documented boundaries, not
contradictions of those reports. The initial Stage1 independent TX2 packaging
is superseded by the shared tuple in Stage2. Newly inventoried P rows largely
expose inherited CPhy/owner contracts; they are not all introduced by Cons_.

No contradiction/vacuity-suspect C antecedent from the old endpoints survives.
This is not a joint inhabitation proof for all remaining runtime/model premises.
No imported candidate from RawJ_, NP6_ or Low2_ is credited or changed.
Source-to-ELF association and the full release target remain open.

### Validation and handoff

Thirty-nine Lean compile attempts of60, zero Kani of0; zero dependency builds.
Fifteen failed development versions are retained and excluded: 001,012,013,015,
018,019,020,021,023,026,028,030,032,034,035. Compiler-generated sorryAx in failed
versions is never accepted. Eleven default-heartbeat failures were isolated and
split; no wall timeout/memory kill/cap/heartbeat increase occurred. The decisive
source-shape correction is in Cons_036: the concrete native TX2 base must include
Op5T's installed batch, rather than reducing unequal arbitrary dictionaries.
Cons_037/038 pass the final Pair/Top; Cons_039 prints all five new theorem audits,
all exactly [propext, Classical.choice, Quot.sound]. Current native/finish/base/
caller/result definitions also passed independently. Every actual call uses the
unchanged S2W launchers, lake env lean -j1 -M7000 -DElab.async=false, separate
scopes MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. One own scope at a time;
initial inventory observed one NP6 scope. No unchanged timed-out source+dependency
rerun, package replay or launcher/infrastructure edit occurred.

Per-attempt source revisions, exact source/dependency hashes, targets, exits,
wall/RSS/swap and full axiom/error lines are in the receipts and source snapshots.
Cons_validation.json validates current sources against the accepted receipts,
field coverage, deduplication/totals and append-only preservation of prior ledger
text. Unchanged cached canonical/SInt2/DrvC/T2Nat/AuS1/Tx2N dependencies were
reused; this is a focused coherent composition, not a frozen release rebuild.

No shipped or cfg(kani) file changed, so the three-ELF rebuild trigger did not
fire. Pins inherited, not freshly reproduced: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No session A live worktree/candidate, foreign module, key or release scope was
changed. Commits are local; no push. Next concrete deliverables are raw L157,
complete runtime L159, same saved-Vec/Context equation and actual source/model
primitive instances, followed by global event and source/artifact association.
'''
doc.write_text(original+text)
print(json.dumps(summary,indent=2))
