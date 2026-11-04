"""Quote exact existing Lean statements; no compilation or theorem credit."""
import pathlib,subprocess,hashlib,json,re
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1];pins=[]
def read(p):
 raw=(R/p).read_bytes() if (R/p).exists() else subprocess.check_output(['git','show','HEAD:'+p],cwd=R)
 pins.append(dict(path=p,sha256=hashlib.sha256(raw).hexdigest()));return raw.decode()
def statement(p,name):
 s=read(p);m=re.search(r'(theorem '+re.escape(name)+r'\b.*?)(?: := by| :=\n)',s,re.S);assert m,(p,name);return m[1]
A='evidence/slice-q-accum-20261104/'
acc=statement(A+'NFS_NEV_AccumPacket.lean','result_state_effects')
embed=statement(A+'NFS_NEV_AccumulateCallees.lean','from_m31')
total=statement(A+'NFS_NEV_CtorResults.lean','m31')
step=statement(A+'NFS_NEV_RowStep.lean','active')
q=statement('docs/research/100bit-spend-path-20261013/lean/ExtractedOpeningQueriesReachability.lean','queries_success')
raw=read(A+'NFS_NEV_AccumulateRaw_Funs.lean');external=read(A+'NFS_NEV_AccumulateRaw_FunsExternal.lean')
query_path='docs/research/100bit-spend-path-20261013/lean/bridge-opening-queries-1b98-20261017/ExtractedOpeningQueriesModel.lean'
query=read(query_path)
assert query.count('← B.embed ')==22
assert 'let we1 ←\n      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31' in raw
text='''# Q callee naming audit (inspection, no row-status ruling)

TX1:182 and TX2:108 remain CLOSED in the inherited NFX basis. TX1:168 remains OPEN. No status is changed by this audit. The 22 query conversions and one batched-accumulation conversion are compiler-confirmed in NGB_MIR_EDGES.json; their results are arguments to the non-prover no-op trace, so Rust evaluates them.

For accumulation, the complete model packet is NFS_NEV_AccumPacket.result_state_effects, in namespace NFS_NEV_AccumPacket, with `open Aeneas Aeneas.Std Result NEV_AccumulateCarriers` and `open AspisR1 AspisR1Stage2 Port3_NativeQueryBody`:

```lean
'''+acc+'''
```

The theorem statement refers to the complete emitted function, rather than listing individual callees. It does NOT erase the conversion from its left-hand execution: NFS_NEV_AccumulateRaw_Funs.lean, loop1.body, lines 133–137, binds basis_at, executes CodeField.from_m31, and then calls trace.value 13. The external binding in NFS_NEV_AccumulateRaw_FunsExternal.lean calls the emitted NEV_CodeFieldRaw constructor, then maps its nominal carrier; trace.value itself is `ok ()`. The value is deliberately absent from the observable effect list. Its evaluation, including partial Result behavior, is retained and then proved total before erasure. Thus “callee not named by the packet” is too strong for the current NFS model forest.

The relevant exact canonical-domain association, namespace NFS_NEV_AccumulateCallees, is:

```lean
'''+embed+'''
```

That law requires m.val < 2147483647. The stronger totality law actually used to erase the diagnostic conversion in the row-step proof, namespace NFS_NEV_CtorResults, is:

```lean
'''+total+'''
```

Here `mValue word := fromCtorE (NEV_CodeFieldBridge.value word)`. The active row proof names NFS_NEV_CtorResults.m31 and NEV_AccumulateRaw.trace.value explicitly. Its full statement (namespace NFS_NEV_RowStep, with Iter/RawFlow/Flow/mapFlow as defined there) is:

```lean
'''+step+'''
```

This establishes a model-side discarded-argument route already present in NFS; it does not grant native callee closure to the new OPEN trait-implementation rows, nor decide the lead's revised inventory status policy. No new compiler/prover run was performed.

For TX1:168 / Transcript<H>::queries, the NFX row has no selected claims and no CLOSED model packet. It is therefore impossible to quote a CLOSED full-function packet for that row. The existing successful-query model observation, in namespace AspisR1PublicPreparation.QueriesCalls, is:

```lean
'''+q+'''
```

This is conditional on model success and is NOT a native/model whole-function bridge. Its statement hides the embedding inside QueriesModel.queries B; the definition does not erase it. The tracked bridge-opening QueriesModel source declares:

```lean
structure QueriesModel.Boundaries where
  decode : Array (Array U8 32#usize) 8#usize → Array (Array U8 32#usize) 8#usize →
    Result (core.result.Result (Array U32 22#usize × Array U8 32#usize) aspis_core.transcript.QuerySampleError)
  embed : aspis_core.field.M31 → Result aspis_core.field.WideExact
```

All 22 sites bind `let we ← B.embed u` (with numbered locals thereafter) before `trace.value 5 ... we`; queries_success's proof destructures each B.embed success separately. Therefore the model names the embedding as a parameter and preserves argument evaluation; it does not by itself identify B.embed with the frozen WideExact CodeField implementation. NFS_NEV_AccumulateCallees.from_m31 is a potential canonical-domain association, not a supplied same-input query caller bridge. The query row stays OPEN, and its concrete B.embed installation/domain/native correspondence needs its own certificate. The source variant inspected here is identified by its path and hash in NGB_Q_SOURCE_PINS.json; no new coherent object association is claimed.

All quoted statements are verbatim retained source, with proof bodies omitted. Existing imports/abbreviations remain part of their meaning. No new theorem, axiom, trust item, or security closure is asserted; #print axioms is N/A for this inspection job. Existing NFS receipts are reused only as historical evidence, not replayed.
'''
(E/'NGB_Q_CALLEE_FINDING.md').write_text(text)
(E/'NGB_Q_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
print('quoted model statements and pinned',len(pins),'source reads')
