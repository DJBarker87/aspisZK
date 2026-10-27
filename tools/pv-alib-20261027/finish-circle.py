from pathlib import Path
import hashlib,json,posixpath,shlex,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-alib-20261027';D='/home/dombarker/project-offloads/codex-pv-alib-20261027'
meta=json.loads((E/'circle-owned-translation.json.txt').read_text())
paths=sorted({x.get('source',{}).get('file','') for k in ['functions','globals','types'] for x in meta.get(k,[])})
r={}
for source in paths:
 if '/source/crates/' not in source:continue
 remote=source if source.startswith('/') else posixpath.normpath(D+'/sampler-owned/'+source)
 relative='crates/'+remote.split('/source/crates/',1)[1]
 actual=subprocess.check_output(['ssh','dombarker@100.108.41.90','sha256sum '+shlex.quote(remote)],text=True).split()[0]
 expected=hashlib.sha256((R/relative).read_bytes()).hexdigest();assert actual==expected,(relative,actual,expected)
 r[relative]={'sha256':actual,'host_path':remote,'worktree_match':True,'extractor_path':source}
(E/'circle-native-input-pins.json').write_text(json.dumps(r,indent=2)+'\n')
p=E/'ROWS-RESUME.json';rows=json.loads(p.read_text());x=next(x for x in rows if x['id']=='V265');x.update(after='selected source callback and complete-Result structural native/reference gate supplied; whole deployed native composition remains separate',status='CLOSED-ON-CANDIDATE',theorem=['R1Z.PV_AL_CircleNative.source_reference','R1Z.PV_AL_CircleSelected.native_source','R1Z.PV_AL_CircleSelected.consumed'],gate='owned safe reference extracted without holes; structural native control transport under ruling (k); no arithmetic Kani',nonvacuity='no equality/totality hypotheses; both row constructors have inverse carrier transports')
p.write_text(json.dumps(rows,indent=2)+'\n')
p=E/'REPORT.md';s=p.read_text();a=s.index('## V265 ongoing source attempt');b=s.index('No endpoint premise or T field changed.',a)
s=s[:a]+'''## V265 source callback and structural gate

Before: `ProverRwFull.ExternalFuns.op259`; the prepared selector lacked the
native/reference source gate. After: **OPEN -> CLOSED-ON-CANDIDATE**, at the
selected source/library-law boundary. Closing theorems:
`PV_AL_CircleNative.source_reference` and
`PV_AL_CircleSelected.{native_source,consumed}`. They cover every block and both
rows with complete Result behavior. Both carrier roundtrips and both row
images are proved. No totality, field equality, source-equivalence or
conclusion-shaped hypothesis is assumed.

Ruling (k)'s structural route is used. The owned safe reference preserves every
frozen arithmetic call and its order, singularity priority, both map errors,
fallback constants and row selection. Explicit matches replace ok_or/? and
unwrap_or_else outside shipped crates. `STRUCTURAL-CIRCLE-GATE.json` checks the
complete pinned native control bodies and identical fallback parameters.
`PV_AL_CircleControl.native_owned` proves the generic control transport with
failure/divergence intact; the native map/fallback/wrapper equations specialize
it to the same extracted arithmetic. The relative sampler source path in the
extraction metadata is resolved against its proof crate, not the SSH login
folder; `circle-native-input-pins.json` checks every relevant source file
against this worktree.

The unchanged pinned tools extract the reference with no external-function
holes or opaque arithmetic leaves. Three positive shift-count literal ABI
mismatches were normalized to the current scalar API; the generic U64 shift
identities are proved in `PV_AL_ShiftLiterals`. Exact edits are recorded in
`primitive-shift-normalization.json` and reproduced by `promote.py --check`.
The extractor and release Rust are unchanged. Source, structural-link and
selected-law checks print only standard axioms (52756/52758/52759/52760/
52763/52764/52767).

`native-circle-owned-03` passes 8,712 wrapper comparisons (8,582 accepted;
130 rejected/fallback), direct map comparisons, directed ±i singular cases,
and both row fallbacks. Earlier reference tests and failed closure/core/Drop
extractions are retained separately. `CIRCLE-FIDELITY-SCAN.json` records all
three live Array.update results and quotient reuse. The fresh Lean emission
(52765) and native Rust agree on zero and FF digit fixtures, including
`[255,2048,7168,14336]`, where quotient writes change the output. The legacy
mut-iterator low_base_p_digits body is absent from this op259 graph. No
chained-field-arithmetic Kani was attempted.

This is a structural source/library result plus fresh extraction and native
checks, not an unbounded whole-machine proof or a deployed endpoint instance.
The final owner dependency replay and whole native composition remain separate.
V184 work continues within the remaining budget.

'''+s[b:];p.write_text(s)
print('circle source pins and per-row report completed')
