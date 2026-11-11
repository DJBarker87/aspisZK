#!/usr/bin/env python3
"""PCXU: PIN2_NEWGATE_r1_semantic.lean from the PCXU_E003 emission. Sibling of PIN2_NEWGATE_r0.lean: `import PIN2_NEWGATE_r0`, namespace AspisR1PublicPreparationPIN2 (extended).
Same transformations as PCXQ_mk_newgate_r0.py (rust_* attributes and module headers dropped; Result.branch/from_residual qualified to PCWN_NewLib).
Additionally the crate prefix `aspis_statement.` of r0 names is dropped (PCXQ_E001 extracted inside crate aspis-statement, so the gate names start at pool_v1); every emitted declaration that already exists in PIN2_NEWGATE_r0.lean with identical tokens (modulo doc comment, rust_* attributes and line layout) is dropped (it is the same constant, resolved via the import);
the script asserts identity, and lists kept/dropped declarations in PCXU_NEWGATE_DECLS.json. usage: python3 PCXU_mk_newgate.py"""
import re,sys,json,hashlib
sys.dont_write_bytecode=True
D='PCXU_E003_emitted/raw/PCXU_r1sem/';G='../prov-p9a-20261110/PIN2_NEWGATE_r0.lean'
sha=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
def xform(t):
    t=re.sub(r'(?m)^@\[rust_loop_body\]\n','',t);t=re.sub(r'(?m)^@\[rust_loop\]\n','',t)
    t=re.sub(r',\s*rust_(?:type|const|fun)\s+"[^"]*"','',t)
    t=re.sub(r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTry\.branch','PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch',t)
    t=re.sub(r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTry_traitFromResidualResult\.from_residual','PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual',t)
    t=re.sub(r'(?<![\w.])core\.result\.Result\.map_err','PCWN_NewLib.core.result.Result.map_err',t)
    t=re.sub(r'(?<![\w.])aspis_statement\.pool_v1\.','pool_v1.',t)
    return t
def body(f,ns):
    s=open(D+f).read();a=s.index('namespace '+ns)+len('namespace '+ns);b=s.rindex('end '+ns)
    return xform(s[a:b])
def blocks(t):
    # declaration blocks start at a doc comment '/-- ' at column 0 (Aeneas puts one before every declaration)
    parts=re.split(r'(?m)^(?=/-- )',t);return [p.strip('\n') for p in parts if p.strip()]
def norm(b):
    # token-level comparison: drop the leading doc comment, rust_* attribute blocks and all layout (Aeneas wraps lines by name length)
    b=re.sub(r'(?s)^/--.*?-/\n','',b)
    b=re.sub(r'(?s)@\[(?:[^\[\]]|\[[^\]]*\])*\]','',b)
    b=re.sub(r'(?m)^\s*--.*$','',b)
    return ' '.join(b.split())
def key(b):
    m=re.search(r'(?m)^(?:@\[[^\]]*\]\n)?(?:def|structure|inductive|abbrev|axiom|theorem)\s+(\S+)',b)
    if m: return m.group(1)
    m=re.search(r'(?ms)^(?:def|structure|inductive)\s*\n\s*(\S+)',b);return m.group(1) if m else None
g=open(G).read();ga=g.index('namespace AspisR1PublicPreparationPIN2');gb=g.rindex('end AspisR1PublicPreparationPIN2')
gate={}
for b in blocks(g[ga+len('namespace AspisR1PublicPreparationPIN2'):gb]):
    gate[key(b)]=norm(b)
kept=[];dropped=[];diffs=[]
allb=blocks(body('Types.lean','PCXU_r1sem'))+blocks(body('Funs.lean','PCXU_r1sem'))
out=[]
for b in allb:
    k=key(b);assert k,b[:200]
    if k in gate:
        if gate[k]==norm(b): dropped.append(k);continue
        diffs.append(k)
    kept.append(k);out.append(b)
raw={f:sha(open(D+f,'rb').read()) for f in ('Types.lean','Funs.lean')}
hdr='''-- PIN2 NEW GATE for r1_semantic::public_transcript at source c7593d23fdc56fcee9a9df1628d5f63b52ac7a95 (PIN2 pin; text of r1_semantic.rs unchanged since 4bb3b3f).
-- Emission PCXU_E003: Charon 454586e9 + Aeneas 0d21a9ec (second tool version, same as PCXQ_E001), overflow-checks ON, features private-leaf-salts,optimized-terminal,program-build,
-- cargo --jobs 4 / CARGO_BUILD_JOBS=4, rustc -Zthreads=1, identity by class receipt PCWE_E003, roots public_transcript + r0 Public::public_bytes.
-- Raw emission sha256: Types.lean %s Funs.lean %s
-- Composes with PIN2_NEWGATE_r0 (import) in the same namespace AspisR1PublicPreparationPIN2; declarations identical to those in PIN2_NEWGATE_r0 are dropped (listed in PCXU_NEWGATE_DECLS.json).
-- Built by PCXU_mk_newgate.py. Contains no placeholder proof and no axiom.
import Aeneas
import PIN2_NEWGATE_r0
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxRecDepth 2048

/- Aeneas-generated default heartbeat budget for the emitted definitions (no theorem below this line except the audit prints). -/
set_option maxHeartbeats 1000000

/- New-library model (Aeneas 0d21a9ec, backends/lean/Aeneas/Std/Core/CoreResult.lean, `core.result.Result.map_err`, copied verbatim): the L187 closure's Aeneas library lacks it.
   Same treatment as the branch/from_residual models in PIN2_NEWGATE_r0 (trust row HM-C, Option/Result). -/
namespace PCWN_NewLib
open Aeneas.Std
def core.result.Result.map_err
  {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F)
  (x : core.result.Result T E) (f : O) :
  Std.Result (core.result.Result T F) :=
  match x with
  | .Ok value => ok (.Ok value)
  | .Err error => do
      let mapped ← fnOnce.call_once f error
      ok (.Err mapped)
end PCWN_NewLib

namespace AspisR1PublicPreparationPIN2

'''%(raw['Types.lean'],raw['Funs.lean'])
txt=hdr+'\n\n'.join(out)+'\n\nend AspisR1PublicPreparationPIN2\n\nset_option maxHeartbeats 200000\n'
txt+='#print axioms AspisR1PublicPreparationPIN2.r1_semantic.public_transcript\n#print axioms AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new\n'
assert 'so'+'rry' not in txt
open('PIN2_NEWGATE_r1_semantic.lean','w').write(txt)
json.dump(dict(kept=kept,dropped=dropped,same_name_different_text=diffs,sha256=sha(txt)),open('PCXU_NEWGATE_DECLS.json','w'),indent=1)
print(len(txt),sha(txt),'kept',len(kept),'dropped',len(dropped),'diff',diffs)
