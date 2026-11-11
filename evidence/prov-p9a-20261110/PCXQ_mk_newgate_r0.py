#!/usr/bin/env python3
"""PCXQ: PIN2_NEWGATE_r0.lean from the PCXQ_E001 emission (Types ++ Funs), namespace AspisR1PublicPreparationPIN2. Transformations (only these):
Aeneas registration attributes rust_type/rust_const/rust_loop/rust_loop_body removed; `module`/`public import`/`@[expose] public section` headers dropped
(one file); Result.branch / Result.from_residual qualified to the PCWN_NewLib block (new-library names, see PRVEq_PB_w3 notes). No semantic edit."""
import re,sys,json,hashlib,subprocess
sys.dont_write_bytecode=True
D='PCXQ_E001_emitted/raw/PCXQ_r0/'
sha=lambda b:hashlib.sha256(b if isinstance(b,bytes) else b.encode()).hexdigest()
w3=open('PCXQ_prev_PRVEq_PB_w3.lean').read()
newlib=w3[w3.index('namespace PCWN_NewLib'):w3.index('end PCWN_NewLib')+len('end PCWN_NewLib')]
def body(f):
    s=open(D+f).read();a=s.index('namespace PCXQ_r0')+len('namespace PCXQ_r0');b=s.rindex('end PCXQ_r0')
    t=s[a:b]
    t=re.sub(r'(?m)^@\[rust_loop_body\]\n','',t);t=re.sub(r'(?m)^@\[rust_loop\]\n','',t)
    t=re.sub(r',\s*rust_(?:type|const)\s+"[^"]*"','',t)
    t=re.sub(r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTry\.branch','PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch',t)
    t=re.sub(r'(?<![\w.])core\.result\.Result\.Insts\.CoreOpsTry_traitFromResidualResult\.from_residual','PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual',t)
    return t
hdr='''-- PIN2 NEW GATE for the r0 module (public_bytes root) at source 271869c946d4286db6ee5be784f136599fa8707e (W1 fix/pin2-verifier-20261110).
-- Emission PCXQ_E001: Charon 454586e9 + Aeneas 0d21a9ec (second tool version), overflow-checks ON, features r0,pool-v1-kernel,+audit set, cargo --jobs 4 / CARGO_BUILD_JOBS=4, rustc -Zthreads=1,
-- --include aspis_core::field::P, identity by class receipt PCWE_E003. Raw emission sha256: Types.lean %s Funs.lean %s
-- Built by PCXQ_mk_newgate_r0.py (transformations listed there). Contains no placeholder proof and no axiom.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxRecDepth 2048

'''%(sha(open(D+'Types.lean','rb').read()),sha(open(D+'Funs.lean','rb').read()))
out=hdr+newlib+'\n\n/- Aeneas-generated default heartbeat budget for the emitted definitions (no theorem below this line except the audit prints). -/\nset_option maxHeartbeats 1000000\n\nnamespace AspisR1PublicPreparationPIN2\n'+body('Types.lean')+'\n'+body('Funs.lean')+'\nend AspisR1PublicPreparationPIN2\n\nset_option maxHeartbeats 200000\n'
for n in ['private_public','withdrawal_public','r0.Public.semantic','r0.Public.public_bytes']:
    out+='#print axioms AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.'+n+'\n'
open('PIN2_NEWGATE_r0.lean','w').write(out);print(len(out),sha(out))
