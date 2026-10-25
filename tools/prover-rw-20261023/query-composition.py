#!/usr/bin/env python3
"""Pin proof-only caller copies to literal emitted declarations and substitutions."""
from pathlib import Path
import argparse, hashlib, json, re
ROOT=Path(__file__).resolve().parents[2]
SRC=ROOT/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
OUT=ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z'
JOBS=[
 ('ProverRwQueryOpening','prover.finish_opening','opening','host_transcript.Transcript.queries','ProverRwQueryInstalled.query','ProverRwQueryInstalled','opening_exact', '''(variant : transport.Variant)
    (h : Slice (Slice U8) → Result (Array U8 32#usize))
    (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts)''','variant h prepared salts','ProverRwQueryInstalled.query_exact'),
 ('ProverRwQuerySemantics','prover.prove_from_semantics','semantics','prover.finish_opening','ProverRwQueryOpening.opening','ProverRwQueryOpening','semantics_exact', '''(pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (h : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (salts : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
      aspis_core.state_only_hiding.StateOnlyHidingContext)''','pub variant h backend sem salts','ProverRwQueryOpening.opening_exact'),
 ('ProverRwQueryAttempt','prover.prove_masked_with_attempt','attempt','prover.prove_from_semantics','ProverRwQuerySemantics.semantics','ProverRwQuerySemantics','attempt_exact', '''{T : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (variant : transport.Variant) (h : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize)
    (secret : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : T)''','store pub compiled variant h context binding secret s','ProverRwQuerySemantics.semantics_exact'),
 ('ProverRwQueryNativeAttempt','prover.prove_masked_attempt','nativeAttempt','prover.prove_masked_with_attempt','ProverRwQueryAttempt.attempt','ProverRwQueryAttempt','native_attempt_exact', '(pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)\n    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)\n    (variant : transport.Variant) (h : Slice (Slice U8) → Result (Array U8 32#usize))\n    (secret : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)\n    (s : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)', 'pub compiled variant h secret s','ProverRwQueryAttempt.attempt_exact'),
]
def build(job):
 module,source,name,old,new,imp,thm,params,args,lemma=job
 text=SRC.read_text(); start=text.index('def '+source+'\n'); end=text.index('\n/--',start)
 decl=text[start:end].rstrip()
 # Replace only actual call tokens; preserve closure/error mapper paths verbatim.
 pattern=r'(?<![\w.])'+re.escape(old)+r'(?![\w.])'
 assert len(re.findall(pattern,decl))==1,(source,old)
 body=re.sub(pattern,new,decl).replace('def '+source+'\n','def '+name+'\n',1)
 output=f'''import R1Z.{imp}
/-! Exact emitted caller with its proved query component installed. Generated
by tools/prover-rw-20261023/query-composition.py; no native source change. -/
set_option autoImplicit false
namespace R1Z.{module}
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

{body}

set_option backward.isDefEq.respectTransparency false in
theorem {thm} {params} :
    {source} {args} = {name} {args} := by
  simp only [{source},{name},{lemma}]
  try rfl

#print axioms {thm}
end R1Z.{module}
'''
 return OUT/(module+'.lean'),output,dict(module=module,source_declaration=source,source_sha256=hashlib.sha256(decl.encode()).hexdigest(),lines=len(decl.splitlines()),substitution=dict(old=old,new=new),theorem=thm)
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
rows=[]
for job in JOBS:
 path,content,row=build(job); rows.append(row)
 if args.check: assert path.read_text()==content,path
 else:path.write_text(content)
print(json.dumps(dict(source=str(SRC.relative_to(ROOT)),sha256=hashlib.sha256(SRC.read_bytes()).hexdigest(),check=args.check,declarations=rows),indent=2))
