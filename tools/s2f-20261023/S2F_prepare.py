from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2f-20261023'
paths=['programs/r1-cost-probe/src/r1_pool_adapter.rs',str((D/'evidence/s2e-20261023/S2E-reference/src/S2E_Reference.rs').relative_to(R)),str((D/'lean/S2E_Model.lean').relative_to(R)),str((D/'lean/S2TrustedSdkBorrow.lean').relative_to(R))]
(E/'S2F-stage0.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),sources={p:dict(sha256=hashlib.sha256((R/p).read_bytes()).hexdigest(),bytes=(R/p).stat().st_size) for p in paths},limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),budget=dict(lean=100,kani=60),scope='Per-source-step comparison; no whole-stage harness. Native SDK/runtime representation and concrete children remain explicit ports.'),indent=2)+'\n')
