#!/usr/bin/env python3
"""Consume the existing eight source first-stop constructors, without re-parsing."""
from pathlib import Path
import argparse,hashlib,json
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
S=B/'lean-candidates/s126-caller-boundary-20261021'
E=B/'evidence/s126-current-caller-20261021'
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
text='''import S1QueryScanModelStepV1
import Query31ConcreteDriverTraceFacts
set_option autoImplicit false
noncomputable section
namespace AspisS1QueryScanModel
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SourceDuplexStep
open AspisV8R19.Q22WordScan
open Query31ExplicitScanBody Query31ExplicitListLoop Query31ModelScanCall
open Query31ConcreteWordsDriverChain

/-- ACCEPTED-ONLY: the existing source driver's SAME successful result
identifies both the ordered queries and the selected mathematical state.
The zero-draw premise is discharged by the concrete default wrapper below. -/
theorem driver_trace_scanOut (blocks advances : Blocks8) (s0 : QueryScan)
    (accepted : Array U32 22#usize) (next : Bytes32) (start : State)
    (valid : validState s0) (zeroDraws : s0.draws.val=0)
    (trace : AspisR1Query31Transcript.DriverTrace (modelScanFn actualQueryWords)
      blocks advances s0 accepted next) :
    R0C.V3.Q22.scanOut 8 (q22StateOf s0)
      (statesFrom blocks 0) (statesFrom advances 0) start=
        (.ok (accepted.val.map (fun w => w.val)),decodeState next) := by
  cases trace with
'''
for k in range(8):
 argslist=' '.join(f'b{i} s{i+1}' for i in range(k+1))
 if k==7:argslist+=' lastStop'
 argslist+=' '+' '.join(f'hblock{i}' for i in range(k+1))
 argslist+=' '+' '.join(f'hscan{i}' for i in range(k+1))+' hfinish hadvance'
 text+=f'  | stop{k} {argslist} =>\n'
 text+='    have valid0 := valid\n'
 for i in range(k+1):
  stop='lastStop' if i==7 else ('true' if i==k else 'false')
  text+=f'    have valid{i+1} := (source_scan_math s{i} s{i+1} b{i} {stop} valid{i} hscan{i}).2\n'
  text+=f'    have bound{i+1} := source_scan_draw_le s{i} s{i+1} b{i} {stop} valid{i} hscan{i}\n'
  text+=f'    have draw{i} : s{i}.draws.val<64 := by omega\n'
  state='start' if i==0 else f'(decodeState (blockAt advances {i-1}#usize (by decide)))'
  text+=f'    have step{i} := scanOut_source_step {7-i} s{i} s{i+1} blocks advances {i}#usize (by decide) b{i} {stop} {state} valid{i} draw{i} hblock{i} hscan{i}\n'
  text+=f'    simp only [show ({i}#usize : Usize).val={i} from by scalar_tac] at step{i}\n'
  text+=f'    rw [step{i}]\n'
  if i<7:text+='    simp only [Bool.false_eq_true,if_false,if_true]\n'
 text+=f'    have nextEq : blockAt advances {k}#usize (by decide)=next :=\n      Result.ok.inj ((blockAt_selected advances {k}#usize (by decide)).symm.trans hadvance)\n'
 if k==7:text+='    cases lastStop <;> simp only [Bool.false_eq_true,if_false,if_true,R0C.V3.Q22.scanOut]\n    all_goals\n      rw [source_finish_math _ _ hfinish,nextEq]\n'
 else:text+='    rw [source_finish_math _ _ hfinish,nextEq]\n'
text+='''
/-- Concrete default state: no separate valid-state or counter premise. -/
theorem default_driver_scanOut (blocks advances : Blocks8)
    (accepted : Array U32 22#usize) (next : Bytes32) (start : State)
    (success : AspisR1Query31Transcript.queries_from_pairs_with_scan
      (modelScanFn actualQueryWords) Query31ConcreteDriverTraceFacts.sourceDefaultState
      blocks advances=ok (.Ok (accepted,next))) :
    R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0
      (blocks.val.map decodeState) (advances.val.map decodeState) start=
        (.ok (accepted.val.map (fun w => w.val)),decodeState next) := by
  have trace := AspisR1Query31Transcript.successful_driver_has_trace _ _ _ _ _ _ success
  have result := driver_trace_scanOut blocks advances _ accepted next start
    Query31ConcreteDriverTraceFacts.sourceDefaultState_valid rfl trace
  simpa only [Query31ConcreteDriverTraceFacts.sourceDefaultState_maps_to_empty_q22,
    R0C.V3.Q22.q0,statesFrom,List.drop_zero] using result

#print axioms driver_trace_scanOut
#print axioms default_driver_scanOut
end AspisS1QueryScanModel
'''
output=S/'S1QueryScanDriverModelV1.lean'
if args.check:assert output.read_text()==text
else:output.write_text(text)
print(json.dumps({'target':output.name,'sha256':hashlib.sha256(text.encode()).hexdigest(),'check':args.check}))
