#!/usr/bin/env python3
from pathlib import Path
R=Path(__file__).resolve().parents[2];S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
s=(S/'S2OwnedStage1ReachabilityV1.lean').read_text().replace('import S2OwnedStage1ModelV1','import S2OwnedStage1ReachabilityV1').replace('AspisS2OwnedStage1.Reachability','AspisS2OwnedStage1.FrameReachability')
a=s.index('theorem first_decoded_success');b=s.index('/-- One enclosing',a);s=s[:a]+s[b:]
s=s.replace('theorem tail_success','theorem tail_frame').replace('first_decoded_success ops','Reachability.first_decoded_success ops').replace('#print axioms first_decoded_success\n','').replace('#print axioms tail_success','#print axioms tail_frame')
s=s.replace('ops.op1 checkedEnd solana_program_error.ProgramError.InvalidAccountData=ok (.Ok proofEnd) ∧','ops.op1 checkedEnd solana_program_error.ProgramError.InvalidAccountData=ok (.Ok proofEnd) ∧\n      alloc.vec.Vec.len proofData=proofEnd ∧')
s=s.replace('      core.slice.Slice.copy_from_slice core.marker.CopyU8 checkpointIn','      alloc.vec.Vec.len checkpoint=Slice.len checkpointIn ∧\n      core.slice.Slice.copy_from_slice core.marker.CopyU8 checkpointIn',1)
s=s.replace('                obtain ⟨frame,hframe,h⟩', '''                rename_i badLength
                have hProofLen : alloc.vec.Vec.len proofReadValue=proofEndValue := by
                  apply UScalar.eq_of_val_eq
                  simpa using badLength
                obtain ⟨frame,hframe,h⟩''',1)
s=s.replace('                        obtain ⟨copied,hcopied,h⟩','''                        rename_i badCheckpointLength
                        have hCheckpointLen : alloc.vec.Vec.len childValue=Slice.len checkpointIn := by
                          apply UScalar.eq_of_val_eq
                          simpa using badCheckpointLength
                        obtain ⟨copied,hcopied,h⟩''',1)
s=s.replace('hcheckedEnd,hproofEnd,hselected','hcheckedEnd,hproofEnd,hProofLen,hselected').replace('childValue hchild,hcopied','childValue hchild,hCheckpointLen,hcopied')
s=s.replace('SDK IO and child interpretations remain named Ops fields at this scope.', 'Length-guard conclusions are derived from this same execution, before slicing\nchecks; no successful-index or matching-checkpoint-length premise is supplied.\nSDK IO and child interpretations remain named Ops fields at this scope.')
(S/'S2OwnedFrameReachabilityV1.lean').write_text(s)
