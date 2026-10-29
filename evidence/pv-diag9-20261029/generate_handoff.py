from pathlib import Path
import json
D=Path(__file__).parent;m='PV_DIAG9_Handoff'
s='''import PV_DIAG9_Operands
import PV_DIAG9_World
import PV_RJ4IDB_OpenInputs
set_option autoImplicit false
namespace PV_DIAG9
open PV_RJ4IDB
/-! Uses the existing decoder's EXACT three acquisition Props. No instance of
these Props, public event binding, terminal binding, or V400 is asserted here.
I may index every prefix of a divergent run; no success restriction is used. -/
variable {I P A : Type}
'''
steps=[('file_acquisition_public','''theorem file_acquisition_public (pub : I → P) (actual : I → List FileOp)
 (native : I → NativeTrace A) (acquisition : OpenInputs.DIAG_FILE_TRACE actual native)
 (events : ∀ i j, pub i=pub j → (native i).events=(native j).events)
 (i j : I) (h : pub i=pub j) : actual i=actual j := by
 rw [acquisition i,acquisition j,events i j h]'''),
('json_stdout_acquisition_public','''theorem json_stdout_acquisition_public (pub : I → P)
 (actual : I → List Bytes × List (Bytes × Bytes)) (native : I → NativeTrace A)
 (acquisition : OpenInputs.DIAG_JSON_STDOUT_TRACE actual native)
 (events : ∀ i j, pub i=pub j → (native i).events=(native j).events)
 (i j : I) (h : pub i=pub j) : actual i=actual j := by
 rw [acquisition i,acquisition j,events i j h]'''),
('error_stderr_acquisition_public','''theorem error_stderr_acquisition_public (pub : I → P)
 (actual : I → List PV_DIAG2.Effect × List PV_DIAG3.Event) (native : I → NativeTrace A)
 (acquisition : OpenInputs.DIAG_ERROR_STDERR_TRACE actual native)
 (events : ∀ i j, pub i=pub j → (native i).events=(native j).events)
 (i j : I) (h : pub i=pub j) : actual i=actual j := by
 rw [acquisition i,acquisition j,events i j h]'''),
('DIAG9_inputs_given_native_binding','''theorem DIAG9_inputs_given_native_binding (pub : I → P)
 (files : I → List FileOp) (json : I → List Bytes × List (Bytes × Bytes))
 (errors : I → List PV_DIAG2.Effect × List PV_DIAG3.Event) (native : I → NativeTrace A)
 (fileBinding : OpenInputs.DIAG_FILE_TRACE files native)
 (jsonBinding : OpenInputs.DIAG_JSON_STDOUT_TRACE json native)
 (errorBinding : OpenInputs.DIAG_ERROR_STDERR_TRACE errors native)
 (publicEvents : ∀ i j, pub i=pub j → (native i).events=(native j).events)
 (i j : I) (h : pub i=pub j) :
 (files i,json i,errors i)=(files j,json j,errors j) := by
 rw [file_acquisition_public pub files native fileBinding publicEvents i j h,
 json_stdout_acquisition_public pub json native jsonBinding publicEvents i j h,
 error_stderr_acquisition_public pub errors native errorBinding publicEvents i j h]'''),
('decoder_given_complete_native_binding','''theorem decoder_given_complete_native_binding (pub : I → P) (native : I → NativeTrace A)
 (completeBinding : ∀ i j, pub i=pub j → native i=native j)
 (i j : I) (h : pub i=pub j) :
 decoder (modelTrace (native i))=decoder (modelTrace (native j)) :=
 congrArg (fun t => decoder (modelTrace t)) (completeBinding i j h)'''),
('native_factorization_retained','''theorem native_factorization_retained (native : I → NativeTrace A) :
 ∀ i, nativeObservation (native i)=decoder (modelTrace (native i)) :=
 PV_RJ4IDB.all_prefixes native'''),
('prefix_files_retained','''theorem prefix_files_retained (before after : List NativeEvent) :
 nativeFiles (before++after)=nativeFiles before++nativeFiles after := by
 simp only [nativeFiles,List.filterMap_append]'''),
('prefix_diagnostics_retained','''theorem prefix_diagnostics_retained (before after : List NativeEvent) :
 nativeDiag2 (before++after)=nativeDiag2 before++nativeDiag2 after ∧
 nativeDiag3 (before++after)=nativeDiag3 before++nativeDiag3 after := by
 simp only [nativeDiag2,nativeDiag3,List.filterMap_append,and_self]'''),
('partial_stdout_delivery_retained','''theorem partial_stdout_delivery_retained (requested delivered : Bytes) :
 nativeStdout [.printed requested delivered]=[(requested,delivered)] := rfl'''),
('terminal_not_supplied_by_three_channels','''theorem terminal_not_supplied_by_three_channels (es : List NativeEvent) (error : Bytes) :
 (⟨es,Terminal.success ()⟩ : NativeTrace Unit) ≠ ⟨es,Terminal.failure error⟩ := by
 intro h
 have ht := congrArg (fun t : NativeTrace Unit => t.terminal) h
 cases ht''')]
cs=[]
for n,d in steps:s+=d+'\n#print axioms '+n+'\n';cs.append(s+'end PV_DIAG9\n')
j=json.loads((D/'plans.json').read_text());j[m]=cs;(D/'plans.json').write_text(json.dumps(j,indent=2)+'\n');(D/(m+'.lean')).write_text(cs[-1])
