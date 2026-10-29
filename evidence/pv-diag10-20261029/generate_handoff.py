from pathlib import Path
import json
D=Path(__file__).parent
text='''import PV_DIAG10_Observer
import PV_DIAG10_Requests
import PV_DIAG10_Operands
import PV_DIAG10_Reached
import PV_DIAG9_Handoff
set_option autoImplicit false
namespace PV_DIAG10
open PV_RJ4IDB
variable {I P A : Type}
/-! Exact top-down composition. Native readout/event-order and public joint
producers are retained as P links. No terminal follows from the three channels. -/
'''
common=''' (files : I → List FileOp) (json : I → List Bytes × List (Bytes × Bytes))
 (errors : I → List PV_DIAG2.Effect × List PV_DIAG3.Event)
 (native : I → NativeTrace A) (raw : I → List NativeEvent)
 (fr : PV_DIAG10_Link_Readout files sourceFile raw)
 (jr : PV_DIAG10_Link_Readout json sourceJSON raw)
 (er : PV_DIAG10_Link_Readout errors sourceError raw)
 (order : PV_DIAG10_Link_EventOrder raw native)'''
steps=[('all_three_exact_inputs','theorem all_three_exact_inputs'+common+''' :
 OpenInputs.DIAG_FILE_TRACE files native ∧
 OpenInputs.DIAG_JSON_STDOUT_TRACE json native ∧
 OpenInputs.DIAG_ERROR_STDERR_TRACE errors native :=
 ⟨file_acquisition_from_source_links files native raw fr order,
 json_acquisition_from_source_links json native raw jr order,
 error_acquisition_from_source_links errors native raw er order⟩''')]
for name,typ,source,acq,old in [
 ('files','List FileOp','sourceFile','file_acquisition_from_source_links','file_acquisition_public'),
 ('json','List Bytes × List (Bytes × Bytes)','sourceJSON','json_acquisition_from_source_links','json_stdout_acquisition_public'),
 ('errors','List PV_DIAG2.Effect × List PV_DIAG3.Event','sourceError','error_acquisition_from_source_links','error_stderr_acquisition_public')]:
 steps.append((name+'_public_from_source',f'''theorem {name}_public_from_source (context : I → P) (actual : I → {typ})
 (native : I → NativeTrace A) (raw : I → List NativeEvent)
 (readout : PV_DIAG10_Link_Readout actual {source} raw)
 (order : PV_DIAG10_Link_EventOrder raw native)
 (publicEvents : ∀ i j, context i=context j → (native i).events=(native j).events)
 (i j : I) (h : context i=context j) : actual i=actual j :=
 PV_DIAG9.{old} context actual native
 ({acq} actual native raw readout order) publicEvents i j h'''))
steps.append(('joint_channels_from_source','theorem joint_channels_from_source (context : I → P)'+common+'''
 (publicEvents : ∀ i j, context i=context j → (native i).events=(native j).events)
 (i j : I) (h : context i=context j) :
 (files i,json i,errors i)=(files j,json j,errors j) := by
 obtain ⟨hf,hj,he⟩ := all_three_exact_inputs files json errors native raw fr jr er order
 exact PV_DIAG9.DIAG9_inputs_given_native_binding context files json errors native
   hf hj he publicEvents i j h'''))
steps.extend([
 ('terminal_and_events_determine_trace','''theorem terminal_and_events_determine_trace (a b : NativeTrace A)
 (events : a.events=b.events) (terminal : a.terminal=b.terminal) : a=b := by
 cases a
 cases b
 cases events
 cases terminal
 rfl'''),
 ('complete_decoder_retains_terminal','''theorem complete_decoder_retains_terminal (a b : NativeTrace A)
 (events : a.events=b.events) (terminal : a.terminal=b.terminal) :
 decoder (modelTrace a)=decoder (modelTrace b) :=
 congrArg (fun t => decoder (modelTrace t)) (terminal_and_events_determine_trace a b events terminal)'''),
 ('file_prefix_recovery','''theorem file_prefix_recovery (before after : List NativeEvent) :
 nativeFiles (before++after)=nativeFiles before++nativeFiles after :=
 PV_DIAG9.prefix_files_retained before after'''),
 ('json_stdout_prefix_recovery','''theorem json_stdout_prefix_recovery (before after : List NativeEvent) :
 nativeJSON (before++after)=nativeJSON before++nativeJSON after ∧
 nativeStdout (before++after)=nativeStdout before++nativeStdout after := by
 simp only [nativeJSON,nativeStdout,List.filterMap_append,and_self]'''),
 ('error_prefix_recovery','''theorem error_prefix_recovery (before after : List NativeEvent) :
 nativeDiag2 (before++after)=nativeDiag2 before++nativeDiag2 after ∧
 nativeDiag3 (before++after)=nativeDiag3 before++nativeDiag3 after :=
 PV_DIAG9.prefix_diagnostics_retained before after''')])
plans=[]
for name,decl in steps:
 text+=decl+'\n#print axioms '+name+'\n';plans.append(text+'end PV_DIAG10\n')
(D/'handoff-plans.json').write_text(json.dumps({'PV_DIAG10_Handoff':plans},indent=2)+'\n')
(D/'PV_DIAG10_Handoff.lean').write_text(plans[-1])
