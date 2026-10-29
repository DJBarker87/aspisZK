from pathlib import Path
import json
D=Path(__file__).parent
text='''import PV_DIAG10_FILE
import PV_DIAG10_JSON_STDOUT
import PV_DIAG10_ERROR_STDERR
set_option autoImplicit false
namespace PV_DIAG10
open PV_RJ4IDB
/-! The source-model observer is the EXISTING decoder on translated events.
Its local links are proved here. Readout/EventOrder for deployed execution are
not constructed by defining a model observer. All abnormal prefixes remain. -/
def sourceFile {I : Type} (_ : I) (es : List NativeEvent) := files (es.map translateEvent)
def sourceJSON {I : Type} (_ : I) (es : List NativeEvent) :=
 (json (es.map translateEvent),stdout (es.map translateEvent))
def sourceError {I : Type} (_ : I) (es : List NativeEvent) :=
 (diagnostics2 (es.map translateEvent),diagnostics3 (es.map translateEvent))
'''
steps=[]
for tag,state,proj,defs,trans,join in [
 ('file','sourceFile','nativeFiles','sourceFile','nativeFiles_translation','List.append'),
 ('json','sourceJSON','(fun es => (nativeJSON es,nativeStdout es))','sourceJSON','nativeJSON_translation,nativeStdout_translation','(fun a b => (a.1++b.1,a.2++b.2))'),
 ('error','sourceError','(fun es => (nativeDiag2 es,nativeDiag3 es))','sourceError','nativeDiag2_translation,nativeDiag3_translation','(fun a b => (a.1++b.1,a.2++b.2))')]:
 steps.append((tag+'_source_agrees',f'''theorem {tag}_source_agrees {{I : Type}} (i : I) (es : List NativeEvent) :
 {state} i es={proj} es := by
 simp only [{defs},{trans}]'''))
 steps.append((tag+'_init_link',f'''theorem {tag}_init_link {{I : Type}} :
 PV_DIAG10_Link_Init (@{state} I) ({proj} []) := by
 intro i
 exact {tag}_source_agrees i []'''))
 native={'file':'nativeFiles','json':'nativeJSON,nativeStdout','error':'nativeDiag2,nativeDiag3'}[tag]
 steps.append((tag+'_step_link',f'''theorem {tag}_step_link {{I : Type}} :
 PV_DIAG10_Link_Step (@{state} I) {join} (fun e => {proj} [e]) := by
 intro i es e
 rw [{tag}_source_agrees,{tag}_source_agrees]
 simp only [{native},List.filterMap_append] <;> rfl'''))
for tag,state,typ,theoremname in [
 ('file','sourceFile','List FileOp','DIAG_FILE_TRACE'),
 ('json','sourceJSON','List Bytes × List (Bytes × Bytes)','DIAG_JSON_STDOUT_TRACE'),
 ('error','sourceError','List PV_DIAG2.Effect × List PV_DIAG3.Event','DIAG_ERROR_STDERR_TRACE')]:
 steps.append((tag+'_acquisition_from_source_links',f'''theorem {tag}_acquisition_from_source_links {{I A : Type}}
 (actual : I → {typ}) (native : I → NativeTrace A) (raw : I → List NativeEvent)
 (readout : PV_DIAG10_Link_Readout actual {state} raw)
 (order : PV_DIAG10_Link_EventOrder raw native) :
 OpenInputs.{theoremname} actual native :=
 {theoremname} actual native raw {state} {tag}_init_link {tag}_step_link readout order'''))
# Diagnostic projection invariants for concrete event constructors; values remain arbitrary.
for name,event,proj,rhs in [
 ('proof_file_write','.proofWrite p a b','nativeFiles','[.write p a b]'),
 ('statement_file_write','.statementWrite p a b','nativeFiles','[.write p a b]'),
 ('stdout_partial_delivery','.printed a b','nativeStdout','[(a,b)]'),
 ('returned_json_bytes','.returned a','nativeJSON','[a]'),
 ('stderr_effect','.diag2 d','nativeDiag2','[d]'),
 ('crash_or_capture_event','.diag3 d','nativeDiag3','[d]')]:
 binders='(p a b : Bytes)' if 'file_write' in name else '(a b : Bytes)' if name=='stdout_partial_delivery' else '(a : Bytes)' if name=='returned_json_bytes' else '(d : PV_DIAG2.Effect)' if name=='stderr_effect' else '(d : PV_DIAG3.Event)'
 steps.append((name,f'theorem {name} {binders} : {proj} [{event}]={rhs} := rfl'))
steps.append(('count_is_separate_retained_channel','''theorem count_is_separate_retained_channel (n : Nat) :
 nativeCounts [.count n]=[n] ∧ nativeJSON [.count n]=[] ∧ nativeDiag2 [.count n]=[] :=
 ⟨rfl,rfl,rfl⟩'''))
steps.append(('terminal_does_not_change_file_acquisition','''theorem terminal_does_not_change_file_acquisition {A : Type}
 (es : List NativeEvent) (t u : Terminal A) :
 nativeFiles (NativeTrace.mk es t).events=nativeFiles (NativeTrace.mk es u).events := rfl'''))
plans=[]
for name,decl in steps:
 text+=decl+'\n#print axioms '+name+'\n';plans.append(text+'end PV_DIAG10\n')
(D/'observer-plans.json').write_text(json.dumps({'PV_DIAG10_Observer':plans},indent=2)+'\n')
(D/'PV_DIAG10_Observer.lean').write_text(plans[-1])
print(len(plans))
