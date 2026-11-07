from pathlib import Path
E=Path(__file__).resolve().parent
for ordinal,n,stem,lemma,div in [('Second',1,'NLQ_SnapshotLaterPrefixes','second_abort',False),('Second',1,'NLQ_SnapshotSecondDiv','second_div',True),('Third',2,'NLQ_SnapshotThirdPrefix','abort',False),('Third',2,'NLQ_SnapshotThirdDiv','diverge',True)]:
 name='NLQ_Stage1'+ordinal+('Div' if div else 'Abort')
 reply='.div'if div else'(.fail err)';errarg=''if div else' (err : Error)';a2=' (a2 : Result Unit)'if n==1 else''
 extent=str([58295,1880,1768][n]);owned='[e.snapshot 0 58295 58295'+(',e.snapshot 1 1880 1880'if n==2 else'')+']'
 allocs='(.ok ()) '+reply+' a2'if n==1 else'(.ok ()) (.ok ()) '+reply
 call=stem+'.'+lemma+' e'+(' err'if not div else'')+(' a2'if n==1 else'')+' extent'
 es='(NLM_Snapshot.G (ready e 0 []) 0 58295 58295 (.ok ())).events ++\n  '
 if n==2:es+='((NLM_Snapshot.G (ready e 1 [e.snapshot 0 58295 58295]) 1 1880 1880 (.ok ())).events ++\n  allocationPrefix s 2 '+reply+')'
 else:es+='allocationPrefix s 1 '+reply
 proof=' rw [NLQ_SnapshotReplay.append]\n'
 if n==2:proof+=' rw [NLQ_SnapshotReplay.append]\n'
 for _ in range(n):proof+=' rw [NLQ_ReplayNormal.normal,NLQ_SnapshotEvents.returned_ready]\n simp only [List.nil_append,List.cons_append,Nat.zero_add]\n'
 proof+=' rw [NLQ_ReplayAbort.allocation]\n'
 text=f'''import NLQ_Stage1Abort
import NLQ_ReplayNormal
import NLQ_SnapshotEvents
import {stem}
set_option autoImplicit false
noncomputable section
namespace {name}
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
open AspisR1.S2W_D189Entry NLM_Snapshot
/-- Exact full parent post and attempted prefix at allocation {n}. Prior
snapshots are completed at SAME arguments; the entered token remains LIVE.
This is a local branch lemma, not a root allocation-success premise. -/
theorem source (e : Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8){errarg}{a2}
 (extent : (S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles {n}).1)).length={extent}) :
 NLQ_Stage1Fold.G e ops p d {allocs} =
 let s := ready e {n} {owned}
 ⟨{reply},⟨{{s with sdk:=acquired s {n},next:=s.next+1}},none⟩,
  ({es}).map Event.snapshot⟩ := by
 unfold NLQ_Stage1Fold.G
 rw [{call}]
 dsimp only
{proof}#print source
#print axioms source
end {name}
'''
 (E/(name+'.lean')).write_text(text)
