from pathlib import Path
import re
E=Path(__file__).resolve().parent
text=(E/'NLF_SnapshotOccurrence.lean').read_text()
statement=text[text.index('    let p :='):text.index(' := by',text.index('    let p :='))]
for tx,count,first in [('TX1',3,452),('TX2',7,471)]:
 for i in range(count):
  prior='(['+','.join(map(str,range(i)))+'] : List Nat)'
  st=re.sub(r'\bprior\b',prior,statement);st=re.sub(r'\ba\b',str(i),st)
  st+=' ∧\n    h.ownerLive '+str(i)+'=true ∧ h.counter (h.accounts '+str(i)+').1=0'
  name=f'NLF_{tx}_Snapshot{i}'
  s=f'''import NLF_SnapshotOccurrence
set_option autoImplicit false
namespace {name}
open AspisR1 NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_RuntimeInterpretation NLF_SnapshotFold
/-- Frozen r1_pool_adapter_owned.rs:{first+i}. Snapshot's token ABI only;
owned Vec allocation/copy and later child calls remain with the parent owner. -/
theorem at_site {{F : Type}} (h : S2Trust.Heap F) (records : Nat → Account) (money : Nat → Nat)
    (runtime : AdapterRw.RuntimeEntrypointAdmission h (fun a => (records a).key) {count}) :
{st} := by
  have base := NLF_SnapshotOccurrence.packet h records money {prior} {i}
  dsimp only at base ⊢
  exact ⟨base.1,base.2.1,base.2.2.1,base.2.2.2,
    runtime.liveAccount {i} (by decide),runtime.counterZero {i} (by decide)⟩
#print axioms at_site
end {name}
'''
  (E/(name+'.lean')).write_text(s)
print('NLF generated ten source-occurrence token packets from one proved generic law')
