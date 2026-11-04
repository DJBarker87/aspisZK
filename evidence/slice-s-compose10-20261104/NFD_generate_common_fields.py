from pathlib import Path
E=Path(__file__).resolve().parent
ex=['(get a.master_account j).val','(get a.checkpoint_account j).val','(get a.selected_lane_account j).val','a.selected_lane.lane_id.val','a.checkpoint.checkpoint_sequence.val','(get a.checkpoint.global_root i).val','(get a.live_snapshot.pool j).val','(get a.live_snapshot.deployment_domain j).val','a.live_snapshot.sequence.val','a.live_snapshot.next_pair_index.val','(get a.live_snapshot.current_root i).val','(get (get a.live_snapshot.frontier k) i).val','c.next_pair_index.val','(get c.next_root i).val','(get (get c.next_frontier k) i).val']
for slot in range(15):
 ns=f'NFD_CommonField{slot:02}'
 text='''import NEU_CommonProjections
set_option autoImplicit false
noncomputable section
namespace '''+ns+'''
open Aeneas Aeneas.Std NEU_ReconstructCore
open NEU_PublicProjections (get)
def expected (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  '''+ex[slot]+'''
theorem alignment (a : Auth) (c : Candidate) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NEU_CommonProjections.value (common a c) ⟨'''+str(slot)+''',by decide⟩ i j k = expected a c i j k := rfl
#print axioms alignment
end '''+ns+'\n'
 (E/(ns+'.lean')).write_text(text)
