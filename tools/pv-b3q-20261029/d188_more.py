from pathlib import Path
import json
D=Path('evidence/pv-b3q-20261029/lean');T=Path('tools/pv-b3q-20261029/d188')
q=lambda n:'{ c0 := { a := '+str(n)+'#u32, b := '+str(n*17)+'#u32 }, c1 := { a := '+str(n*31)+'#u32, b := '+str(n*47)+'#u32 } }'
a=lambda n,b:'(Array.make '+str(n)+'#usize ['+', '.join(q(b+i)for i in range(n))+'] (by rfl))'
base='''import PV_B3P_P227_14
namespace MODULE
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def report {n : Usize} (r : Result (Array aspis_core.field.QM31 n)) : String :=
 match r with
 | .ok xs => reprStr (xs.val.flatMap (fun q => [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]))
 | .fail _ => "FAIL"
 | .div => "DIV"
'''
for ix in range(10,15):
 m='PV_B3Q_D188Fixture'+str(ix);s=base.replace('MODULE',m)
 if ix==10:
  s+='''def public (variant : reference_terminal.CompiledVariant) : reference_terminal.SemanticPublic :=
 let bytes := Array.repeat 32#usize 0#u8
 let digest := Array.repeat 8#usize 0#u32
 let frontier := Array.repeat 20#usize digest
 { variant := variant, pool := bytes, deployment_domain := bytes, anchor := digest,
   nullifier := digest, asset_id := 0#u32, recipient := none, change := digest,
   withdrawal_amount := none, transition := {
     live_snapshot := { pool := bytes, deployment_domain := bytes, sequence := 0#u64,
       next_pair_index := 0#u64, current_root := digest, frontier := frontier },
     candidate_afterstate := { next_pair_index := 0#u64, next_root := digest, next_frontier := frontier } } }
'''
 for seed in [0,1,7,19]:
  n=(seed+1)*131;state=a(16,n);opening='{ z := '+state+', succ_z := '+a(16,n+20)+', xor12_z := '+a(16,n+40)+' }';selectors='{ high := '+a(64,n+100)+', low := '+state+' }'
  if ix==10:
   for variant,label in [('PrivateTransfer','private'),('Withdrawal','withdrawal')]:
    expr='(do let (initial,absorption) ← reference_terminal.semantic_initial_and_absorption (public .'+variant+') ('+opening+') ('+selectors+'); .ok (Array.make 32#usize (initial.val ++ absorption.val) (by simp only [List.length_append,initial.property,absorption.property]; rfl)))'
    s+='#eval "semantic_initial_'+label+':'+str(seed)+'=" ++ report ('+expr+')\n'
  elif ix in[11,12]:
   prefix='host_terminal_field'if ix==11 else'reference_field'
   for length in [0,1,2,3,4]:
    s+='#eval "'+prefix+'_pack'+str(length)+':'+str(seed)+'=" ++ report (do let value ← '+prefix+'.qm31_pack_base4 (Array.to_slice '+a(length,n)+'); .ok (Array.make 1#usize [value] (by rfl)))\n'
  elif ix==13:
   rows='(Array.make 3#usize ['+', '.join(a(29,n+r*29)for r in range(3))+'] (by rfl))'
   s+='#eval "select227:'+str(seed)+'=" ++ report (reference_terminal.select227 '+rows+')\n'
  else:
   s+='#eval "mask_fragment:'+str(seed)+'=" ++ report (reference_terminal.composition_parts_loop0 '+a(84,n)+' (Array.repeat 10#usize aspis_core.field.QM31.ZERO) 0#usize)\n'
 s+='end '+m+'\n';(D/(m+'.lean')).write_text(s)
suffix='''
// D500 extra D188 observation roots. Original owned source remains a byte prefix.
pub fn observe_more(seed:u32){
 let n=(seed+1)*131;
 let claims=core::array::from_fn(|r|core::array::from_fn(|c|crate::q(n+r as u32*29+c as u32)));
 let selected=select227(claims);assert_ne!(selected,[QM31::ZERO;84]);crate::emit("select227",seed,&selected);
 let flat=core::array::from_fn(|i|crate::q(n+i as u32));
 let mask_only=qm31_array!(STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,column,{selected_claim(&flat,0,POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1+column)});
 assert_ne!(mask_only,[QM31::ZERO;10]);crate::emit("mask_fragment",seed,&mask_only);
 use aspis_statement::pool_v1::pair_tree_profile::{PoolV1PairLiveSnapshotV1,PoolV1PairLatePublicStatementV1};
 use aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1;
 let digest=[M31(0);8];let frontier=[digest;20];
 let transition=PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:[0;32],deployment_domain:[0;32],sequence:0,next_pair_index:0,current_root:digest,frontier},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:0,next_root:digest,next_frontier:frontier}};
 for (variant,label) in [(CompiledVariant::PrivateTransfer,"private"),(CompiledVariant::Withdrawal,"withdrawal")] {
  let p=SemanticPublic{variant,pool:[0;32],deployment_domain:[0;32],anchor:digest,nullifier:digest,asset_id:M31(0),recipient:None,change:digest,withdrawal_amount:None,transition};
  let (initial,absorption)=semantic_initial_and_absorption(p,&crate::openings(n),&crate::selectors(n));assert_ne!(initial,[QM31::ZERO;16]);assert_ne!(absorption,[QM31::ZERO;16]);
  let values:Vec<QM31>=initial.into_iter().chain(absorption).collect();crate::emit(&format!("semantic_initial_{label}"),seed,&values);
 }
}
'''
p=T/'reference_terminal.rs';text=p.read_text();assert '// D500 extra D188 observation roots.'not in text;p.write_text(text+suffix)
p=T/'main.rs';text=p.read_text();text=text.replace('reference_copy_terminal::observe(seed);','''reference_copy_terminal::observe(seed);reference_terminal::observe_more(seed);
 let n=(seed+1)*131;let values:[QM31;4]=core::array::from_fn(|i|q(n+i as u32));
 for length in 0..=4 {let h=host_terminal_field::qm31_pack_base4(&values[..length]);let r=reference_field::qm31_pack_base4(&values[..length]);assert_eq!(h,r);if length>0 {assert_ne!(r,QM31::ZERO);}
 emit(&format!("host_terminal_field_pack{length}"),seed,&[h]);emit(&format!("reference_field_pack{length}"),seed,&[r]);}
''');p.write_text(text)
