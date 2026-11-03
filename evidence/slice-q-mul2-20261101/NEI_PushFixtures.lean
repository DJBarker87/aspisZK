import NEG_PushActual.Funs
open Aeneas Aeneas.Std Result
namespace NEI_PushFixtures
def pushes : Result (List (List Nat)) := do
  let p0 ← NEG_PushActual.BatchedWeights.push ⟨⟨[ Array.make 4#usize [ 2147483648#u64, 2147483649#u64, 2147483650#u64, 2147483651#u64 ], Array.make 4#usize [ 2147483652#u64, 2147483653#u64, 2147483654#u64, 2147483655#u64 ], Array.make 4#usize [ 2147483656#u64, 2147483657#u64, 2147483658#u64, 2147483659#u64 ] ],by scalar_tac⟩,3#usize⟩ 0#usize ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ 0#u32
  let p1 ← NEG_PushActual.BatchedWeights.push ⟨⟨[ Array.make 4#usize [ 2147483648#u64, 2147483649#u64, 2147483650#u64, 2147483651#u64 ], Array.make 4#usize [ 2147483652#u64, 2147483653#u64, 2147483654#u64, 2147483655#u64 ], Array.make 4#usize [ 2147483656#u64, 2147483657#u64, 2147483658#u64, 2147483659#u64 ] ],by scalar_tac⟩,0#usize⟩ 1#usize ⟨⟨640585266#u32,1401694993#u32⟩,⟨590844326#u32,1645146169#u32⟩⟩ 1330129639#u32
  let p2 ← NEG_PushActual.BatchedWeights.push ⟨⟨[ Array.make 4#usize [ 2147483648#u64, 2147483649#u64, 2147483650#u64, 2147483651#u64 ], Array.make 4#usize [ 2147483652#u64, 2147483653#u64, 2147483654#u64, 2147483655#u64 ], Array.make 4#usize [ 2147483656#u64, 2147483657#u64, 2147483658#u64, 2147483659#u64 ] ],by scalar_tac⟩,1#usize⟩ 2#usize ⟨⟨684116573#u32,1654619725#u32⟩,⟨486239895#u32,1644828829#u32⟩⟩ 583974315#u32
  let p3 ← NEG_PushActual.BatchedWeights.push ⟨⟨[ Array.make 4#usize [ 2147483648#u64, 2147483649#u64, 2147483650#u64, 2147483651#u64 ], Array.make 4#usize [ 2147483652#u64, 2147483653#u64, 2147483654#u64, 2147483655#u64 ], Array.make 4#usize [ 2147483656#u64, 2147483657#u64, 2147483658#u64, 2147483659#u64 ] ],by scalar_tac⟩,2#usize⟩ 0#usize ⟨⟨1021504709#u32,548257143#u32⟩,⟨1580574866#u32,564381121#u32⟩⟩ 668630530#u32
  let p4 ← NEG_PushActual.BatchedWeights.push ⟨⟨[ Array.make 4#usize [ 2147483648#u64, 2147483649#u64, 2147483650#u64, 2147483651#u64 ], Array.make 4#usize [ 2147483652#u64, 2147483653#u64, 2147483654#u64, 2147483655#u64 ], Array.make 4#usize [ 2147483656#u64, 2147483657#u64, 2147483658#u64, 2147483659#u64 ] ],by scalar_tac⟩,3#usize⟩ 1#usize ⟨⟨915903750#u32,1814733430#u32⟩,⟨1000707960#u32,852600189#u32⟩⟩ 1283590606#u32
  let p5 ← NEG_PushActual.BatchedWeights.push ⟨⟨[ Array.make 4#usize [ 2147483648#u64, 2147483649#u64, 2147483650#u64, 2147483651#u64 ], Array.make 4#usize [ 2147483652#u64, 2147483653#u64, 2147483654#u64, 2147483655#u64 ], Array.make 4#usize [ 2147483656#u64, 2147483657#u64, 2147483658#u64, 2147483659#u64 ] ],by scalar_tac⟩,7#usize⟩ 2#usize ⟨⟨1064571478#u32,2004815668#u32⟩,⟨1811781566#u32,76271588#u32⟩⟩ 1023605638#u32
  ok [ (p0.raw.val.flatMap (fun r=>r.val.map (fun x=>x.val))) ++ [p0.terms.val], (p1.raw.val.flatMap (fun r=>r.val.map (fun x=>x.val))) ++ [p1.terms.val], (p2.raw.val.flatMap (fun r=>r.val.map (fun x=>x.val))) ++ [p2.terms.val], (p3.raw.val.flatMap (fun r=>r.val.map (fun x=>x.val))) ++ [p3.terms.val], (p4.raw.val.flatMap (fun r=>r.val.map (fun x=>x.val))) ++ [p4.terms.val], (p5.raw.val.flatMap (fun r=>r.val.map (fun x=>x.val))) ++ [p5.terms.val] ]
#eval pushes
def caller64 : Result (List Nat) := do
 let zero := Array.make 4#usize [0#u64,0#u64,0#u64,0#u64]
 let initial : NEG_PushActual.BatchedWeights := ⟨⟨List.replicate 64 zero,by scalar_tac⟩,3#usize⟩
 let out ← NEG_PushActual.BatchedWeights.push initial 23#usize ⟨⟨1#u32,2#u32⟩,⟨3#u32,4#u32⟩⟩ 5#u32
 ok ((out.raw.val.flatMap fun row => row.val.map fun word => word.val) ++ [out.terms.val])
#eval caller64
end NEI_PushFixtures
