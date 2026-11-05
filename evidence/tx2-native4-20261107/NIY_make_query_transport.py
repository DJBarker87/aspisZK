from NIY_port_tools import E,head
ops=[]
for i in range(22):ops += [f'let (a{i+5}, r{i+13}) ← RAW r{i+12}',f'let i{i+8} ← lift (core.num.U32.from_le_bytes a{i+5})']
arr='(Array.make 22#usize ['+', '.join('i'+str(i) for i in range(8,30))+'])'
ns='NIY_QueryTransport';out=head(ns,['NIY_QueryRead','NIY_RawTransport'])+'''
/-- Read22 transports the exact ordered array and reader to an arbitrary continuation.
Every primitive is one raw4 read; failures and divergence keep their original position. -/
theorem continuation {A B : Type} (f : A → B) (r12 : Fresh.R)
 (left : Array U32 22#usize → Fresh.R → Result A)
 (right : Array U32 22#usize → Cohort.R → Result B)
 (h : ∀ q out,outer f (left q (unReader out))=right q out) :
 outer f (do let (q,out) ← NIY_QueryRead.read22 (NIL_FreshOps.raw 4#usize) r12;left q out)=
 (do let (q,out) ← NIY_QueryRead.read22 (CheckpointBytes3Reader.raw 4#usize) (reader r12);right q out) := by
 have fresh := NIY_QueryRead.continuation (NIL_FreshOps.raw 4#usize) r12 left
 have cohort := NIY_QueryRead.continuation (CheckpointBytes3Reader.raw 4#usize) (reader r12) right
 apply Eq.trans (congrArg (outer f) fresh)
 apply Eq.trans ?_ cohort.symm
'''
for i in range(22):
 out+=' apply NIY_RawTransport.raw\n'+f' intro a{i+5} r{i+13}\n'
 out+=' apply NIL_ResultCases.map_bind_congr\n'+f' intro i{i+8}\n'
out+=' exact h '+arr+' r34\n#print axioms continuation\nend '+ns+'\n'
(E/(ns+'.lean')).write_text(out)
print('Authored ordered read22 transport as 22 named raw4 continuation steps, with exact failure positions and reader end.')
