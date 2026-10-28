"""Named symbolic applications and exact row assertions. No concrete recurrence reduction."""
from pathlib import Path
import json,re,sys,hashlib
E=Path(__file__).resolve().parent;check='--check' in sys.argv
expected={}
def emit(n,imports,body,theorem='result'):
 m='KNA_'+n;expected[m]='\n'.join('import '+x for x in imports)+'\nset_option autoImplicit false\nnamespace '+m+'\nopen KMX_CopyMeaning KMY_WindowComposition\n'+body+'\n#print axioms '+theorem+'\nend '+m+'\n'
emit('Frame',['KMZ_Growth'],'''/-- A pointwise heap frame is the runtime interface; no allocation is inferred. -/
theorem result (before source after : Nat → Nat) (len size : Nat)
 (prefix : ∀ j, j<len → after j=before j)
 (tail : ∀ j, len≤j → j<len+size → after j=source (j-len)) :
 ∀ j, j<len+size → after j=(if j<len then before j else source (j-len)) := by
 intro j bound
 by_cases h : j<len
 · simpa only [if_pos h] using prefix j h
 · simpa only [if_neg h] using tail j (by omega) bound''')
emit('Partition',['KNA_Frame'],'''theorem result (j : Nat) (h : j<1768) :
 (j<1736 ∧ ∃ w, w<11 ∧ 160*w≤j ∧ j<min 1736 (160*(w+1))) ∨
 (1736≤j ∧ j<1768) := by
 by_cases p : j<1736
 · left
   refine ⟨p,j/160,?_,?_,?_⟩
   · omega
   · omega
   · omega
 · right; omega''')
# Focused positive domains, including the eleven required halved replacements.
for w in range(12):
 lo=160*w if w<11 else 1736;hi=min(1736,lo+160) if w<11 else 1768
 emit(f'Window{w:02}',['KNA_Frame'],f'''theorem result (before garbage answer : Nat → Nat) (j : Nat)
 (range : {lo}≤j ∧ j<{hi}) :
 window answer (loop before garbage 0 (min 1736 3472)) 1736 32 j =
 if j<1736 then before j else answer (j-1736) :=
 KMZ_Growth.append_after_growth before garbage answer 1736 1736 3472 32 j
 (by omega) (by omega) (by omega)''')
for w in range(11):
 lo=160*w;hi=min(1736,lo+160);mid=(lo+hi)//2
 emit(f'Halves{w:02}',['KNA_Frame'],f'''/-- Both new subwindows are necessary; a timeout on the parent gives no premise. -/
theorem result (actual expected : Nat → Nat)
 (left : ∀ j, {lo}≤j → j<{mid} → actual j=expected j)
 (right : ∀ j, {mid}≤j → j<{hi} → actual j=expected j) :
 ∀ j, {lo}≤j → j<{hi} → actual j=expected j := by
 intro j lower upper
 by_cases h : j<{mid}
 · exact left j lower h
 · exact right j (by omega) upper''')
for cap,lo,hi in [(128,1,16),(256,17,22)]:
 emit(f'Query{cap}',['KNA_Frame'],f'''theorem result (before garbage source : Nat → Nat) (i j : Nat)
 (domain : {lo}≤i ∧ i<{hi}) (bound : j<64+4*i+4) :
 64+4*i+4≤{cap} ∧
 window source (loop before garbage 0 (min {cap} {cap})) (64+4*i) 4 j =
 if j<64+4*i then before j else source (j-(64+4*i)) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage source (64+4*i) {cap} {cap} 4 j
     (by omega) (by omega) bound''')
# Exact original byte projections, retaining successful-growth premises.
for row,n,limit in [('LPm_K004',32,1704),('LPm_K005',4,1732),('LPi_K012',16,1720),('LPi_K013',32,1704),('LPm_K003',16,1720)]:
 selected=row=='LPm_K003';word=row=='LPm_K005';raw=row=='LPm_K004'
 args='(i cap next j : Nat) (idx : i<64)' if selected else '(len cap next j : Nat) (limit : len≤'+str(limit)+')'
 length='(712+16*i)' if selected else 'len'
 source='source' if raw else '(fun b => (word / 2^(8*b)) % 256)' if word else '(fun b => (limb (b/4) / 2^(8*(b%4))) % 256)'
 input_='source : Nat → Nat' if raw else 'word : Nat' if word else 'limb : Nat → Nat'
 rhs=f'source (j-{length})' if raw else f'(word / 2^(8*(j-{length}))) % 256' if word else f'(limb ((j-{length})/4) / 2^(8*((j-{length})%4))) % 256'
 emit(row,['KNA_Frame','KMY_CheckpointComposition'],f'''theorem result (before garbage : Nat → Nat) ({input_}) {args}
 (live : {length}≤cap) (growth : cap≤next) (bound : j<{length}+{n}) :
 {length}+{n}≤1736 ∧ window {source} (loop before garbage 0 (min cap next)) {length} {n} j =
 (if j<{length} then before j else {rhs}) := by
 constructor
 · omega
 · exact KMZ_Growth.append_after_growth before garbage {source} {length} cap next {n} j live growth bound''')
emit('LPe_K017',['KNA_Frame'],'''theorem result (roots : Nat → Nat → Nat) (query before : Nat → Nat)
 (j : Nat) (bound : j<152) :
 2*32+22*4=152 ∧
 KMY_RootComposition.rootsQueries (fun b => roots (b/32) (b%32))
  (fun b => (query (b/4) / 2^(8*(b%4))) % 256) before j =
 if j<64 then roots (j/32) (j%32)
 else (query ((j-64)/4) / 2^(8*((j-64)%4))) % 256 := by
 constructor
 · exact KMY_RootComposition.roots_queries_length
 · exact KMY_RootComposition.roots_queries_bytes roots
     (fun i b => (query i / 2^(8*b)) % 256) before j bound''')
emit('LPf_K027',['KNA_Frame','KMZ_LPf_K027'],'''theorem result (initial garbage answer : Nat → Nat) (j : Nat) (bound : j<1768) :
 2+1=3 ∧ 1736+32=1768 ∧
 window answer (loop initial garbage 0 (min 1736 3472)) 1736 32 j =
 if j<1736 then initial j else answer (j-1736) := by
 refine ⟨by omega,by omega,?_⟩
 exact KMZ_LPf_K027.result initial garbage answer j bound''')
for row in ['LPi_K017','LPi_K018']:
 emit(row,['KNA_Frame','KMZ_'+row],f'''theorem result (body garbage hp hu answer : Nat → Nat) (j : Nat) (bound : j<1768) :
 0+3=3 ∧ 1736+32=1768 ∧
 window answer (loop (KMZ_{row}.joinedPrefix body hp hu) garbage 0 (min 1736 3472)) 1736 32 j =
 if 16≤j ∧ j<48 then hp (j-16) else if 48≤j ∧ j<80 then hu (j-48)
 else if j<1736 then body j else if j<1768 then answer (j-1736) else body j := by
 refine ⟨by omega,by omega,?_⟩
 exact KMZ_{row}.result body garbage hp hu answer j bound''')
emit('QuerySchedule',['KNA_Query128','KNA_Query256'],'''theorem result (i : Nat) (h : i<22) :
 i=0 ∨ (1≤i ∧ i<16) ∨ i=16 ∨ (17≤i ∧ i<22) := by omega''')
emit('FrameUnion',['KNA_Partition'],'''theorem result (actual expected : Nat → Nat)
 (prefixWindows : ∀ w, w<11 → ∀ j, 160*w≤j → j<min 1736 (160*(w+1)) → actual j=expected j)
 (appended : ∀ j, 1736≤j → j<1768 → actual j=expected j) :
 ∀ j, j<1768 → actual j=expected j := by
 intro j bound
 rcases KNA_Partition.result j bound with ⟨_,w,hw,lo,hi⟩ | ⟨lo,hi⟩
 · exact prefixWindows w hw j lo hi
 · exact appended j lo hi''')
emit('Capacity',['KNA_Frame'],'''theorem result (len size : Nat) :
 len≤max 8 (max (2*len) (len+size)) ∧
 len+size≤max 8 (max (2*len) (len+size)) := by omega''')
assert len(expected)==39,len(expected)
final='\n'.join('import '+m for m in expected)+'\n'+'\n'.join('#print axioms '+m+'.result' for m in expected)+'\n'
expected['KNA_Final']=final
for m,s in expected.items():
 assert not re.search(r'\b(sorry|admit|norm_num|decide|native_decide)\b',s),m
 p=E/(m+'.lean')
 if check:assert p.read_text()==s,m
 else:p.write_text(s)
records=[dict(module=m,sha256=hashlib.sha256(s.encode()).hexdigest()) for m,s in expected.items()]
(E/'KNA_LEAN_PREFLIGHT.json').write_text(json.dumps(dict(modules=records,next_consumer='KNA_Final',validation='Named symbolic applications only; 39 focused targets and one final replay; heap premises remain separately required'),indent=2)+'\n')
(E/'KNA_LEAN_MANIFEST.json').write_text(json.dumps(list(expected),indent=2)+'\n')
print('PASS 39 focused modules and one final manifest')
