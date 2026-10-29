from pathlib import Path
D=Path(__file__).parent
plans=[]
def plan(name,imports,defs,ts):
 s=''.join('import '+i+'\n' for i in imports)+'set_option autoImplicit false\nnamespace PV_DIAG8\n'+defs+'\n'
 chunks=[]
 for name,t in ts:
  chunks.append(s+t+'\n#print axioms '+name+'\n');s=''
 (D/('PV_DIAG8_'+name.split('_')[0]+'.unused')).exists() if False else None
 return chunks

def emit(module,imports,defs,theorems):
 chunks=plan(module,imports,defs,theorems)
 (D/(module+'.lean')).write_text('-- NEXT\n'.join(chunks)+'end PV_DIAG8\n')
 plans.append(dict(module=module,chunks=len(chunks),theorems=[n for n,t in theorems]))
def T(n,s):return n,'theorem '+n+' '+s
emit('PV_DIAG8_Cursor',['Mathlib.Tactic'],'''/-! Source guards only: no panic payload is evaluated. The caller invariant
is proved inductively from new(word=8), not postulated for an entire client. -/
def slot (word : Nat) : Nat := if word = 8 then 0 else word
def nextCursor (word : Nat) : Nat := slot word + 1
def cursorRun : Nat → Nat
 | 0 => 8
 | n+1 => nextCursor (cursorRun n)
''',[
T('cursor_initial',': cursorRun 0 = 8 := rfl'),
T('cursor_slot_lt','(w : Nat) (h : w ≤ 8) : slot w < 8 := by unfold slot; split <;> omega'),
T('cursor_next_bound','(w : Nat) (h : w ≤ 8) : nextCursor w ≤ 8 := by have := cursor_slot_lt w h; unfold nextCursor; omega'),
T('cursor_invariant','(n : Nat) : cursorRun n ≤ 8 := by induction n with | zero => decide | succ n ih => exact cursor_next_bound _ ih'),
T('cursor_start','(w : Nat) (h : w ≤ 8) : 4 * slot w ≤ 28 := by have := cursor_slot_lt w h; omega'),
T('cursor_end','(w : Nat) (h : w ≤ 8) : 4 * slot w + 4 ≤ 32 := by have := cursor_start w h; omega'),
T('cursor_length','(w : Nat) : (4 * slot w + 4) - 4 * slot w = 4 := by omega'),
T('cursor_byte0','(w : Nat) (h : w ≤ 8) : 4 * slot w < 32 := by have := cursor_start w h; omega'),
T('cursor_byte1','(w : Nat) (h : w ≤ 8) : 4 * slot w + 1 < 32 := by have := cursor_start w h; omega'),
T('cursor_byte2','(w : Nat) (h : w ≤ 8) : 4 * slot w + 2 < 32 := by have := cursor_start w h; omega'),
T('cursor_byte3','(w : Nat) (h : w ≤ 8) : 4 * slot w + 3 < 32 := by have := cursor_start w h; omega'),
T('cursor_machine_safe','(w : Nat) (h : w ≤ 8) : 4 * slot w + 4 < 2^32 ∧ nextCursor w < 2^32 := by have := cursor_end w h; have := cursor_next_bound w h; constructor <;> omega'),
T('cursor_reachable_slice','(n : Nat) : 4 * slot (cursorRun n) + 4 ≤ 32 := cursor_end _ (cursor_invariant n)'),
T('cursor_panic_guard_false','(n : Nat) : ¬ (32 < 4 * slot (cursorRun n) + 4 ∨ (4 * slot (cursorRun n) + 4) - 4 * slot (cursorRun n) ≠ 4) := by have := cursor_reachable_slice n; have := cursor_length (cursorRun n); omega')])
emit('PV_DIAG8_Arrays',['R1Z.ProverCommitArrayIndex25','PV_DIAG8_Cursor'],'''open Aeneas Aeneas.Std
/-! Existing extracted array-index theorem, specialized to reached fixed sizes.
These are index laws, not a claim that every native caller supplies the bound. -/
''',[
T('array_no_bounds_failure','{α : Type} {n : Usize} (a : Aeneas.Std.Array α n) (i : Usize) (h : i.val < n.val) : Aeneas.Std.Array.index_usize a i ≠ .fail .arrayOutOfBounds := by rw [R1Z.ProverCommitArrayIndex25.array_index_usize_ok a i h]; intro bad; cases bad'),
*[T('array_'+str(n)+'_safe',f'{{α : Type}} (a : Aeneas.Std.Array α {n}#usize) (i : Usize) (h : i.val < {n}) : Aeneas.Std.Array.index_usize a i ≠ .fail .arrayOutOfBounds := array_no_bounds_failure a i (by simpa using h)') for n in [4,8,20,22,26,29,32,56,64,512,1024]],
T('array_cursor_read_safe','(a : Aeneas.Std.Array U8 32#usize) (i : Usize) (n : Nat) (hat : i.val = 4 * slot (cursorRun n)) : Aeneas.Std.Array.index_usize a i ≠ .fail .arrayOutOfBounds := array_32_safe a i (by rw [hat]; exact cursor_byte0 _ (cursor_invariant n))'),
T('array_all_cursor_bytes_safe','(a : Aeneas.Std.Array U8 32#usize) (i : Usize) (n j : Nat) (hj : j < 4) (hat : i.val = 4 * slot (cursorRun n) + j) : Aeneas.Std.Array.index_usize a i ≠ .fail .arrayOutOfBounds := array_32_safe a i (by rw [hat]; have := cursor_start _ (cursor_invariant n); omega)')])
emit('PV_DIAG8_Round',['PV_DIAG8_Cursor'],'''/-! Bounds for prover::round and fold. PERM=[0,3,2,1]; no field
normalization and no formatted assertion operand is evaluated. -/
def roundPerm (t : Nat) : Nat := if t = 0 then 0 else if t = 1 then 3 else if t = 2 then 2 else 1
def foldedLength (n : Nat) : Nat := n / 4
''',[
T('round_perm_bound','(t : Nat) : roundPerm t ≤ 3 := by unfold roundPerm; split <;> (try split) <;> (try split) <;> omega'),
T('round_coeff_bound','(s t : Nat) (hs : s < 4) : s + roundPerm t < 7 := by have := round_perm_bound t; omega'),
T('round_query_bound','(n d s : Nat) (hd : d < n / 4) (hs : s < 4) : 4*d+s < n := by omega'),
T('round_weight_bound','(n d t : Nat) (hd : d < n / 4) (ht : t < 4) : 4*d+t < n := round_query_bound n d t hd ht'),
T('round_equal_shape','(q w : Nat) (h : q = w) : ¬ q ≠ w := by omega'),
T('round_fold_equal','(q w : Nat) (h : q = w) : foldedLength q = foldedLength w := congrArg foldedLength h'),
T('round_fold_nonincrease','(n : Nat) : foldedLength n ≤ n := Nat.div_le_self _ _'),
T('round_fold_index0','(n i : Nat) (h : i < n/4) : 4*i < n := by omega'),
T('round_fold_index1','(n i : Nat) (h : i < n/4) : 4*i+1 < n := by omega'),
T('round_fold_index2','(n i : Nat) (h : i < n/4) : 4*i+2 < n := by omega'),
T('round_fold_index3','(n i : Nat) (h : i < n/4) : 4*i+3 < n := by omega'),
T('round_messages_lane','(l : Nat) (h : l < 26) : l < 29 := by omega'),
T('round_messages_aux',': 26 < 29 ∧ 27 < 29 ∧ 28 < 29 := by decide'),
T('round_row_increment','(r : Nat) (h : r < 1024) : r+1 ≤ 1024 ∧ r+1 < 2^32 := by omega')])
# Structural publication arithmetic: constants are checked against deployed source by bind.py.
emit('PV_DIAG8_Publication',['PV_DIAG8_Round'],'''def publishedIndex (attempts : Nat) : Nat := attempts - 1
/-! Only exact guard implications are claimed until native constructor,
query and publication invariants are associated on the honest family. -/
''',[
T('publication_selected_index','(a : Nat) (h : 1 ≤ a ∧ a ≤ 8) : publishedIndex a < 8 := by unfold publishedIndex; omega'),
T('publication_sub_no_underflow','(a : Nat) (h : 1 ≤ a) : a-1+1=a := by omega'),
T('publication_callback_bound','(k : Nat) (h : k < 8) : k+1 ≤ 8 := by omega'),
T('publication_callback_order','(entered k : Nat) (h : entered = k) : ¬ k ≠ entered := by omega'),
T('publication_query_index','(i : Nat) (h : i < 22) : i+1 ≤ 22 := by omega'),
T('publication_batch0',': 0 ≤ 10 ∧ 10 ≤ 22 := by decide'),
T('publication_batch1',': 10 ≤ 22 := by decide'),
T('publication_slot_index','(b t : Nat) (hb : b < 2) (ht : t < 3) : 3*b+t < 6 := by omega'),
T('publication_capacity_pad','(out nodes cap : Nat) (h : nodes ≤ cap) : out+nodes+cap-nodes = out+cap := by omega'),
T('publication_slot_no_underflow','(out nodes cap : Nat) (h : nodes ≤ cap) : nodes ≤ out+nodes+cap := by omega'),
T('publication_folded_start','(u : Nat) (h : u < 512) : 4*(u/4)+4 ≤ 512 := by omega'),
T('publication_folded_salt','(u : Nat) (h : u < 512) : u/4 < 128 := by omega'),
T('publication_opening_values_count',': 4*29*32=3712 := by decide'),
T('publication_nodes_guard','(nodes cap : Nat) (h : nodes ≤ cap) : ¬ cap < nodes := by omega')])
(D/'plans.json').write_text(__import__('json').dumps(plans,indent=2)+'\n')
emit('PV_DIAG8_Messages',['PV_DIAG8_Publication'],'''/-! Literal error-construction sites of the actual proof-account client.
Formatting OS replies and arbitrary Debug implementations remains separate. -/
inductive ClientGuard
 | legacy | listType | listCount | keyType | keyCanonical | duplicate
 | position | attempts | lane | checkpoint | anchor | settled | marker | unknown
 deriving DecidableEq
 def guardText : ClientGuard → String
 | .legacy => "legacy proof_account input is unsupported"
 | .listType => "proof_accounts must be eight public keys"
 | .listCount => "proof_accounts must contain eight public keys"
 | .keyType => "proof account must be a string"
 | .keyCanonical => "noncanonical/zero proof account"
 | .duplicate => "duplicate proof account"
 | .position => "unexpected settlement proof-account position"
 | .attempts => "invalid successful attempt count"
 | .lane => "wrong live output lane"
 | .checkpoint => "checkpoint master mismatch"
 | .anchor => "deposits do not reconstruct finalized anchor"
 | .settled => "settled lane differs from proved afterstate"
 | .marker => "consumed marker identity differs"
 | .unknown => "unknown action"
''',[
T('message_fixed_at_site','{W : Type} (site : ClientGuard) (w w\' : W) : (fun _ : W => guardText site) w = (fun _ : W => guardText site) w\' := rfl'),
T('message_site_law','(a b : ClientGuard) (h : a=b) : guardText a = guardText b := congrArg guardText h'),
T('message_no_dynamic_operands','(g : ClientGuard) : ∃ text : String, guardText g = text := ⟨guardText g,rfl⟩'),
T('message_length_law','(a b : ClientGuard) (h : a=b) : (guardText a).utf8ByteSize=(guardText b).utf8ByteSize := congrArg String.utf8ByteSize (message_site_law a b h)'),
T('message_public_history','{P W : Type} (sites : P → List ClientGuard) (p : P) (w w\' : W) : (fun _ : W => (sites p).map guardText) w = (fun _ : W => (sites p).map guardText) w\' := rfl'),
T('message_error_prefix','(sites : List ClientGuard) (n : Nat) : (sites.take n).map guardText = (sites.map guardText).take n := by simp only [List.map_take]'),
T('message_prefix_count','(sites : List ClientGuard) : (sites.map guardText).length=sites.length := by simp'),
T('message_capture_site_separate','(a b : ClientGuard) (h : a=b) : (a,guardText a)=(b,guardText b) := by cases h; rfl')])
emit('PV_DIAG8_World',['PV_DIAG8_Messages'],'''/-! Sufficient request-discipline criterion for V400, not an instance of it.
Requests retain operation, route/name, offset and size. Payload is separate:
byte blindness must be proved for the deployed filesystem/allocator world. -/
structure Request where
 op : Nat
 route : List Nat
 offset : Nat
 size : Nat
 deriving DecidableEq
structure Reply where
 failed : Bool
 code : Nat
 count : Nat
 deriving DecidableEq
abbrev History := List (Request × Reply)
def replay (world : History → Request → Reply) : History → List Request → History
 | h, [] => h
 | h, q::qs => replay world (h ++ [(q,world h q)]) qs
def failures (h : History) : List Bool := h.map (fun x => x.2.failed)
def appendReq (h : History) (q : Request) (r : Reply) : History := h ++ [(q,r)]
''',[
T('world_empty','(world : History → Request → Reply) (h : History) : replay world h [] = h := rfl'),
T('world_cons','(world : History → Request → Reply) (h : History) (q : Request) (qs : List Request) : replay world h (q::qs) = replay world (appendReq h q (world h q)) qs := rfl'),
T('world_history_length','(world : History → Request → Reply) (qs : List Request) (h : History) : (replay world h qs).length=h.length+qs.length := by induction qs generalizing h with | nil => simp [replay] | cons q qs ih => rw [replay,ih]; simp; omega'),
T('world_failure_length','(h : History) : (failures h).length=h.length := by simp [failures]'),
T('world_same_history','(world : History → Request → Reply) (h h\' : History) (eqh : h=h\') (q q\' : Request) (eqq : q=q\') : world h q=world h\' q\' := by cases eqh; cases eqq; rfl'),
T('world_same_requests','(world : History → Request → Reply) (h : History) (a b : List Request) (he : a=b) : replay world h a=replay world h b := congrArg (replay world h) he'),
T('world_failure_event_public','{P W : Type} (world : History → Request → Reply) (requests : P → List Request) (initial : P → History) (p : P) (w w\' : W) : (fun _ : W => failures (replay world (initial p) (requests p))) w = (fun _ : W => failures (replay world (initial p) (requests p))) w\' := rfl'),
T('world_reached_failure_public','{P W : Type} (world : History → Request → Reply) (requests : P → List Request) (p : P) (w w\' : W) : (fun _ : W => true ∈ failures (replay world [] (requests p))) w ↔ (fun _ : W => true ∈ failures (replay world [] (requests p))) w\' := Iff.rfl'),
T('world_prefix_requests','(world : History → Request → Reply) (a b : List Request) (h : History) : replay world h (a++b)=replay world (replay world h a) b := by induction a generalizing h with | nil => rfl | cons q a ih => simpa only [List.cons_append,replay] using ih (h++[(q,world h q)])'),
T('world_error_not_success_erasure','(h : History) (q : Request) (r : Reply) : failures (appendReq h q r)=failures h ++ [r.failed] := by simp [failures,appendReq]'),
T('world_request_size_retained','(h : History) (q : Request) (r : Reply) : (appendReq h q r).getLast?=some (q,r) := by simp [appendReq]'),
T('world_64_byte_draw','(op : Nat) (route : List Nat) (offset : Nat) : (Request.mk op route offset 64).size = 64 := rfl'),
T('world_nonce_file_fields',': 16+32+32 = 80 := by decide'),
T('world_byte_blind_transport','''{A : Type} (world : History → Request → Reply) (native : A → History → Request → Reply) (blind : ∀ a h q, native a h q=world h q) (a : A) (qs : List Request) (h : History) : replay (native a) h qs = replay world h qs := by
  have he : native a = world := by
    funext h q
    exact blind a h q
  rw [he]''')])
emit('PV_DIAG8_Frames',['PV_DIAG8_World'],'''/-! Error-path capture requires the live stack at the capture point, not only
public formatted text or public backtrace configuration. No PCs are put into
option B's environment-failure input by this model. -/
inductive PathStep
 | enter (frame : Nat)
 | leave
 | capture (enabled : Bool)
 deriving DecidableEq
def stackStep (stack : List Nat) : PathStep → List Nat
 | .enter f => f::stack
 | .leave => stack.tail
 | .capture _ => stack
def captures (stack : List Nat) : List PathStep → List (List Nat)
 | [] => []
 | s::rest => (match s with | .capture true => [stack] | _ => []) ++ captures (stackStep stack s) rest
''',[
T('frames_no_capture_empty','(s : List Nat) : captures s []=[] := rfl'),
T('frames_capture_here','(s : List Nat) (rest : List PathStep) : captures s (.capture true::rest) = s::captures s rest := rfl'),
T('frames_disabled_here','(s : List Nat) (rest : List PathStep) : captures s (.capture false::rest)=captures s rest := rfl'),
T('frames_enter','(s : List Nat) (f : Nat) (rest : List PathStep) : captures s (.enter f::rest)=captures (f::s) rest := rfl'),
T('frames_leave','(s : List Nat) (rest : List PathStep) : captures s (.leave::rest)=captures s.tail rest := rfl'),
T('frames_public_path','{P W : Type} (path : P → List PathStep) (stack : P → List Nat) (p : P) (w w\' : W) : (fun _ : W => captures (stack p) (path p)) w = (fun _ : W => captures (stack p) (path p)) w\' := rfl'),
T('frames_path_transport','(s : List Nat) (a b : List PathStep) (h : a=b) : captures s a=captures s b := congrArg (captures s) h'),
T('frames_same_message_insufficient',': captures [0] [.capture true] ≠ captures [1] [.capture true] := by decide'),
T('frames_same_config_insufficient',': captures [] [.enter 0,.capture true] ≠ captures [] [.enter 1,.capture true] := by decide'),
T('frames_decoder_transport','{O : Type} (decode : List (List Nat) → O) (s : List Nat) (a b : List PathStep) (h : a=b) : decode (captures s a)=decode (captures s b) := congrArg decode (frames_path_transport s a b h)')])
(D/'plans.json').write_text(__import__('json').dumps(plans,indent=2)+'\n')
