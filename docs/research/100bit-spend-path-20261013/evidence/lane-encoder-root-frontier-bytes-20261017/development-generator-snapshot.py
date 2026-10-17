from pathlib import Path
import sys
idx=int(sys.argv[1]); start=128+32*idx; end=start+32
src=Path('/tmp/LaneEncoderActualRootBytesV1.lean').read_text()
head=src[:src.index('theorem successful_tail_preserves_root_bytes')]
lines=[head.rstrip(),f'''theorem successful_tail_preserves_frontier_{idx}_bytes (lane : PoolV1PairForestLaneStateV1) (out : Array U8 768#usize)
    (hok : encode_lane_bytes_tail_v1 lane = .ok out) :
    ∃ row : Array M31 8#usize, ∃ bytes : Array U8 32#usize,
      Array.index_usize lane.tree.frontier {idx}#usize = .ok row ∧
      encode_digest_canonical row = .ok bytes ∧
      ∀ k : Nat, k < 32 → out.val[{start} + k]? = bytes.val[k]? := by''',
'''  have h := hok
  unfold encode_lane_bytes_tail_v1 at h''']
init=src[src.index('  rcases bind_ok_inv h with'):src.index('    have hbaseExists :')]
lines.extend(init.rstrip().splitlines())
lines.append('    let base0 : Array U8 768#usize := rootBack rootCopied')
prev=32
for i in range(20):
    first=prev+1; a=128+32*i; b=a+32
    base = 'base0' if i == 0 else f'base_{i}'
    lines += [f'    rcases bind_ok_inv hrest{prev} with ⟨pair_{i}, hindex_{i}, hrest{first}⟩',
      f'    rcases pair_{i} with ⟨target_{i}, back_{i}⟩',
      f'    rcases bind_ok_inv hrest{first} with ⟨frontier_{i}, hread_{i}, hrest{first+1}⟩',
      f'    rcases bind_ok_inv hrest{first+1} with ⟨digest_{i}, hencode_{i}, hrest{first+2}⟩',
      f'    rcases bind_ok_inv hrest{first+2} with ⟨slice_{i}, hlift_{i}, hrest{first+3}⟩',
      f'    rcases bind_ok_inv hrest{first+3} with ⟨copied_{i}, hcopy_{i}, hrest{first+4}⟩',
      f'    have hsource_{i} : slice_{i} = Array.to_slice digest_{i} := by',
      f'      simpa [lift] using hlift_{i}.symm',f'    rw [hsource_{i}] at hcopy_{i}']
    lines.append(f'    let base_{i+1} : Array U8 768#usize := back_{i} copied_{i}')
    if i==idx or i>idx:
      lines += [f'    have hindexNorm{i} : core.array.Array.index_mut',
       f'        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) {base}',
       f'        {{ start := {a}#usize, «end» := {b}#usize }} = .ok (target_{i}, back_{i}) := by',
       f'      simpa [{base}] using hindex_{i}',
       f'    have hstart_{i} : ({a}#usize : Usize) ≤ {b}#usize := by decide',
       f'    have hend_{i} : ({b}#usize : Usize) ≤ 768#usize := by decide',
       f'    have hlen_{i} : slice_{i}.length = {b} - {a} := by',
       f'      rw [hsource_{i}]',f'      simp [Array.to_slice, Slice.length]']
    if i==idx:
      lines += [f'    have hbackExact_{i} : (back_{i} copied_{i}).val = {base}.val.setSlice! {a} digest_{i}.val := by',
       f'      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact',
       f'        {base} digest_{i} target_{i} copied_{i} back_{i}',
       f'        {{ start := {a}#usize, «end» := {b}#usize }} hstart_{i} hend_{i}',
       f'        (by simpa [Array.to_slice, Slice.length] using hlen_{i}) hindexNorm{i} hcopy_{i}',
       f'    have hslot_{i} : ∀ k : Nat, k < 32 → (back_{i} copied_{i}).val[{a} + k]? = digest_{i}.val[k]? := by',
       f'      intro k hk',f'      rw [hbackExact_{i}]',f'      rw [List.setSlice!_getElem?_middle]',
       f'      · simp only [Nat.add_sub_cancel_left]',f'      · constructor',f'        · omega',f'        constructor',
       f'        · simpa [Nat.add_sub_cancel_left] using hk',f'        · have hb : {a} + k < 768 := by omega',f'          simpa using hb']
    if i>idx:
      lines += [f'    have hstartNat_{i} : ({a}#usize).val = {a} := by decide',
       f'    have hframeAll_{i} : ∀ q : Nat, q < {a} → (back_{i} copied_{i}).val[q]? = {base}.val[q]? := by',
       f'      intro q hq',
       f'      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice',
       f'        base_{i} (Array.to_slice digest_{i}) target_{i} copied_{i} back_{i}',
       f'        {{ start := {a}#usize, «end» := {b}#usize }} hstart_{i} hend_{i}',
       f'        (by simpa [Array.to_slice, Slice.length] using hlen_{i}) hindexNorm{i} hcopy_{i}',
       f'        q (by change q < ({a}#usize).val; rw [hstartNat_{i}]; exact hq)']
    prev=first+4
lines += ['    have hfinal : base_20 = out := by','      exact Result.ok.inj hrest132',
 f'    refine ⟨frontier_{idx}, digest_{idx}, hread_{idx}, hencode_{idx}, ?_⟩','    intro k hk','    calc',
 f'      out.val[{start} + k]? = base_20.val[{start} + k]? := by simpa [hfinal]']
for j in range(19,idx,-1):
    lines.append(f'      _ = base_{j}.val[{start} + k]? := hframeAll_{j} ({start} + k) (by omega)')
lines += [f'      _ = (back_{idx} copied_{idx}).val[{start} + k]? := by rfl',f'      _ = digest_{idx}.val[k]? := hslot_{idx} k hk','',f'#print axioms successful_tail_preserves_frontier_{idx}_bytes','end AspisR1PairForestLaneEncoderTailActualRootBlock','']
Path(f'/tmp/LaneEncoderFrontier{idx}Narrow.lean').write_text('\n'.join(lines))
