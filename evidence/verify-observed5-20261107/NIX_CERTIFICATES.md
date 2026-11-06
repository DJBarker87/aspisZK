# Native-to-cut certificate register

Each association is reviewed transcription, reclassified under the owner-approved P6/D188 option A; never removal of tool trust. All sources are scratch-only and NIX_HARNESSES.patch reproduces the final source. The exact KMX patch is retained unchanged.

## AspisR1.NIX_Cuts.samplerCut

Source: NIX_sampler.rs.txt; SHA256 `bf3862dcb456c8c0713a2635761194ff9cbc0448d24afdc14bae995bb3a47dbb`; receipts NIX_K053, NIX_K048.

Exact assertion lines:

```rust
  {assert_eq!(log.block,block.as_ptr());assert!(same(log.parameter,q));if tag!=0 {assert_eq!(log.index,match row{CircleRow::First=>0,CircleRow::Second=>1});}else{assert_eq!(log.index,old_index);}}
  {assert_eq!(log.at[0],count);assert_eq!(log.at[1],count+1);if tag!=0{assert_eq!(log.at[2],count+2);assert_eq!(log.count,count+3);}else{assert_eq!(log.at[2],at[2]);assert_eq!(log.count,count+2);}}
  {assert_eq!(log.frame,frame);}
  {let expected=if tag==0{p}else{fb};assert!(same(result.x,expected.x)&&same(result.y,expected.y));}
```

## AspisR1.NIX_DispatchCut.cut

Source: NIX_validated.rs.txt; SHA256 `f38a0198f0689a7e860f956df4067a135bfad96ff82ee716b1c47fbd79613d1f`; receipts NIX_K049, NIX_K050.

Exact assertion lines:

```rust
  {if row==25||row==26{assert_eq!(log.row,row);assert_eq!(log.ptr,framed.as_ptr());assert_eq!(log.len,len);assert_eq!(log.next,before_next);assert_eq!(log.state[j],before_state[j]);assert_eq!(log.at,calls);if success{assert_eq!(log.sample_block[j],sampled[j]);match (row,log.sample_row){(25,CircleRow::First)|(26,CircleRow::Second)=>{},_=>assert!(false)}}}}
  {assert_eq!(log.frame,frame);if row==25||row==26{assert_eq!(transcript.state[j],new_state[j]);assert_eq!(transcript.next_row,new_next);if !success{assert_eq!(log.sample_block[j],old_sample[j]);assert!(matches!(log.sample_row,CircleRow::First));}assert_eq!(log.calls,calls+if success{2}else{1});}else{assert_eq!(transcript.state[j],before_state[j]);assert_eq!(transcript.next_row,before_next);assert_eq!(log.calls,calls);assert_eq!(log.sample_block[j],old_sample[j]);assert!(matches!(log.sample_row,CircleRow::First));assert_eq!(log.row,0);assert!(log.ptr.is_null());assert_eq!(log.len,0);assert_eq!(log.state[j],old_state[j]);assert_eq!(log.next,0);assert_eq!(log.at,0);}}
  {if row==25||row==26{match (success,result){(true,Ok(p))=>assert!(same(p.x,point.x)&&same(p.y,point.y)),(false,Err(Error::RowOrder{expected:e,actual:a}))=>{assert_eq!(e,expected);assert_eq!(a,actual);},_=>assert!(false)}}else{assert!(matches!(result,Err(Error::InvalidRow)));}}
```

## AspisR1.NIX_ResidualCut.cut

Source: NIX_residual.rs.txt; SHA256 `1c678ac5885301b020ca62c86037621d9fc99c8667670bc68d7e0dbc2e4da0f2`; receipts NIX_K058, NIX_K059.

Exact assertion lines:

```rust
  let i:usize=kani::any();kani::assume(i<17);assert!(same(l.args[2*i],expected[i].0)&&same(l.args[2*i+1],expected[i].1));assert!(canonical(l.args[2*i])&&canonical(l.args[2*i+1]));let kinds=[0u8,0,0,0,1,1,1,1,2,1,1,2,1,2,1,1,0];assert_eq!(l.kind[i],kinds[i]);assert_eq!(l.at[i],count+i as u8);assert_eq!(l.count,count+17);assert_eq!(l.frame,frame);assert!(same(result,o[16]));
```

## AspisR1.NIX_CertificateFrames.roundArgs

Source: NIX_round_local.rs.txt; SHA256 `b2c5c97db2214e4791a25ce1ed831f79a04663db835ffa16c95b1994f39cbac5`; receipts NIX_K073, NIX_K074.

Exact assertion lines:

```rust
  assert_eq!(l.getter_prefix[0],prefix);assert_eq!(l.getter_row[0],row);assert_eq!(l.getter_count,if has_semantic{2}else{1});if has_semantic{assert_eq!(l.getter_prefix[1],prefix);assert_eq!(l.getter_row[1],row);}else{assert_eq!(l.getter_prefix[1],0);assert_eq!(l.getter_row[1],0);}
  assert_eq!(l.decode_row,row);assert_eq!(l.ptr,framed.as_ptr());assert_eq!(l.len,len);assert_eq!(l.offset,0);assert_eq!(l.times[0],count);assert_eq!(l.frame,frame);
  if decode_ok{assert!(same(l.bp,poly[k]));assert_eq!(l.times[1],count+1);}else{assert!(same(l.bp,seed));assert_eq!(l.times[1],times[1]);}
  if has_semantic{assert_eq!(l.semantic_row,row);assert_eq!(l.semantic_ptr,framed.as_ptr());assert_eq!(l.semantic_len,len);assert_eq!(l.state[z],state[z]);assert_eq!(l.next,next);assert_eq!(l.times[2],count+2);}else{assert_eq!(l.semantic_row,0);assert!(l.semantic_ptr.is_null());assert_eq!(l.semantic_len,0);assert_eq!(l.state[z],oldstate[z]);assert_eq!(l.next,0);assert_eq!(l.times[2],times[2]);}
  if has_value{assert!(same(l.vp,poly[k]));assert!(same(l.va,if j==round{challenge}else{alpha[j]}));assert_eq!(l.value_round,round);assert_eq!(l.times[3],count+3);}else{assert!(same(l.vp,seed)&&same(l.va,seed));assert_eq!(l.value_round,99);assert_eq!(l.times[3],times[3]);}
  assert_eq!(l.count,count+if !decode_ok{1}else if !boundary_ok{2}else if !semantic_ok{3}else{4});
  match out{Ok((r,al,t))=>{assert!(has_value);assert!(same(r,value));assert!(same(al[j],if j==round{challenge}else{alpha[j]}));assert_eq!(t.state()[z],newstate[z]);assert_eq!(t.next_row(),newnext);},Err(err)=>{if !decode_ok{if tag==0{assert!(matches!(err,Error::Length{row:r} if r==row));}else{assert!(matches!(err,Error::NonCanonical{row:r,value:v} if r==row&&v==bad_value));}}else if !boundary_ok{assert!(matches!(err,Error::Boundary{round:r} if r==round));}else{assert!(!semantic_ok);assert!(matches!(err,Error::RowOrder{expected:x,actual:y} if x==e&&y==a));}}}
```

## AspisR1.NIX_CertificateFrames.roundResult

Source: NIX_round_local.rs.txt; SHA256 `b2c5c97db2214e4791a25ce1ed831f79a04663db835ffa16c95b1994f39cbac5`; receipts NIX_K075, NIX_K076.

Exact assertion lines:

```rust
  assert_eq!(l.getter_prefix[0],prefix);assert_eq!(l.getter_row[0],row);assert_eq!(l.getter_count,if has_semantic{2}else{1});if has_semantic{assert_eq!(l.getter_prefix[1],prefix);assert_eq!(l.getter_row[1],row);}else{assert_eq!(l.getter_prefix[1],0);assert_eq!(l.getter_row[1],0);}
  assert_eq!(l.decode_row,row);assert_eq!(l.ptr,framed.as_ptr());assert_eq!(l.len,len);assert_eq!(l.offset,0);assert_eq!(l.times[0],count);assert_eq!(l.frame,frame);
  if decode_ok{assert!(same(l.bp,poly[k]));assert_eq!(l.times[1],count+1);}else{assert!(same(l.bp,seed));assert_eq!(l.times[1],times[1]);}
  if has_semantic{assert_eq!(l.semantic_row,row);assert_eq!(l.semantic_ptr,framed.as_ptr());assert_eq!(l.semantic_len,len);assert_eq!(l.state[z],state[z]);assert_eq!(l.next,next);assert_eq!(l.times[2],count+2);}else{assert_eq!(l.semantic_row,0);assert!(l.semantic_ptr.is_null());assert_eq!(l.semantic_len,0);assert_eq!(l.state[z],oldstate[z]);assert_eq!(l.next,0);assert_eq!(l.times[2],times[2]);}
  if has_value{assert!(same(l.vp,poly[k]));assert!(same(l.va,if j==round{challenge}else{alpha[j]}));assert_eq!(l.value_round,round);assert_eq!(l.times[3],count+3);}else{assert!(same(l.vp,seed)&&same(l.va,seed));assert_eq!(l.value_round,99);assert_eq!(l.times[3],times[3]);}
  assert_eq!(l.count,count+if !decode_ok{1}else if !boundary_ok{2}else if !semantic_ok{3}else{4});
  match out{Ok((r,al,t))=>{assert!(has_value);assert!(same(r,value));assert!(same(al[j],if j==round{challenge}else{alpha[j]}));assert_eq!(t.state()[z],newstate[z]);assert_eq!(t.next_row(),newnext);},Err(err)=>{if !decode_ok{if tag==0{assert!(matches!(err,Error::Length{row:r} if r==row));}else{assert!(matches!(err,Error::NonCanonical{row:r,value:v} if r==row&&v==bad_value));}}else if !boundary_ok{assert!(matches!(err,Error::Boundary{round:r} if r==round));}else{assert!(!semantic_ok);assert!(matches!(err,Error::RowOrder{expected:x,actual:y} if x==e&&y==a));}}}
```

## Additional native stages

NIX_PAIR_PLAN.json and each *_PAIR.json identify the independent cells/boundaries, with per-child exact command, exit, wall, peak RSS, swap, features, frozen graph and unchanged lock. These are not admitted parent bridges. No Kani proof_for_contract or stub_verified is used, so no uncalibrated function-contract interface shape is relied on. No Option<fn>-dependent native credit is used.

## Resource and artifact pins

Every scope is 6G high / 8G max / zero swap / 64 tasks; optimized Rust opt-level=3, jobs=1; Lean -M7000/-j1/async=false. Per-scope source revisions/hashes and Aeneas object fingerprints are in receipts; per-child native metrics are in the pair register. The source target is 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, frozen3, deployed private-leaf-salts/optimized-terminal/program-build and program pool-adapter as applicable; default features remain enabled. Core-only helper bodies have no feature-dependent source branch; all field callees are opaque and separately paired with coherent Lean laws. Final caller dispatch/round certificates instantiate the actual program SolanaDigest.

No shipped source changed. Default f8c0ec72…, devnet 63ad3e9c…, Pool 121f3e29… are retained release pins, not fresh SBF rebuild results. Wire: same frozen P1 semantic rows, 10 rounds, 3x29 claims, two circle rows. Headline AspisR1.RPx_Deployed.deployed; L154 remains a statement parameter; no work-normalized/grinding credit, privacy or two-transaction change.
