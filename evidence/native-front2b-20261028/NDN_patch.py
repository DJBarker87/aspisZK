from pathlib import Path
import difflib,subprocess
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def files():
 n='crates/aspis-statement/src/state_only_poseidon.rs'
 s=(E/'NDN_seed'/n).read_text()
 old='{unsafe{NDE_native::NDE_MATRIX_REPLY=local[NDE_native::NDE_PACKED_ROW][NDE_native::NDE_PACKED_LIMB];}return [0;4];'
 assert old in s
 s=s.replace(old,old+'}',1)
 a=s.index('fn interpolate_three_constant_limb(');b=s.index('\n#[inline(always)]',a)
 original=s[a:b];alternate=original
 for i in range(3):
  old='u64::from(weight'+str(i)+') * u64::from(constant'+str(i)+')'
  assert old in alternate
  alternate=alternate.replace(old,'NDN_native::product('+str(i)+',u64::from(weight'+str(i)+'),u64::from(constant'+str(i)+'))')
 gate='all(kani,any(NDN_interpolation_factors,NDN_interpolation_sum))'
 s=s[:a]+'#[cfg(not('+gate+'))]\n'+original+'\n#[cfg('+gate+')]\n'+alternate+s[b:]
 s+='\n#[cfg(kani)]\n#[path="NDN_state_native.rs"] mod NDN_native;\n'
 out={n:s}
 out['crates/aspis-statement/src/NDN_state_native.rs']=(E/'NDN_state_native.rs').read_text()
 n='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
 s=subprocess.check_output(['git','show',REV+':'+n],text=True)
 a=s.index('    fn active_mask_basis(');b=s.index('    fn active(&self)',a)
 body=s[a:b]
 point='        let mut block = 0usize;'
 body=body.replace(point,point+'\n        #[cfg(all(kani,any(NDN_active_high,NDN_active_route,NDN_active_sparse,NDN_active_sparse2)))] {high_sums=unsafe{NDN_native::PRE};block=unsafe{NDN_native::BLOCK};}',1)
 point='            high_sums[coordinate] = high_sums[coordinate].add(self.high[block]);'
 body=body.replace(point,'            #[cfg(all(kani,NDN_active_route))] {unsafe{NDN_native::COORD=coordinate;NDN_native::LEFT=high_sums[coordinate];NDN_native::RIGHT=self.high[block];}return QM31::ZERO;}\n'+point,1)
 point='            block += 1;'
 body=body.replace(point,point+'\n            #[cfg(all(kani,any(NDN_active_high,NDN_active_route,NDN_active_sparse,NDN_active_sparse2)))] {unsafe{NDN_native::AFTER=high_sums;NDN_native::NEXT=block;}return QM31::ZERO;}',1)
 body=body.replace('        let mut block = 0usize;','        let mut block = 0usize;\n        #[cfg(all(kani,NDN_active_low))] {block=64;}',1)
 body=body.replace('        let mut block = 0usize;','        let mut block = 0usize;\n        #[cfg(all(kani,NDN_active_outer))] {block=64;high_sums=unsafe{NDN_native::PRE};}',1)
 body=body.replace('        let mut sum = QM31::ZERO;','        let mut sum = QM31::ZERO;\n        #[cfg(all(kani,NDN_active_outer))] {sum=unsafe{NDN_native::OUTER_SUM};}',1)
 body=body.replace('        let mut coordinate = 0usize;','        let mut coordinate = 0usize;\n        #[cfg(all(kani,NDN_active_low))] {coordinate=unsafe{NDN_native::COORD};}',1)
 point='            sum = sum.add(high_sums[coordinate].mul(low_sum));'
 body=body.replace(point,'            #[cfg(all(kani,NDN_active_low))] {unsafe{NDN_native::LOW_REPLY=low_sum;}return QM31::ZERO;}\n'+point,1)
 body=body.replace(point,point+'\n            #[cfg(all(kani,NDN_active_outer))] {unsafe{NDN_native::OUTER_REPLY=sum;}return sum;}',1)
 s=s[:a]+body+s[b:]
 a=s.index('fn finish_pattern_basis_values(');b=s.index('\n#[cfg',a)
 body=s[a:b]
 body=body.replace('    let mut group = 0usize;','    let mut group = 0usize;\n    #[cfg(all(kani,any(NDN_pattern_step,NDN_pattern_route,NDN_pattern_write)))] {group=unsafe{NDN_native::PATTERN_GROUP};}',1)
 body=body.replace('        let mut coordinate = COPY_PATTERN_GROUP_OFFSETS[group];','        let mut coordinate = COPY_PATTERN_GROUP_OFFSETS[group];\n        #[cfg(all(kani,any(NDN_pattern_step,NDN_pattern_route,NDN_pattern_write)))] {coordinate=unsafe{NDN_native::PATTERN_COORD};}',1)
 point='            values[group] = values[group].add(patterns[pattern].mul(pattern_selectors[coordinate]));'
 body=body.replace(point,'            #[cfg(all(kani,NDN_pattern_route))] {unsafe{NDN_native::PATTERN_LEFT=patterns[pattern];NDN_native::PATTERN_RIGHT=pattern_selectors[coordinate];NDN_native::PATTERN_BASE=values[group];}return values;}\n            #[cfg(not(all(kani,NDN_pattern_write)))] {\n'+point+'\n            }\n            #[cfg(all(kani,NDN_pattern_write))] {values[group]=values[group].add(unsafe{NDN_native::PATTERN_PRODUCT});}',1)
 body=body.replace('            coordinate += 1;','            coordinate += 1;\n            #[cfg(all(kani,any(NDN_pattern_step,NDN_pattern_route,NDN_pattern_write)))] {unsafe{NDN_native::PATTERN_AFTER=values;NDN_native::PATTERN_NEXT=coordinate;}return values;}',1)
 s=s[:a]+body+s[b:]
 a=s.index('fn copy_tag_coordinate_dot(');b=s.index('\n#[cfg',a)
 original=s[a:b];body=original
 gate='all(kani,any(NDN_tag_geometry,NDN_tag_factors,NDN_tag_accumulate,NDN_tag_reduce))'
 point='    let end = usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate + 1]);'
 body=body.replace(point,point+'\n    index=unsafe{NDN_native::TAG_INDEX};',1)
 point='        let chunk_end = core::cmp::min(index + 4, end);'
 body=body.replace(point,point+'\n        #[cfg(NDN_tag_geometry)] {unsafe{NDN_native::TAG_END=end;NDN_native::TAG_CHUNK_END=chunk_end;}return QM31::ZERO;}',1)
 body=body.replace('        let mut raw = [0u64; 4];','        let mut raw=unsafe{NDN_native::TAG_RAW};\n        #[cfg(NDN_tag_reduce)] {index=chunk_end;}',1)
 point='            let tag = u64::from(COPY_TAG_TERMS.1[index]);'
 body=body.replace(point,point+'\n            #[cfg(NDN_tag_factors)] {unsafe{NDN_native::TAG_WORDS=[value.c0.a.0,value.c0.b.0,value.c1.a.0,value.c1.b.0];NDN_native::TAG_TAG=tag;NDN_native::TAG_BLOCK=usize::from(COPY_TAG_TERMS.0[index]);}return QM31::ZERO;}',1)
 for i,limb in enumerate(['c0.a','c0.b','c1.a','c1.b']):
  point='raw['+str(i)+'] += u64::from(value.'+limb+'.0) * tag;'
  assert point in body
  body=body.replace(point,'raw['+str(i)+'] += unsafe{NDN_native::TAG_PRODUCTS['+str(i)+']};',1)
 body=body.replace('            index += 1;','            index += 1;\n            #[cfg(NDN_tag_accumulate)] {unsafe{NDN_native::TAG_AFTER=raw;NDN_native::TAG_NEXT=index;}return QM31::ZERO;}',1)
 body=body.replace('        let mut limb = 0usize;','        let mut limb=unsafe{NDN_native::TAG_LIMB};\n        output=unsafe{NDN_native::TAG_OUTPUT};',1)
 body=body.replace('            limb += 1;','            limb += 1;\n            #[cfg(NDN_tag_reduce)] {unsafe{NDN_native::TAG_REDUCED=output;}return QM31::ZERO;}',1)
 s=s[:a]+'#[cfg(not('+gate+'))]\n'+original+'\n#[cfg('+gate+')]\n'+body+s[b:]
 # Source-window instrumentation: each product receives the arbitrary prior-cut
 # result except the selected multiplication; erasing cfg blocks restores frozen body.
 a=s.index('fn copy_residual(');b=s.index('\n#[inline(always)]',a)
 body=s[a:b]
 # A local trait makes the alternate call spelling explicit, without modifying
 # the frozen core field implementation or creating a Kani method stub.
 body=body.replace('    let denominators = [','    #[cfg(all(kani,NDN_residual_cut))] use NDN_native::CutMul;\n    let denominators = [',1)
 body=body.replace('.mul(','.NDN_mul(')
 # Entire alternate body is cfg-only; real frozen body remains selected otherwise.
 original=s[a:b]
 alternate=body.replace('fn copy_residual(', 'fn copy_residual(',1)
 s=s[:a]+'#[cfg(not(all(kani,NDN_residual_cut)))]\n'+original+'\n#[cfg(all(kani,NDN_residual_cut))]\n'+alternate+s[b:]
 s+='\n#[cfg(kani)]\n#[path="NDN_copy_native.rs"] mod NDN_native;\n'
 out[n]=s
 out['crates/aspis-statement/src/pool_v1/NDN_copy_native.rs']=(E/'NDN_copy_native.rs').read_text()
 out['crates/aspis-statement/src/pool_v1/NDN_reference.rs']=(E/'NDN_reference.rs').read_text()
 n='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
 s=subprocess.check_output(['git','show',REV+':'+n],text=True)
 a=s.index('fn equality_value(');b=s.index('\n#[allow',a)
 body=s[a:b]
 body=body.replace('    let mut product = factor(left[0], right[0]);','    #[cfg(not(all(kani,NDN_eq_outer)))]\n    let mut product = factor(left[0], right[0]);\n    #[cfg(all(kani,NDN_eq_outer))]\n    let mut product=unsafe{NDN_native::EQ_PRE};\n    #[cfg(all(kani,NDN_eq_factor))] {return product;}')
 body=body.replace('    let mut index = 1usize;','    let mut index = 1usize;\n    #[cfg(all(kani,NDN_eq_outer))]\n    let mut index=unsafe{NDN_native::EQ_INDEX};\n    #[cfg(all(kani,NDN_eq_outer))]\n    let factor=|a,b|{unsafe{NDN_native::EQ_ARGS=(a,b);NDN_native::EQ_FACTOR}};')
 body=body.replace('        index += 1;','        index += 1;\n        #[cfg(all(kani,NDN_eq_outer))] {return product;}',1)
 s=s[:a]+body+s[b:]
 a=s.index('        pub fn public_bytes(self)');b=s.index('        /// Fast K path',a)
 body=s[a:b]
 point='                    out.extend_from_slice(&value.0.to_le_bytes());'
 assert point in body
 body=body.replace(point,'                    #[cfg(all(kani,NDN_fields_window))] {unsafe{super::NDN_native::FIELD_BYTES=value.0.to_le_bytes();super::NDN_native::FIELD_REACHED=true;}return Ok(());}\n'+point,1)
 point='            let p = self.semantic();'
 assert point in body
 body=body.replace(point,'            #[cfg(all(kani,NDN_fields_window))] {let mut out=Vec::new();let r=fields(&mut out,&[M31(unsafe{super::NDN_native::FIELD_WORD})]);unsafe{super::NDN_native::FIELD_ERROR=matches!(r,Err(Error::Public));}return Ok(out); }\n'+point,1)
 s=s[:a]+body+s[b:]
 s+='\n#[cfg(kani)]\n#[path="NDN_semantic_native.rs"] mod NDN_native;\n'
 out[n]=s
 out['crates/aspis-statement/src/pool_v1/NDN_semantic_native.rs']=(E/'NDN_semantic_native.rs').read_text()
 n='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
 s=subprocess.check_output(['git','show',REV+':'+n],text=True)
 a=s.index('pub fn decode_pool_v1_pair_forest_terminal_request_v1(');b=s.index('\n///',a)
 body=s[a:b]
 point='    let public = match kind {'
 body=body.replace(point,'    #[cfg(all(kani,NDN_request_cut))] {unsafe{NDN_native::REQ_REACHED=true;NDN_native::REQ_LENGTH=bytes[REQUEST_PAYMENT_OFFSET..].len();NDN_native::REQ_VALUE=bytes[REQUEST_PAYMENT_OFFSET+NDN_native::REQ_INDEX];NDN_native::REQ_KIND=kind as u8;}return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength); }\n'+point,1)
 s=s[:a]+body+s[b:]
 a=s.index('pub fn validate_pool_v1_pair_forest_terminal_result_against_statement_v1(');b=s.index('\npub fn encode_pool',a)
 body=s[a:b]
 gate='all(kani,any(NDN_result_compare,NDN_result_field))'
 body=body.replace('    validate_pool_v1_pair_forest_terminal_statement_v1(statement)?;','    #[cfg(not('+gate+'))] {validate_pool_v1_pair_forest_terminal_statement_v1(statement)?;}',1)
 body=body.replace('    validate_result(result)?;','    #[cfg(not('+gate+'))] {validate_result(result)?;}',1)
 point='    let common = statement.common();'
 body=body.replace(point,point+'\n    #[cfg(all(kani,NDN_result_field))] {unsafe{let j=NDN_native::COMPARE_J;NDN_native::COMPARE_MASTER=(result.master_account[j],common.master_account[j]);NDN_native::COMPARE_LANE=(result.selected_lane_account[j],common.selected_lane_account[j]);}return Err(PoolV1PairForestTerminalFormatErrorV1::ResultBindingMismatch);}',1)
 s=s[:a]+body+s[b:]
 a=s.index('pub fn encode_pool_v1_pair_forest_terminal_result_v1(');b=s.index('\npub fn decode_pool',a)
 body=s[a:b]
 body=body.replace('    validate_result(result)?;','    #[cfg(not(all(kani,NDN_result_header)))] {validate_result(result)?;}',1)
 point='    output[7] = result.output_lane;'
 body=body.replace(point,point+'\n    #[cfg(all(kani,NDN_result_header))] {unsafe{NDN_native::RESULT_HEADER=output[..8].try_into().unwrap();}return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength);}',1)
 s=s[:a]+body+s[b:]
 s+='\n#[cfg(kani)]\n#[path="NDN_terminal_native.rs"] mod NDN_native;\n'
 out[n]=s
 out['crates/aspis-statement/src/pool_v1/NDN_terminal_native.rs']=(E/'NDN_terminal_native.rs').read_text()
 patch=''
 for n,s in out.items():
  r=subprocess.run(['git','show',REV+':'+n],capture_output=True,text=True);prior=r.stdout
  patch+=''.join(difflib.unified_diff(prior.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n,n=0))
 (E/'NDN_harness.patch').write_text(patch)
 return out
