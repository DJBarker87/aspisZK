exec(open('evidence/pv-route2-20261027/more_candidates.py').read().split("p='crates/aspis-core/src/r0/encoder.rs'")[0])
p='crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs';s=Path(p).read_text();a=s.index('    for link in links {',s.index('fn endpoint_counts'));b=s.index('    Ok((producers, consumers))',a);s=s[:a]+'''    let mut i=0usize;
    while i<links.len() {
        let link=links[i];
        let producer=usize::from(link.producer_row);
        if producer>=POOL_V1_PAIR_TRACE_ROWS || producers[producer]>=2 {return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity {row:producer as u16});}
        producers[producer]+=1;
        let consumer=usize::from(link.consumer_row);
        if consumer>=POOL_V1_PAIR_TRACE_ROWS || consumers[consumer]>=2 {return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity {row:consumer as u16});}
        consumers[consumer]+=1;
        i+=1;
    }
'''+s[b:];a=s.index('    let mut links = build_pool_v1_pair_copy_row_schedule_v1()?');b=s.index('    // The existing schedule',a);s=s[:a]+'''    let legacy=build_pool_v1_pair_copy_row_schedule_v1()?;
    let mut links=Vec::new();
    let mut i=0usize;
    while i<legacy.len() {
        let scheduled=legacy[i];
        if !matches!(scheduled.kind,PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent{..}|PoolV1PairCopyRowLinkKindV1::PrivatePathLeft{..}|PoolV1PairCopyRowLinkKindV1::PrivatePathRight{..}) {links.push(scheduled);}
        i+=1;
    }
'''+s[b:];s=s.replace('    for scheduled in &mut links {','    let mut i=0usize;\n    while i<links.len() {\n        let mut scheduled=links[i];',1);needle='    links.reserve(3 *';pos=s.index(needle);s=s[:pos].rstrip().removesuffix('}')+'        links[i]=scheduled;\n        i+=1;\n    }\n'+s[pos:]
a=s.index('    let mut rows = build_pool_v1_pair_forest_copy_row_schedule_v1()?');b=s.index('    rows.sort_unstable();',a);s=s[:a]+'''    let schedule=build_pool_v1_pair_forest_copy_row_schedule_v1()?;
    let mut rows=Vec::new();let mut i=0usize;
    while i<schedule.len() {rows.push(schedule[i].producer_row);rows.push(schedule[i].consumer_row);i+=1;}
'''+s[b:]
s=s.replace('    for row in pool_v1_pair_forest_copy_active_rows_v1()? {\n        masks[usize::from(row) >> 4] |= 1 << (usize::from(row) & 15);\n    }','    let rows=pool_v1_pair_forest_copy_active_rows_v1()?;\n    let mut i=0usize;\n    while i<rows.len() {let row=rows[i];masks[usize::from(row)>>4]|=1<<(usize::from(row)&15);i+=1;}')
for op in [132,133,134]:save(op,p,s,'prover-local',['host_semantic::build/copy_poles_clear','prover::build','schedule','endpoint_counts','active rows and masks','legacy schedule constructors','sort/dedup'])
p='crates/aspis-statement/src/pool_v1/pair_forest_trace.rs';s=Path(p).read_text();a=s.index('    for limb in &mut tuple.limbs {');b=s.index('    tuple\n',a);s=s[:a]+'''    let mut i=0usize;
    while i<16 {
        match tuple.limbs[i] {
            PoolV1PairTupleLimbV1::Cell {mut source,offset} => {
                if usize::from(source.cell.row)>=864 {source.cell.row+=48;}
                tuple.limbs[i]=PoolV1PairTupleLimbV1::Cell {source,offset};
            }
            PoolV1PairTupleLimbV1::Zero => {}
        }
        i+=1;
    }
'''+s[b:];s=s.replace('    for scheduled in schedule {','    let mut schedule_index=0usize;\n    while schedule_index<schedule.len() {\n        let scheduled=schedule[schedule_index];',1);a=s.index('            let old = legacy\n');b=s.index('            (\n',a);s=s[:a]+'''            let mut found=None;
            let mut i=0usize;
            while i<legacy.len() && found.is_none() {
                if legacy[i].kind==scheduled.kind {found=Some(legacy[i]);}
                i+=1;
            }
            let old=match found {Some(v)=>v,None=>return Err(PoolV1PairTraceErrorV1::CopyLayout)};
'''+s[b:];pos=s.index('    if output.len() != POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1',a);s=s[:pos].rstrip().removesuffix('}')+'        schedule_index+=1;\n    }\n'+s[pos:];save(228,p,s,'prover-local',['forest trace/helper builders','build_pool_v1_pair_forest_copy_registry_v1','legacy registry','schedule (132 patch)','translate_aux_tuple','tuple_cells'])
p='crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs';s=Path(p).read_text();s=s.replace('    build_copy_logup_helper(&rows, chi).map_err(|_| PoolV1PairTraceErrorV1::CopyImbalance)','    match build_copy_logup_helper(&rows, chi) {Ok(v)=>Ok(v),Err(_)=>Err(PoolV1PairTraceErrorV1::CopyImbalance)}',1);save(224,p,s,'prover-local',['host_semantic::build/build_with_helper_mode','forest copy rows','registry (228)','build_copy_logup_helper','compress_tagged_tuple (223)'])
p='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';s=Path(p).read_text();s=s.replace('                for value in values {\n                    if value.0','                let mut i=0usize;\n                while i<values.len() {\n                    let value=values[i];\n                    if value.0',1).replace('                    out.extend_from_slice(&value.0.to_le_bytes());\n                }','                    out.extend_from_slice(&value.0.to_le_bytes());\n                    i+=1;\n                }',1);save(226,p,s,'prover-local',['host public bytes consumers in prover/transcript','Public::semantic','private_public/withdrawal_public','fields','frontier','Vec append'])
s=Path(p).read_text();s=s.replace('            let selected = core::array::from_fn(|i| claims[i / 28][i % 28]);','            let mut selected=[QM31::ZERO;84];\n            let mut i=0usize;\n            while i<84 {selected[i]=claims[i/28][i%28];i+=1;}');s=s.replace('            terminal_parts(\n                self.semantic(),','            match terminal_parts(\n                self.semantic(),',1).replace('            )\n            .map(|parts| parts.0)\n            .map_err(|_| Error::Public)','            ) {Ok(parts)=>Ok(parts.0),Err(_)=>Err(Error::Public)}',1);save(227,p,s,'prover-local',['host terminal consumers (Public wrapper copied)','Public::semantic','terminal_parts and all family evaluators'])
(D/'candidates.json').write_text(json.dumps(rows,indent=2)+'\n')
