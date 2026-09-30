// Const coalescing of the EXISTING exact ordered endpoint registry.
#[derive(Clone,Copy)]
struct R105Term{term:R57Term,count:u16}
const fn r105_table()->([u16;74],[R105Term;544]){
    let mut offsets=[0u16;74];let empty=R105Term{term:R57Term{high:0,kind:0,level:0},count:0};
    let mut terms=[empty;544];let mut next=0;let mut coordinate=0;
    while coordinate<73{
        let start=next;let mut i=R57_TABLE.0[coordinate]as usize;
        while i<R57_TABLE.0[coordinate+1]as usize{
            let t=R57_TABLE.1[i];let mut at=start;
            // Level is irrelevant to unconditional and variant-only terms.
            while at<next && !(terms[at].term.high==t.high && terms[at].term.kind==t.kind
                && (t.kind<3 || terms[at].term.level==t.level)){at+=1;}
            if at==next{terms[next]=R105Term{term:t,count:1};next+=1;}
            else{terms[at].count+=1;}
            i+=1;
        }
        offsets[coordinate+1]=next as u16;coordinate+=1;
    }
    (offsets,terms)
}
static R105_TABLE:([u16;74],[R105Term;544])=r105_table();
#[inline(never)]
fn r57_gather(scratch:&mut[QM31],selectors:&Selectors,append:u64,variant:PoolV1PairForestCompiledVariantV1){
    for coordinate in 0..73{
        let mut raw=[0u64;4];
        for index in usize::from(R105_TABLE.0[coordinate])..usize::from(R105_TABLE.0[coordinate+1]){
            let entry=R105_TABLE.1[index];
            if r57_enabled(entry.term,append,variant){
                let v=selectors.high[usize::from(entry.term.high)];let c=u64::from(entry.count);
                // Total multiplicity <=544, even for full-width raw u32 limbs.
                raw[0]+=u64::from(v.c0.a.0)*c;raw[1]+=u64::from(v.c0.b.0)*c;
                raw[2]+=u64::from(v.c1.a.0)*c;raw[3]+=u64::from(v.c1.b.0)*c;
            }
        }
        scratch[30+coordinate]=QM31{c0:CM31::new(M31::reduce_u64(raw[0]),M31::reduce_u64(raw[1])),
            c1:CM31::new(M31::reduce_u64(raw[2]),M31::reduce_u64(raw[3]))};
    }
}
#[cfg(not(v8_performance_sbf))]
pub fn r105_table_controls()->usize{
    // Exact integer coefficient equality for EVERY high/kind/level coordinate.
    for coordinate in 0..73{for high in 0..64{for kind in 0..5{for level in 0..64{
        if kind<3 && level!=0{continue;}
        let key=|t:R57Term|t.high==high && t.kind==kind && (kind<3 || t.level==level);
        let old=(usize::from(R57_TABLE.0[coordinate])..usize::from(R57_TABLE.0[coordinate+1])).filter(|&i|key(R57_TABLE.1[i])).count();
        let new:usize=(usize::from(R105_TABLE.0[coordinate])..usize::from(R105_TABLE.0[coordinate+1])).filter(|&i|key(R105_TABLE.1[i].term)).map(|i|usize::from(R105_TABLE.1[i].count)).sum();
        assert_eq!(old,new);
    }}}}
    usize::from(R105_TABLE.0[73])
}
