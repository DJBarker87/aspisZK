// Proof-only owned references. Not enabled in any production configuration.
#[cfg(any(kani,aeneas_ref))]
pub mod owned19 {
    use alloc::vec::Vec;
    pub fn concat(parts:Vec<Vec<u8>>,index:usize,mut output:Vec<u8>)->Vec<u8> {
        if index==parts.len() { return output; }
        let part=parts[index].clone();
        output.extend_from_slice(&part);
        concat(parts,index.wrapping_add(1),output)
    }
    // One program-table transition, including conflict retention.
    // The table is represented by unique-key entries; ordering is immaterial
    // to lookup, while the simulator's public iteration order needs transport.
    pub fn insert(mut table:Vec<(Vec<u8>,[u8;32])>,index:usize,address:Vec<u8>,answer:[u8;32],collision:bool)
        ->(Vec<(Vec<u8>,[u8;32])>,bool) {
        if index==table.len() {
            table.push((address,answer));
            return (table,collision);
        }
        let (key,previous)=table[index].clone();
        if key==address {
            table[index]=(key,answer);
            (table,collision || previous!=answer)
        } else {
            insert(table,index.wrapping_add(1),address,answer,collision)
        }
    }

    // Owned recursion for the actual walk's 25 semantic transcript rows.
    // The callee is unchanged. Both its advanced transcript and semantic
    // error are retained; no callback success or hash law is asserted here.
    pub fn semantic_rows<H:aspis_core::Digest32>(
        mut state:crate::r1_wire::SemanticTranscript<H>, records:Vec<Vec<u8>>,
        row:usize,mut sem:[aspis_core::field::QM31;25])
        ->Result<(crate::r1_wire::SemanticTranscript<H>,[aspis_core::field::QM31;25]),super::Error> {
        if row==25 {return Ok((state,sem));}
        let record=records[row].clone();
        let value=state.semantic(row as u8,&record).map_err(|_|super::Error::Semantic)?;
        sem[row]=value;
        semantic_rows(state,records,row.wrapping_add(1),sem)
    }
}
