fn mark(phase:Phase){
    match phase {
        Phase::QueryPart(i,j)=>msg!("r1:query-part:{}:{}",i,j),
        Phase::SemanticPart(i)=>msg!("r1:semantic-part:{}",i),
        Phase::Parsed=>msg!("r1:parsed"),Phase::Semantic=>msg!("r1:semantic"),Phase::Prepare=>msg!("r1:prepare"),
        Phase::CheckpointRead=>msg!("r1:checkpoint-read"),Phase::CheckpointWrite=>msg!("r1:checkpoint-write"),
        Phase::Merkle(i)=>msg!("r1:merkle:{}",i),Phase::Query(i)=>msg!("r1:query:{}",i),
        Phase::Relation=>msg!("r1:relation"),Phase::Final=>msg!("r1:final"),
    }
    sol_log_compute_units();
}