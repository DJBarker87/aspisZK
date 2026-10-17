/// Host-only secret salts retained until queried openings have been emitted.
/// Drop overwrites the full salt buffer so salts for unopened leaves are not
/// left in the allocator after proof construction.
pub struct PrivateSalts(Vec<[u8; 32]>);