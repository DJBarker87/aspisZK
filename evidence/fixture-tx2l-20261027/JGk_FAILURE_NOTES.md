# Rejected source shapes

002: wrong Bool-coercion simplifier in generic transitivity; 003 replaces it with decide_eq_true_eq and passes.
050: inherited unchecked LeafIteration attempted rfl on native packed-key opening indices. 051 instead uses the already-proved symbolic Port4B_KeyDecode.packed equation for arbitrary Fin12 and scalar extensionality; passes.
052: new LeafPush had a record-field indentation parser error and used reserved theorem name prefix. 053 moves the record fields to one line and names the view theorem content. All rejected source snapshots/logs are retained; no recovery sorryAx output grants proof credit.
