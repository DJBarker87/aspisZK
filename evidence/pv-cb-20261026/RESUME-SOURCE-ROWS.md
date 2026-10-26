# Source equation resume

No endpoint premise removal claimed. Before: 0/73 discharged rows; current: 1/73.

|op|row|status|theorem|receipt / obstruction|
|---:|---|---|---|---|
|3|V169|ROW-DISCHARGED(candidate)|R1Z.PV_CB_TakeSource.op3_source|24000.json; Direct std::mem::take extraction with --include core::mem::take; no P6 bound used.|
|25|V177|OBSTRUCTED|—|aeneas-source-path25-001/collected-receipt.json; Direct shipped deref extraction rejects &raw const (*_5), std/src/path.rs:2414. Existing P6 borrow16 gate lacks a universal or proved-sufficient reach bound.|
|28|V179|OBSTRUCTED|—|kani-string-003/collected-receipt.json; String AsRef<Path> reaches Path::new pointer reinterpretation; direct path primitive extraction failure retained. Existing ASCII/scalar gates do not cover arbitrary UTF8 String.|
|29|V180|OBSTRUCTED|—|aeneas-source-path25-001/collected-receipt.json; PathBuf AsRef<Path> delegates to deref; same Path::new pointer primitive extraction obstruction, bounded P6 gate insufficient.|
