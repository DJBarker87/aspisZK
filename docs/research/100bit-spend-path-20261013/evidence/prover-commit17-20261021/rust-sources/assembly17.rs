// Proof-only outer assembly. All vectors and expander states are fresh owned
// bindings at call boundaries. Begins after nonce reservation and seed setup.
#[cfg(any(kani, aeneas_ref))]
pub(crate) struct OwnedMaterial17 {
    pub(crate) c1: Vec<M31>,
    pub(crate) columns: Vec<Vec<M31>>,
    pub(crate) g: Vec<aspis_core::field::QM31>,
    pub(crate) padding: Vec<aspis_core::field::QM31>,
    pub(crate) nonce: [u8;32],
}
#[cfg(any(kani, aeneas_ref))]
pub(crate) fn assemble_owned17(hash: HashFn, domain: &[u8], state: State,
    cells: usize, c1: Vec<M31>, columns: Vec<Vec<M31>>,
    g: Vec<aspis_core::field::QM31>, padding: Vec<aspis_core::field::QM31>,
    dependent: usize, active: &[bool;1024], nonce: [u8;32])
    -> (Result<OwnedMaterial17,StateOnlyMaskBuildError>,State)
{
    let (status,c1,after_c1)=collect_m31_owned(hash,domain,state,cells,c1);
    if let Err(e)=status {return (Err(e),after_c1);}
    let (status,columns,after_columns)=material_columns_owned(hash,domain,after_c1,
        columns,0,10,dependent,active);
    if let Err(e)=status {return (Err(e),after_columns);}
    let (status,g,after_g)=collect_qm31_owned(hash,domain,after_columns,1024,g);
    if let Err(e)=status {return (Err(e),after_g);}
    let (status,g)=balance_qm31_owned(g,dependent,active);
    if let Err(e)=status {return (Err(e),after_g);}
    let (status,padding,final_state)=material_padding_owned(hash,domain,after_g,
        padding,0,dependent,active);
    if let Err(e)=status {return (Err(e),final_state);}
    let (status,padding)=balance_qm31_owned(padding,dependent,active);
    if let Err(e)=status {return (Err(e),final_state);}
    (Ok(OwnedMaterial17{c1,columns,g,padding,nonce}),final_state)
}
