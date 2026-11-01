// Derived CoreWrapper default, expanded in original field declaration order.
impl<T> CoreWrapper<T>
where T:BufferKindUser+Default,T::BlockSize:IsLess<U256>,Le<T::BlockSize,U256>:NonZero {
    pub fn pv_dl_owned_default()->Self {
        Self {core:Default::default(),buffer:Default::default()}
    }
}
