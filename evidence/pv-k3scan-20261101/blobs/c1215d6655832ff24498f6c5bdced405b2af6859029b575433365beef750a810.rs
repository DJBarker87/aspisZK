// Exact owned body copy appended only to this job's native test copy.
impl<T> CoreWrapper<T>
where
    T: FixedOutputCore,
    T::BlockSize: IsLess<U256>,
    Le<T::BlockSize,U256>: NonZero,
{
    pub fn pv_dl_owned_finalize_into(mut self,out:&mut Output<Self>) {
        let Self { core, buffer } = &mut self;
        core.finalize_fixed_core(buffer, out);
    }
}
