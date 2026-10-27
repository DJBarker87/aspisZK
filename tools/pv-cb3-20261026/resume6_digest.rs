//! cfg(kani) extraction entry points forcing the shipped generic impl bodies.
use digest::{Digest, FixedOutput, HashMarker, Output, Update};
use digest::core_api::{Buffer, BufferKindUser, CoreWrapper, CtVariableCoreWrapper,
    FixedOutputCore, UpdateCore, VariableOutputCore};
use digest::generic_array::{ArrayLength, GenericArray};
use digest::typenum::{IsLess, IsLessOrEqual, Le, LeEq, NonZero, U256};

pub fn finalize<D:FixedOutput+Default+Update+HashMarker>(d:D)->Output<D> {
    Digest::finalize(d)
}

pub fn core_update<T>(mut c:CoreWrapper<T>, bytes:&[u8])->CoreWrapper<T>
where T:BufferKindUser+UpdateCore, T::BlockSize:IsLess<U256>, Le<T::BlockSize,U256>:NonZero {
    Update::update(&mut c,bytes);
    c
}

pub fn core_default<T>()->CoreWrapper<T>
where T:BufferKindUser+Default, T::BufferKind:Default, T::BlockSize:IsLess<U256>, Le<T::BlockSize,U256>:NonZero {
    CoreWrapper::<T>::default()
}

pub fn core_finalize<T>(c:CoreWrapper<T>,mut out:Output<CoreWrapper<T>>)->Output<CoreWrapper<T>>
where T:FixedOutputCore, T::BlockSize:IsLess<U256>, Le<T::BlockSize,U256>:NonZero {
    FixedOutput::finalize_into(c,&mut out);
    out
}

pub fn ct_finalize<T,S,O>(mut c:CtVariableCoreWrapper<T,S,O>,
    mut buffer:Buffer<CtVariableCoreWrapper<T,S,O>>,mut out:GenericArray<u8,S>)
    ->(CtVariableCoreWrapper<T,S,O>,Buffer<CtVariableCoreWrapper<T,S,O>>,GenericArray<u8,S>)
where T:VariableOutputCore, S:ArrayLength<u8>+IsLessOrEqual<T::OutputSize>+'static,
    LeEq<S,T::OutputSize>:NonZero,T::BlockSize:IsLess<U256>,Le<T::BlockSize,U256>:NonZero {
    FixedOutputCore::finalize_fixed_core(&mut c,&mut buffer,&mut out);
    (c,buffer,out)
}
