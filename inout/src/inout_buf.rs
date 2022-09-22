use crate::{
    errors::{IntoArrayError, NotEqualError},
    InOut,
};
use core::{marker::PhantomData, slice};
use generic_array::{ArrayLength, GenericArray};

/// Custom slice type which references one immutable (input) slice and one
/// mutable (output) slice of equal length. Input and output slices are
/// either the same or do not overlap.
pub struct InOutBuf<'inp, 'out, T> {
    // Invariant: The invariants required by the `from_raw` constructor must
    // always hold.
    in_ptr: *const T,
    out_ptr: *mut T,
    len: usize,
    _pd: PhantomData<(&'inp T, &'out mut T)>,
}

impl<'a, T> From<&'a mut [T]> for InOutBuf<'a, 'a, T> {
    #[inline(always)]
    fn from(buf: &'a mut [T]) -> Self {
        let p = buf.as_mut_ptr();
        Self {
            in_ptr: p,
            out_ptr: p,
            len: buf.len(),
            _pd: PhantomData,
        }
    }
}

impl<'a, T> InOutBuf<'a, 'a, T> {
    /// Create `InOutBuf` from a single mutable reference.
    ///
    /// # Panics
    ///
    /// Panics if `mem::size_of::<T>()` overflows `isize`.
    #[inline(always)]
    pub fn from_mut(val: &'a mut T) -> InOutBuf<'a, 'a, T> {
        assert!(core::mem::size_of::<T>() <= isize::MAX as usize);
        let p = val as *mut T;

        // SAFETY:
        // - `in_ptr` is initialized from `val`, which is guaranteed to point to
        //   a properly aligned and initialized value of type `T`, and is valid
        //   for reads of size `len * mem::size_of::<T>()` (`len` is set to 1).
        //   Since `val` is a reference, these bytes are guaranteed to lie in a
        //   single allocation.
        // - `out_ptr` is initialized from `val`, which is guaranteed to point
        //   to a properly aligned and initialized value of type `T`, and is
        //   valid for reads and writes of size `len * mem::size_of::<T>()`
        //   (`len` is set to 1). Since `val` is a reference, these bytes are
        //   guaranteed to lie in a single allocation.
        // - `in_ptr` and `out_ptr` are equal since they come from the same
        //   reference.
        // - `in_ptr` and `out_ptr` point to the same allocated object (`*val`),
        //   and the memory referenced by them cannot be accessed through any
        //   other pointer (guaranteed by the fact that `val` is a mutable
        //   reference). Since `val` has the lifetime `'a`, this restriction is
        //   upheld for the duration of `'a`.
        // - The total size of `len * mem::size_of::<T>()` cannot overflow
        //   `isize::MAX` thanks to the preceding assert and the fact that `len`
        //   is set to 1.
        unsafe { Self::from_raw(p, p, 1) }
    }
}

impl<'inp, 'out, T> IntoIterator for InOutBuf<'inp, 'out, T> {
    type Item = InOut<'inp, 'out, T>;
    type IntoIter = InOutBufIter<'inp, 'out, T>;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        InOutBufIter { buf: self, pos: 0 }
    }
}

impl<'inp, 'out, T> InOutBuf<'inp, 'out, T> {
    /// Create `InOutBuf` from a pair of immutable and mutable references.
    ///
    /// # Panics
    ///
    /// Panics if `mem::size_of::<T>()` overflows `isize`.
    #[inline(always)]
    pub fn from_ref_mut(in_val: &'inp T, out_val: &'out mut T) -> Self {
        assert!(core::mem::size_of::<T>() <= isize::MAX as usize);

        // SAFETY:
        // - `in_ptr` is initialized from `in_val`, which is guaranteed to point
        //   to a properly aligned and initialized value of type `T`, and is
        //   valid for reads of size `len * mem::size_of::<T>()` (`len` is set
        //   to 1). Since `in_val` is a reference, these bytes are guaranteed to
        //   lie in a single allocation.
        // - `out_ptr` is initialized from `out_val`, which is guaranteed to
        //   point to a properly aligned and initialized value of type `T`, and
        //   is valid for reads and writes of size `len * mem::size_of::<T>()`
        //   (`len` is set to 1). Since `out_val` is a reference, these bytes
        //   are guaranteed to lie in a single allocation.
        // - `in_ptr` and `out_ptr` are non-overlapping since `out_val` is a
        //   mutable reference.
        // - The memory accessed through `out_ptr` cannot be accessed through
        //   any other pointer for the duration of `'out` since `out_val` is a
        //   mutable reference with the lifetime `'out`.
        // - The total size of `len * mem::size_of::<T>()` cannot overflow
        //   `isize::MAX` thanks to the preceding assert and the fact that `len`
        //   is set to 1.
        unsafe { Self::from_raw(in_val as *const T, out_val as *mut T, 1) }
    }

    /// Create `InOutBuf` from immutable and mutable slices.
    ///
    /// Returns an error if length of slices is not equal to each other.
    ///
    /// # Panics
    ///
    /// Panics if `in_buf.len() * mem::size_of::<T>()` overflows an `isize`.
    #[inline(always)]
    pub fn new(in_buf: &'inp [T], out_buf: &'out mut [T]) -> Result<Self, NotEqualError> {
        // SAFETY: This multiplication is guaranteed not to overflow since
        // `in_buf` exists in memory, and does not wrap around. We can use that
        // fact in our safety analysis below.
        assert!(in_buf.len() * core::mem::size_of::<T>() <= isize::MAX as usize);
        if in_buf.len() != out_buf.len() {
            Err(NotEqualError)
        } else {
            // SAFETY:
            // - `in_ptr` is initialized from `in_buf`, which is guaranteed to
            //   point to `in_buf.len()` properly aligned and initialized values
            //   of type `T`, and is valid for reads of size `in_buf.len() *
            //   mem::size_of::<T>()` by definition of `&[T]`. Since `in_buf` is
            //   a reference, these bytes are guaranteed to lie in a single
            //   allocation.
            // - `out_ptr` is initialized from `out_buf`, which, thanks to the
            //   `in_buf.len() != out_buf.len()` check, is guaranteed to point
            //   to `in_buf.len()` properly aligned and initialized values of
            //   type `T`, and is valid for reads and writes of size
            //   `in_buf.len() * mem::size_of::<T>()` by definition of `&mut
            //   [T]`. Since `out_buf` is a reference, these bytes are
            //   guaranteed to lie in a single allocation.
            // - `in_ptr` and `out_ptr` are non-overlapping since `out_buf` is a
            //   mutable reference.
            // - The memory accessed through `out_ptr` cannot be accessed
            //   through any other pointer for the duration of `'out` since
            //   `out_buf` is a mutable reference with the lifetime `'out`.
            // - The total size of `len * mem::size_of::<T>()` cannot overflow
            //   `isize::MAX` thanks to the preceding assert and the
            //   `in_buf.len() != out_buf.len()` check.
            unsafe {
                Ok(Self::from_raw(
                    in_buf.as_ptr(),
                    out_buf.as_mut_ptr(),
                    in_buf.len(),
                ))
            }
        }
    }

    /// Get length of the inner buffers.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the buffer has a length of 0.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns an `InOut` for the given position without checking safety
    /// invariants.
    ///
    /// # Safety
    ///
    /// It is undefined behavior to call `get_unchecked` with `pos >=
    /// self.len()`.
    #[inline(always)]
    unsafe fn get_unchecked(&mut self, pos: usize) -> InOut<'inp, 'out, T> {
        // SAFETY: TODO
        unsafe { InOut::from_raw(self.in_ptr.add(pos), self.out_ptr.add(pos)) }
    }

    /// Returns `InOut` for given position.
    ///
    /// # Panics
    /// If `pos` greater or equal to buffer length.
    #[inline(always)]
    pub fn get<'a>(&'a mut self, pos: usize) -> InOut<'a, 'a, T> {
        assert!(pos < self.len);
        // SAFETY: `get_unchecked` only requires than `pos < self.len`, which we
        // just asserted.
        unsafe { self.get_unchecked(pos) }
    }

    /// Get input slice.
    #[inline(always)]
    pub fn get_in<'a>(&'a self) -> &'a [T] {
        // SAFETY:
        // - `self.in_ptr` is guaranteed by invariants to be valid for reads of
        //   size `len * mem::size_of::<T>()`, and to point to `len` aligned and
        //   intialized values of `T` which lie within a single allocation.
        // - The memory in question is guaranteed by invariants not to be
        //   mutated for the duration of `'a`, except if all views of that
        //   memory (including `T`) treat it as contained in `UnsafeCell`s.
        // - Invariants guarantee that `self.len * mem::size_of::<T>()` does not
        //   overflow an `isize`.
        unsafe { slice::from_raw_parts(self.in_ptr, self.len) }
    }

    /// Get output slice.
    #[inline(always)]
    pub fn get_out<'a>(&'a mut self) -> &'a mut [T] {
        // SAFETY:
        // - `self.in_ptr` is guaranteed by invariants to be a non-null pointer
        //   which is valid for reads of size `len * mem::size_of::<T>()`, and
        //   to point to `len` aligned and intialized values of `T` which lie
        //   within a single allocation.
        // - The memory in question is guaranteed by invariants not to be
        //   mutated for the duration of `'a`, except if all views of that
        //   memory (including `T`) treat it as contained in `UnsafeCell`s.
        // - Invariants guarantee that `self.len * mem::size_of::<T>()` does not
        //   overflow an `isize`.
        unsafe { slice::from_raw_parts_mut(self.out_ptr, self.len) }
    }

    /// Consume self and return output slice with lifetime `'a`.
    #[inline(always)]
    pub fn into_out(self) -> &'out mut [T] {
        // SAFETY:
        // - `self.out_ptr` is guaranteed by invariants to be a non-null pointer
        //   which is valid for reads of size `len * mem::size_of::<T>()`, and
        //   to point to `len` aligned and intialized values of `T` which lie
        //   within a single allocation.
        // - The memory in question is guaranteed by invariants not to be
        //   aliased for the duration of `'a`.
        // - Invariants guarantee that `self.len * mem::size_of::<T>()` does not
        //   overflow an `isize`.
        unsafe { slice::from_raw_parts_mut(self.out_ptr, self.len) }
    }

    /// Get raw input and output pointers.
    #[inline(always)]
    pub fn into_raw(self) -> (*const T, *mut T) {
        (self.in_ptr, self.out_ptr)
    }

    /// Reborrow `self`.
    #[inline(always)]
    pub fn reborrow<'a>(&'a mut self) -> InOutBuf<'a, 'a, T> {
        // SAFETY: Since `self` is borrowed mutably for `'a`, and the returned
        // `InOutBuf` has the lifetime `'a`, no methods may be called on `self`
        // while the returned `InOutBuf` exists. Since the returned `InOutBuf`
        // has exactly the same contents as `self`, all methods called on a
        // reference - mutable or immutable - to the returned `InOutBuf` are
        // sound because the same methods called on `self` would have been sound
        // if `reborrow` had not been called. Finally, all methods which take
        // `InOutBuf` by value return values which are bound by `'a`, and none
        // of those methods invalidate any of the invariants on any of the
        // fields of `InOutBuf`.
        Self {
            in_ptr: self.in_ptr,
            out_ptr: self.out_ptr,
            len: self.len,
            _pd: PhantomData,
        }
    }

    /// Create [`InOutBuf`] from raw input and output pointers.
    ///
    /// # Safety
    /// Behavior is undefined if any of the following conditions are violated:
    /// - `in_ptr` must be non-null, must point to `len` contiguous properly
    /// aligned and initialized values of type `T`, and must be valid for reads
    /// for `len * mem::size_of::<T>()` many bytes. These bytes must lie within
    /// a single allocation.
    /// - `out_ptr` must be non-null, must point to `len` contiguous properly
    /// aligned and initialized values of type `T`, and must be valid for both
    /// reads and writes for `len * mem::size_of::<T>()` many bytes. These bytes
    /// must lie within a single allocation.
    /// - `in_ptr` and `out_ptr` must be either equal or non-overlapping.
    /// - If `in_ptr` and `out_ptr` are equal, then they must point to the same
    /// allocated object, and the memory referenced by them must not be accessed
    /// through any other pointer (not derived from the return value) for the
    /// duration of lifetime 'a. Both read and write accesses are forbidden.
    /// - If `in_ptr` and `out_ptr` are not equal, then the memory referenced by
    /// `out_ptr` must not be accessed through any other pointer (not derived
    /// from the return value) for the duration of lifetime 'a. Both read and
    /// write accesses are forbidden. The memory referenced by `in_ptr` must not
    /// be mutated for the duration of lifetime `'a`, except if all references
    /// to that memory treat it as one or more `UnsafeCell`s (including `T`).
    /// - The total size `len * mem::size_of::<T>()`  must be no larger than
    /// `isize::MAX`.
    #[inline(always)]
    pub unsafe fn from_raw(
        in_ptr: *const T,
        out_ptr: *mut T,
        len: usize,
    ) -> InOutBuf<'inp, 'out, T> {
        Self {
            in_ptr,
            out_ptr,
            len,
            _pd: PhantomData,
        }
    }

    /// Divides one buffer into two at `mid` index.
    ///
    /// The first will contain all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will contain all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// # Panics
    ///
    /// Panics if `mid > len`.
    #[inline(always)]
    pub fn split_at(self, mid: usize) -> (InOutBuf<'inp, 'out, T>, InOutBuf<'inp, 'out, T>) {
        assert!(mid <= self.len);
        // SAFETY: TODO
        let (tail_in_ptr, tail_out_ptr) = unsafe { (self.in_ptr.add(mid), self.out_ptr.add(mid)) };
        (
            InOutBuf {
                in_ptr: self.in_ptr,
                out_ptr: self.out_ptr,
                len: mid,
                _pd: PhantomData,
            },
            InOutBuf {
                in_ptr: tail_in_ptr,
                out_ptr: tail_out_ptr,
                len: self.len - mid,
                _pd: PhantomData,
            },
        )
    }

    /// Partition buffer into 2 parts: buffer of arrays and tail.
    #[inline(always)]
    pub fn into_chunks<N: ArrayLength<T>>(
        self,
    ) -> (
        InOutBuf<'inp, 'out, GenericArray<T, N>>,
        InOutBuf<'inp, 'out, T>,
    ) {
        let chunks = self.len() / N::USIZE;
        let tail_pos = N::USIZE * chunks;
        let tail_len = self.len() - tail_pos;
        // SAFETY: TODO
        unsafe {
            let chunks = InOutBuf {
                in_ptr: self.in_ptr as *const GenericArray<T, N>,
                out_ptr: self.out_ptr as *mut GenericArray<T, N>,
                len: chunks,
                _pd: PhantomData,
            };
            let tail = InOutBuf {
                in_ptr: self.in_ptr.add(tail_pos),
                out_ptr: self.out_ptr.add(tail_pos),
                len: tail_len,
                _pd: PhantomData,
            };
            (chunks, tail)
        }
    }
}

impl<'inp, 'out> InOutBuf<'inp, 'out, u8> {
    /// XORs `data` with values behind the input slice and write
    /// result to the output slice.
    ///
    /// # Panics
    /// If `data` length is not equal to the buffer length.
    #[inline(always)]
    #[allow(clippy::needless_range_loop)]
    pub fn xor_in2out(&mut self, data: &[u8]) {
        assert_eq!(self.len, data.len());
        // SAFETY:
        // - Safety of `add` calls:
        //   - It is guaranteed by invariants that both `in_ptr` and `out_ptr`
        //     point to ranges of `len * mem::size_of::<u8>()` bytes which each
        //     fall entirely within a single allocated object. Since `i <
        //     data.len() == len`, all calls to `add(i)` result in a pointer
        //     which is still in bounds of the original allocation (`in_ptr` or
        //     `out_ptr` respectively).
        //   - It is guaranteed by invariants that `len * mem::size_of::<u8>()`
        //     does not overflow an `isize`. Since `i < data.len() == len`, all
        //     calls to `add(i)` are guaranteed to result in a "computed offset"
        //     (to use the `add` docs' phrase) which does not overflow an
        //     `isize`.
        //   - Since `in_ptr` and `out_ptr` each point to a single allocation of
        //     length at most `len`, allocations cannot wrap around the address
        //     space, and `i < len`, the `add(i)` calls cannot wrap around the
        //     address space.
        // - Safety of dereferences:
        //   - By the preceding arguments, the `add(i)` calls result in pointers
        //     which are in-bounds of `in_ptr` and `out_ptr` respectively.
        //   - Invariants on `InOutBuf` guarantee that `in_ptr` is valid for
        //     reads and that `out_ptr` is valid for writes.
        //   - Since `*in_ptr` and `*out_ptr` do not create references,
        //     performing both dereferences on the same line is sound even if
        //     `in_ptr` and `out_ptr` point to the same allocation. While this
        //     is not a proof of soundness, it has been confirmed that a similar
        //     program is not rejected by Miri [1].
        //
        // [1] https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=0eaaa226eabddbfc8974ef33a9f0d170
        unsafe {
            for i in 0..data.len() {
                let in_ptr = self.in_ptr.add(i);
                let out_ptr = self.out_ptr.add(i);
                *out_ptr = *in_ptr ^ data[i];
            }
        }
    }
}

impl<'inp, 'out, T, N> TryInto<InOut<'inp, 'out, GenericArray<T, N>>> for InOutBuf<'inp, 'out, T>
where
    N: ArrayLength<T>,
{
    type Error = IntoArrayError;

    #[inline(always)]
    fn try_into(self) -> Result<InOut<'inp, 'out, GenericArray<T, N>>, Self::Error> {
        if self.len() == N::USIZE {
            // SAFETY: TODO
            unsafe {
                Ok(InOut::from_raw(
                    self.in_ptr as *const _,
                    self.out_ptr as *mut _,
                ))
            }
        } else {
            Err(IntoArrayError)
        }
    }
}

/// Iterator over [`InOutBuf`].
pub struct InOutBufIter<'inp, 'out, T> {
    buf: InOutBuf<'inp, 'out, T>,
    pos: usize,
}

impl<'inp, 'out, T> Iterator for InOutBufIter<'inp, 'out, T> {
    type Item = InOut<'inp, 'out, T>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.buf.len() == self.pos {
            return None;
        }

        // SAFETY: `get_unchecked` only requires than `self.pos < self.buf.len`,
        // which is guaranteed by the preceding bounds check.
        unsafe { self.buf.get_unchecked(self.pos) };
        let res = unsafe { self.buf.get_unchecked(self.pos) };
        self.pos += 1;
        Some(res)
    }
}
