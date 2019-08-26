// Copyright (c) 2017, 2018, 2019 Alexey Tourbin
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#pragma once
#ifndef __cplusplus
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#else
#include <cstddef>
#include <cstdint>
extern "C" {
#endif

// Beta version, static linking only.
#ifdef __GNUC__
#pragma GCC visibility push(hidden)
#endif

struct fp47set *fp47set_new(int logsize);
void fp47set_free(struct fp47set *set);

// i386 convention: on Windows, stick to fastcall, for compatibility with msvc.
#if (defined(_WIN32) || defined(__CYGWIN__)) && \
    (defined(_M_IX86) || defined(__i386__))
#define FP47SET_MSFASTCALL 1
#if defined(__GNUC__)
#define FP47SET_FASTCALL __attribute__((fastcall))
#else
#define FP47SET_FASTCALL __fastcall
#endif
#else // otherwise, use regparm(3).
#define FP47SET_MSFASTCALL 0
#if defined(__i386__)
#define FP47SET_FASTCALL __attribute__((regparm(3)))
#else
#define FP47SET_FASTCALL
#endif
#endif

// fastcall has trouble passing uint64_t in registers.
#if FP47SET_MSFASTCALL
#define FP47SET_pFP64 uint32_t lo, uint32_t hi
#define FP47SET_aFP64(fp) fp, fp >> 32
#else
#define FP47SET_pFP64 uint64_t fp
#define FP47SET_aFP64(fp) fp
#endif

// Expose the structure, to inline vfunc calls.
struct fp47set {
    // To reduce the failure rate, one or two fingerprints can be stashed.
    uint32_t stash[4];
    // Virtual functions, depend on the bucket size, switched on resize.
    // Pass fp arg first, eax:edx may hold hash() return value.
    int (FP47SET_FASTCALL *add)(FP47SET_pFP64, struct fp47set *set);
    int (FP47SET_FASTCALL *has)(FP47SET_pFP64, const struct fp47set *set);
    // The buckets (malloc'd); each bucket has bsize slots.
    // Two-dimensional structure is emulated with pointer arithmetic.
    uint32_t *bb;
    // The total number of unique fingerprints added to buckets,
    // not including the stashed fingerprints.
    size_t cnt;
    // The number of slots in each bucket: 2, 3, or 4.
    uint8_t bsize;
    // The number of fingerprints stashed: 0, 1, or 2.
    uint8_t nstash;
    // The number of buckets, initial and current, the logarithm: 4..32.
    uint8_t logsize0, logsize1;
    // The corresponding masks, help indexing into the buckets.
    uint32_t mask0, mask1;
};

// Add a 64-bit fingerprint to the set.  Returns 0 for a previously added
// fingerprint, 1 when the new fingerprint was added smoothly; 2 if the
// structure has been resized (when this regularly happens more than once,
// it indicates that the initial logsize value passed to fp47set_new was too
// small).  Returns -1 on malloc failure (ENOMEM); or the insertion can fail
// just by chance (EAGAIN), which means that a series of evictions failed,
// and an unrelated fingerprint has been kicked out.  Unless false negatives
// are permitted, the only option in this case is to rebuild the set from
// scratch, fingerprinting the data with a different seed.  The possibility
// of this kind of failure decreases exponentially with logsize.
static inline int fp47set_add(struct fp47set *set, uint64_t fp)
{
    return set->add(FP47SET_aFP64(fp), set);
}

// Check if a fingerprint is in the set.
static inline bool fp47set_has(const struct fp47set *set, uint64_t fp)
{
    // An implementation detail: set->has returns int because in SSE assembly
    // we can simply do "pmovmskb %xmm,%eax".  Conversion to bool can usually
    // be optimized out - the compiler should "test %eax,%eax" instead of %al.
    return set->has(FP47SET_aFP64(fp), set);
}

#ifdef __GNUC__
#pragma GCC visibility pop
#endif

#ifdef __cplusplus
}
#endif
