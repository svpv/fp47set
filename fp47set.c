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

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "fp47set.h"

#define unlikely(cond) __builtin_expect(cond, 0)
#define HIDDEN __attribute__((visibility("hidden")))

// The inline functions below rely heavily on constant propagation.
#define inline inline __attribute__((always_inline))

// 1 + fp % UINT32_MAX
static inline uint32_t mod32(uint64_t fp)
{
    uint32_t lo = fp;
    uint32_t hi = fp >> 32;
    lo += 1;
    if (unlikely(lo == 0))
	lo = 1;
    lo += hi;
    lo += (lo < hi);
    return lo;
}

// Fingerprint to indices.
// Note that the two buckets are completely symmetrical with regard to xor,
// i.e. the information about "the first and true" index is not preserved.
// This looses about 1 bit out of 32+logsize bits of hashing material.
#define dFP2I					\
    uint32_t i1 = fp;				\
    uint32_t fptag = mod32(fp);			\
    uint32_t i2 = i1 ^ fptag;			\
    i1 &= set->mask0;				\
    i2 &= set->mask0

// Fingerprint to indices and buckets.
#define dFP2IB					\
    dFP2I;					\
    if (resized || nstash)			\
	Sort2(i1, i2);				\
    if (resized) {				\
	i1 |= fptag << set->logsize0;		\
	i2 = i1 ^ fptag;			\
	i1 &= set->mask1;			\
	i2 &= set->mask1;			\
    }						\
    uint32_t *b1 = set->bb + i1 * bsize;	\
    uint32_t *b2 = set->bb + i2 * bsize

// How do we sort two numbers?  That's a major problem in computer science.
// I thought that cmov might help, but this does not seem to be the case.
#define Sort2swap(i1, i2)		\
    do {				\
	if (i1 > i2) {			\
	    uint32_t i3 = i1;		\
	    i1 = i2, i2 = i3;		\
	}				\
    } while (0)
#define Sort2 Sort2swap

static inline size_t has(uint32_t fptag,
	const uint32_t *b1, const uint32_t *b2, uint32_t i1, uint32_t i2,
	const uint32_t stash[4], int bsize, bool resized, int nstash)
{
    // Issue loads for both buckets.
    int has1 = fptag == b1[0];
    int has2 = fptag == b2[0];
    // Stashed elements can be checked in the meantime.
    if (nstash > 0 && unlikely(fptag == stash[0]) && (i1 == stash[1] || i2 == stash[1])) return 1;
    if (nstash > 1 && unlikely(fptag == stash[2]) && (i1 == stash[3] || i2 == stash[3])) return 1;
    // Check the rest of the slots.
    if (bsize > 1) {
	has1 |= fptag == b1[1];
	has2 |= fptag == b2[1];
    }
    if (bsize > 2) {
	has1 |= fptag == b1[2];
	has2 |= fptag == b2[2];
    }
    if (bsize > 3) {
	has1 |= fptag == b1[3];
	has2 |= fptag == b2[3];
    }
    return has1 | has2;
}

// Template for set->has virtual functions.
static inline size_t t_has(const struct fp47set *set, uint64_t fp,
	int bsize, bool resized, int nstash)
{
    dFP2IB;
    return has(fptag, b1, b2, i1, i2, set->stash, bsize, resized, nstash);
}

// Instantiate generic functions, only prototypes for now.
#define MakeVFuncs(BS, RE, ST) \
    static FP47SET_FASTCALL int fp47set_add##BS##re##RE##st##ST(FP47SET_pFP64, struct fp47set *set); \
    static FP47SET_FASTCALL int fp47set_has##BS##re##RE##st##ST(FP47SET_pFP64, const struct fp47set *set);

// There are no resized function for bsize == 2, becuase we first go 2->3->4,
// then double the number of buckets and go 3->4 again.
#define MakeAllVFuncs \
    MakeVFuncs(2, 0, 0) MakeVFuncs(2, 0, 1) MakeVFuncs(2, 0, 2) \
    MakeVFuncs(3, 0, 0) MakeVFuncs(3, 0, 1) MakeVFuncs(3, 0, 2) \
    MakeVFuncs(4, 0, 0) MakeVFuncs(4, 0, 1) MakeVFuncs(4, 0, 2) \
    MakeVFuncs(3, 1, 0) MakeVFuncs(3, 1, 1) MakeVFuncs(3, 1, 2) \
    MakeVFuncs(4, 1, 0) MakeVFuncs(4, 1, 1) MakeVFuncs(4, 1, 2)
MakeAllVFuncs

// When BS and RE are literals.
#define setVFuncsBR(set, BS, RE, nstash)		\
do {							\
    if (nstash == 0)					\
	set->add = fp47set_add##BS##re##RE##st0,	\
	set->has = fp47set_has##BS##re##RE##st0;	\
    else if (nstash == 1)				\
	set->add = fp47set_add##BS##re##RE##st1,	\
	set->has = fp47set_has##BS##re##RE##st1;	\
    else						\
	set->add = fp47set_add##BS##re##RE##st2,	\
	set->has = fp47set_has##BS##re##RE##st2;	\
} while (0)

static inline void setVFuncs(struct fp47set *set, int bsize, bool resized, int nstash)
{
    if (bsize == 2) {
	if (resized)
	    assert(0);
	else
	    setVFuncsBR(set, 2, 0, nstash);
    }
    else if (bsize == 3) {
	if (resized)
	    setVFuncsBR(set, 3, 1, nstash);
	else
	    setVFuncsBR(set, 3, 0, nstash);
    }
    else {
	if (resized)
	    setVFuncsBR(set, 4, 1, nstash);
	else
	    setVFuncsBR(set, 4, 0, nstash);
    }
}

struct fp47set *fp47set_new(int logsize)
{
    assert(logsize >= 0);
    if (logsize < 4)
	logsize = 4;
    // The ultimate limit: two 32-bit halves out of each fingerprint.
    if (logsize > (sizeof(size_t) > 4 ? 32 : 31))
	return NULL;

    // Starting with two slots per bucket.
    size_t nb = (size_t) 1 << logsize;
    uint32_t *bb = calloc(nb, 2 * sizeof(uint32_t));
    if (!bb)
	return NULL;

    struct fp47set *set = malloc(sizeof *set);
    if (!set)
	return free(bb), NULL;

    set->bb = bb;
    set->cnt = 0;
    set->bsize = 2;
    set->nstash = 0;
    set->logsize0 = set->logsize1 = logsize;
    set->mask0 = set->mask1 = nb - 1;

    setVFuncs(set, 2, 0, 0);
    return set;
}

void fp47set_free(struct fp47set *set)
{
    if (!set)
	return;
#ifdef FP47SET_DEBUG
    // The number of entries must match the occupied slots.
    size_t cnt = 0;
    uint32_t *bb = set->bb;
    size_t n = set->bsize * (set->mask1 + (size_t) 1);
    for (size_t i = 0; i < n; i += 4)
	cnt += (bb[i+0] > 0)
	    +  (bb[i+1] > 0)
	    +  (bb[i+2] > 0)
	    +  (bb[i+3] > 0);
    assert(cnt == set->cnt);
#endif
    free(set->bb);
    free(set);
}

static inline bool insert1(uint32_t fptag, uint32_t *b, int bsize)
{
    if (bsize > 0 && b[0] == 0) return b[0] = fptag, true;
    if (bsize > 1 && b[1] == 0) return b[1] = fptag, true;
    if (bsize > 2 && b[2] == 0) return b[2] = fptag, true;
    if (bsize > 3 && b[3] == 0) return b[3] = fptag, true;
    return false;
}

static inline bool insert2(uint32_t fptag, uint32_t *b1, uint32_t *b2, int bsize)
{
    if (bsize > 0 && b1[0] == 0) return b1[0] = fptag, true;
    if (bsize > 0 && b2[0] == 0) return b2[0] = fptag, true;
    if (bsize > 1 && b1[1] == 0) return b1[1] = fptag, true;
    if (bsize > 1 && b2[1] == 0) return b2[1] = fptag, true;
    if (bsize > 2 && b1[2] == 0) return b1[2] = fptag, true;
    if (bsize > 2 && b2[2] == 0) return b2[2] = fptag, true;
    if (bsize > 3 && b1[3] == 0) return b1[3] = fptag, true;
    if (bsize > 3 && b2[3] == 0) return b2[3] = fptag, true;
    return false;
}

static inline bool kickloop(uint32_t *bb,
	uint32_t fptag, uint32_t *b, uint32_t i,
	uint32_t *ofptag, uint32_t *oi,
	int logsize, uint32_t mask, int bsize)
{
    int maxkick = 2 * logsize;
    do {
	// Put at the top, kick out from the bottom.
	// Using *ofp as a temporary register.
	*ofptag = b[0];
	if (bsize > 1) b[0] = b[1];
	if (bsize > 2) b[1] = b[2];
	if (bsize > 3) b[2] = b[3];
	b[bsize-1] = fptag, fptag = *ofptag;
	// Ponder over the entry that's been kicked out.
	// Find out the alternative bucket.
	i ^= fptag;
	i &= mask;
	b = bb + bsize * i;
	if (insert1(fptag, b, bsize))
	    return true;
    } while (--maxkick >= 0);
    // Ran out of tries? ofptag already set.
    *oi = i;
    return false;
}

#define A8(p) __builtin_assume_aligned(p, 8)

static inline void reinterp23(uint32_t *bb, size_t nb)
{
    // Reinterpret as a 3-tier array.
    //
    //             2 3 . .   . . . .
    //   1 2 3 4   1 3 4 .   1 2 3 4
    //   1 2 3 4   1 2 4 .   1 2 3 4

    for (size_t i = nb - 2; i; i -= 2) {
	uint32_t *src0 = bb + 2 * i, *src1 = src0 + 2;
	uint32_t *dst0 = bb + 3 * i, *dst1 = dst0 + 3;
	memcpy(   dst1 , A8(src1), 8); dst1[2] = 0;
	memcpy(A8(dst0), A8(src0), 8); dst0[2] = 0;
    }
    bb[5] = 0, bb[4] = bb[3], bb[3] = bb[2], bb[2] = 0;
}

static inline void reinterp34(uint32_t *bb, size_t nb)
{
    // Reinterpret as a 4-tier array.
    //
    //             2 3 4 .   . . . .
    //   1 2 3 4   1 3 4 .   1 2 3 4
    //   1 2 3 4   1 2 4 .   1 2 3 4
    //   1 2 3 4   1 2 3 .   1 2 3 4

    for (size_t i = nb - 2; i; i -= 2) {
	uint32_t *src0 = bb + 3 * i, *src1 = src0 + 3;
	uint32_t *dst0 = bb + 4 * i, *dst1 = dst0 + 4;
	dst1[2] = src1[2]; memcpy(A8(dst1),    src1 , 8); dst1[3] = 0;
	dst0[2] = src0[2]; memcpy(A8(dst0), A8(src0), 8); dst0[3] = 0;
    }
    bb[7] = 0, bb[6] = bb[5], bb[5] = bb[4], bb[4] = bb[3], bb[3] = 0;
}

static inline bool stash(struct fp47set *set, uint32_t fptag, uint32_t i1,
	bool resized, int bsize)
{
    uint32_t i2 = i1 ^ fptag;
    i1 &= set->mask0;
    i2 &= set->mask0;
    i1 = (i2 < i1) ? i2 : i1;
    if (set->nstash == 0) {
	set->cnt--;
	set->nstash = 1;
	set->stash[0] = set->stash[2] = fptag;
	set->stash[1] = set->stash[3] = i1;
	setVFuncs(set, bsize, resized, 1);
	return true;
    }
    if (set->nstash == 1) {
	set->cnt--;
	set->nstash = 2;
	set->stash[2] = fptag;
	set->stash[3] = i1;
	setVFuncs(set, bsize, resized, 2);
    }
    return false;
}

// After the table gets resized, we try to reinsert the stashed elements.
static inline unsigned restash2(struct fp47set *set, int bsize, bool resized)
{
    unsigned k = 0;
    uint32_t *st = set->stash;
    for (unsigned j = 0; j < 2; j++) {
	uint32_t fptag = st[2*j+0];
	uint32_t i1 = st[2*j+1];
	uint32_t i2 = i1 ^ fptag;
	i1 &= set->mask0;
	i2 &= set->mask0;
	if (resized) {
	    Sort2(i1, i2);
	    i1 |= fptag << set->logsize0;
	    i2 = i1 ^ fptag;
	    i1 &= set->mask1;
	    i2 &= set->mask1;
	}
	uint32_t *b1 = set->bb + i1 * bsize;
	uint32_t *b2 = set->bb + i2 * bsize;
	if (insert2(fptag, b1, b2, bsize))
	    continue;
	if (kickloop(set->bb, fptag, b1, i1, &fptag, &i1, set->logsize1, set->mask1, bsize))
	    continue;
	st[2*k+0] = fptag;
	st[2*k+1] = i1;
	k++;
    }
    return k;
}

static inline int insert23tail(struct fp47set *set, uint32_t fptag, uint32_t i1, int bsize)
{
    bool resized = set->logsize1 > set->logsize0;
    if (stash(set, fptag, i1, resized, bsize))
	return 1;
    size_t nb = set->mask1 + (size_t) 1;
    uint32_t *bb = realloc(set->bb, (bsize + 1) * nb * sizeof(uint32_t));
    if (!bb) {
	set->cnt--;
	return -1;
    }
    if (bsize == 2) reinterp23(bb, nb);
    if (bsize == 3) reinterp34(bb, nb);
    set->bb = bb;
    set->bsize = bsize + 1;
    // Insert fptag at i1, no kicks required.
    uint32_t *b1 = bb + (bsize + 1) * i1;
    b1[bsize] = fptag;
    // Reinsert the stashed elements.
    set->cnt += set->nstash;
    set->nstash = restash2(set, bsize + 1, resized);
    set->cnt -= set->nstash;
    setVFuncs(set, bsize + 1, set, set->nstash);
    return 2;
}

HIDDEN FP47SET_FASTCALL int fp47set_insert2tail(struct fp47set *set, uint32_t fptag, uint32_t i1)
{ return insert23tail(set, fptag, i1, 2); }
HIDDEN FP47SET_FASTCALL int fp47set_insert3tail(struct fp47set *set, uint32_t fptag, uint32_t i1)
{ return insert23tail(set, fptag, i1, 3); }

HIDDEN FP47SET_FASTCALL int fp47set_insert4tail(struct fp47set *set, uint32_t fptag, uint32_t i1)
{
    return -1; // TODO
}

static inline int t_add(struct fp47set *set, uint64_t fp,
	int bsize, bool resized, int nstash)
{
    dFP2IB;
    set->cnt++; // strategical bump, may renege
    if (has(fptag, b1, b2, i1, i2, set->stash, nstash, resized, bsize))
	return 0;
    if (insert2(fptag, b1, b2, bsize))
	return 1;
    if (kickloop(set->bb, fptag, b1, i1, &fptag, &i1, set->logsize1, set->mask1, bsize))
	return 1;
    if (bsize == 2) return fp47set_insert2tail(set, fptag, i1);
    if (bsize == 3) return fp47set_insert3tail(set, fptag, i1);
    if (bsize == 4) return fp47set_insert4tail(set, fptag, i1);
    return -1; // cannot happen
}

#if FP47SET_MSFASTCALL
#define LOHI2FP lo | (uint64_t) hi << 32
#else
#define LOHI2FP fp
#endif

#undef MakeVFuncs
#define MakeVFuncs(BS, RE, ST) \
    static FP47SET_FASTCALL int fp47set_add##BS##re##RE##st##ST(FP47SET_pFP64, struct fp47set *set) \
    { return t_add(set, LOHI2FP, BS, RE, ST); } \
    static FP47SET_FASTCALL int fp47set_has##BS##re##RE##st##ST(FP47SET_pFP64, const struct fp47set *set) \
    { return t_has(set, LOHI2FP, BS, RE, ST); }
MakeAllVFuncs
