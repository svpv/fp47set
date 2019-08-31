// Copyright (c) 2018, 2019 Alexey Tourbin
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

#define FUNC(name)  \
	.global    NAME(name); \
	.hidden    NAME(name); \
	.type      NAME(name),@function; \
	.align     32; \
	NAME(name):

#define ENDF(name) \
	.size      NAME(name),.-NAME(name)

#if defined(__i386__) || defined(__ILP32__)
#define m_stash    0
#define m_bb       24
#define m_mask0    36
#define m_mask1    40
#else
#define m_stash    0
#define m_bb       32
#define m_mask0    52
#define m_mask1    56
#endif

#if defined(__i386__)
#if defined(_WIN32) || defined(__CYGWIN__)
#define MSFASTCALL 1
#define REGPARM3   0
#else
#define MSFASTCALL 0
#define REGPARM3   1
#endif
#define MS64ABI    0
#else // x86_64
#if defined(_WIN32) || defined(__CYGWIN__)
#define MS64ABI    1
#else
#define MS64ABI    0
#endif
#define MSFASTCALL 0
#define REGPARM3   0
#endif

#if MSFASTCALL
#define r_lo       %ecx
#define r_hi       %edx
#define r_ptr      %eax
#endif

#if REGPARM3
#define r_lo       %eax
#define r_hi       %edx
#define r_ptr      %ecx
#endif

#ifdef __i386__
#define e_lo       r_lo
#define e_hi       r_hi

#elif MS64ABI
#define q_fp       %rcx
#define r_ptr      %rdx
#define q_lo       %rcx
#define r_lo       %rcx
#define q_hi       %r11
#define r_hi       %r11

#else // System V ABI
#define q_fp       %rdi
#define q_lo       %rdi
#define q_hi       %r11
#define e_lo       %edi
#define e_hi       %r11d

#ifdef __ILP32__
#define r_ptr      %esi
#define r_lo       %edi
#define r_hi       %r11d
#else
#define r_ptr      %rsi
#define r_lo       %rdi
#define r_hi       %r11
#endif

#endif // System V ABI

#define e_i1       e_lo
#define r_i1       r_lo
#define e_i2       e_hi
#define r_i2       r_hi

.macro hasBegin_re0st0
    #ifndef __i386__
	mov      q_fp,q_hi
	shr      $32,q_hi
    #endif
	add      $1,e_hi
	adc      e_lo,e_hi
	adc      $0,e_hi
	movd     e_hi,%xmm0
	xor      e_lo,e_hi
	pshufd   $0,%xmm0,%xmm0
	and      m_mask0(r_ptr),e_i1
	and      m_mask0(r_ptr),e_i2
	mov      m_bb(r_ptr),r_ptr
.endm

.macro hasRet_re0st0
	ret
.endm

.macro hasBegin_re0st1
    #ifndef __i386__
	mov      q_fp,q_hi
	shr      $32,q_hi
    #endif
	add      $1,e_hi
	adc      e_lo,e_hi
	adc      $0,e_hi
	cmp      0+m_stash(r_ptr),e_hi
	je       91f
	movd     e_hi,%xmm0
	xor      e_lo,e_hi
	and      m_mask0(r_ptr),e_i1
	and      m_mask0(r_ptr),e_i2
    90:
	pshufd   $0,%xmm0,%xmm0
	mov      m_bb(r_ptr),r_ptr
.endm

.macro hasRet_re0st1
	ret
    91:
	movd     e_hi,%xmm0
	xor      e_lo,e_hi
	and      m_mask0(r_ptr),e_i1
	and      m_mask0(r_ptr),e_i2
	cmp      4+m_stash(r_ptr),e_i1
	je       99f
	cmp      4+m_stash(r_ptr),e_i2
	jne      90b
    99:
	mov      $1,%eax
	ret
.endm

.macro hasBegin_re0st2
    #ifndef __i386__
	mov      q_fp,q_hi
	shr      $32,q_hi
    #endif
	add      $1,e_hi
	adc      e_lo,e_hi
	adc      $0,e_hi
	movd     e_hi,%xmm0
	cmp      0+m_stash(r_ptr),e_hi
	je       93f
    90:
	cmp      8+m_stash(r_ptr),e_hi
	je       95f
    91:
	xor      e_lo,e_hi
	and      m_mask0(r_ptr),e_i1
	and      m_mask0(r_ptr),e_i2
    92:
	pshufd   $0,%xmm0,%xmm0
	mov      m_bb(r_ptr),r_ptr
.endm

.macro hasRet_re0st2
	ret
    93:
	xor      e_lo,e_hi
	and      m_mask0(r_ptr),e_i1
	and      m_mask0(r_ptr),e_i2
	cmp      4+m_stash(r_ptr),e_i1
	je       99f
	cmp      4+m_stash(r_ptr),e_i2
	je       99f
	movd     %xmm0,e_hi
	cmp      8+m_stash(r_ptr),e_hi
	jne      94f
	xor      e_lo,e_hi
	and      m_mask0(r_ptr),e_i2
	cmp      12+m_stash(r_ptr),e_i1
	je       99f
	cmp      12+m_stash(r_ptr),e_i2
	je       99f
	jmp      92b
    94:
	xor      e_lo,e_hi
	and      m_mask0(r_ptr),e_i2
	jmp      92b
    95:
	xor      e_lo,e_hi
	and      m_mask0(r_ptr),e_i1
	and      m_mask0(r_ptr),e_i2
	cmp      12+m_stash(r_ptr),e_i1
	je       99f
	cmp      12+m_stash(r_ptr),e_i2
	jne      90b
    99:
	mov      $1,%eax
	ret
.endm

.macro hasBody2
	movq     (r_ptr,r_i1,8),%xmm1
	movq     (r_ptr,r_i2,8),%xmm2
	punpcklqdq %xmm2,%xmm1
	pcmpeqd  %xmm0,%xmm1
	pmovmskb %xmm1,%eax
.endm

.macro hasBody3
	shl      $2,r_i1
	shl      $2,r_i2
	movdqu   (r_ptr,r_i1,2),%xmm1
	movdqu   (r_ptr,r_i2,2),%xmm2
	pcmpeqd  %xmm0,%xmm1
	pcmpeqd  %xmm0,%xmm2
	packssdw %xmm2,%xmm1
	pmovmskb %xmm1,%eax
	and      $0x3f3f,%eax
.endm

.macro hasBody4
	shl      $4,r_i1
	shl      $4,r_i2
	movdqa   (r_ptr,r_i1,1),%xmm1
	pcmpeqd  %xmm0,%xmm1
	pcmpeqd  (r_ptr,r_i2,1),%xmm0
	packssdw %xmm0,%xmm1
	pmovmskb %xmm1,%eax
.endm

#define NAME(name) fp47set_##name##sse2

FUNC(has2re0st0)
	hasBegin_re0st0
	hasBody2
	hasRet_re0st0
ENDF(has2re0st0)

FUNC(has2re0st1)
	hasBegin_re0st1
	hasBody2
	hasRet_re0st1
ENDF(has2re0st1)

FUNC(has2re0st2)
	hasBegin_re0st2
	hasBody2
	hasRet_re0st2
ENDF(has2re0st2)

FUNC(has3re0st0)
	hasBegin_re0st0
	hasBody3
	hasRet_re0st0
ENDF(has3re0st0)

FUNC(has3re0st1)
	hasBegin_re0st1
	hasBody3
	hasRet_re0st1
ENDF(has3re0st1)

FUNC(has3re0st2)
	hasBegin_re0st2
	hasBody3
	hasRet_re0st2
ENDF(has3re0st2)

FUNC(has4re0st0)
	hasBegin_re0st0
	hasBody4
	hasRet_re0st0
ENDF(has3re0st0)

FUNC(has4re0st1)
	hasBegin_re0st1
	hasBody4
	hasRet_re0st1
ENDF(has3re0st1)

FUNC(has4re0st2)
	hasBegin_re0st2
	hasBody4
	hasRet_re0st2
ENDF(has3re0st2)
