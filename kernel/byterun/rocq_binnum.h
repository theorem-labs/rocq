/************************************************************************/
/*         *      The Rocq Prover / The Rocq Development Team           */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

/* The routines of the BINNUM and BINNUMCALL instructions: C versions of
   functions on binary numbers, which kernel/vmbinnum.ml binds to the
   constants whose bodies are equal to its reference terms. */

#ifndef _ROCQ_BINNUM_
#define _ROCQ_BINNUM_

#include <stdint.h>
#include <stdlib.h>
#include <caml/mlvalues.h>
#include <caml/version.h>

/** Packed numbers.

    A positive number n with 2 <= n < 2^62 can be held as one block of tag
    BINNUM_PACKED_TAG (OCaml's Lazy_tag, 246, which the VM never uses) with
    one field, Val_long(n). The block stands for the chain of n: xI (a block
    of tag 1) if n is odd and xO (tag 2) if it is even, over the chain of
    n >> 1, which is xH (Val_int(0)) when n >> 1 = 1.

    Only the routines make packed blocks, as results that they compute
    whole. SWITCH (rocq_interp.c) and whd_val (vmvalues.ml, through
    rocq_binnum_expand) replace a packed block by the chain of its number
    before they read it, and the routines read it as its number. No other
    reader of a positive's structure exists (see the census of the readers
    in the report of slice 4 of the design).

    Packing exists only on 64-bit builds, where Val_long has 63 bits, with
    OCaml before 5.0, whose runtime scans a block of tag 246, size 1 and an
    immediate field as an ordinary block. The OCaml 5 runtime was not read.
    Elsewhere ROCQ_BINNUM_PACKING is 0, no packed block is ever made, and
    binnum_is_packed is always false. */
#if defined(ARCH_SIXTYFOUR) && OCAML_VERSION < 50000
#define ROCQ_BINNUM_PACKING 1
#else
#define ROCQ_BINNUM_PACKING 0
#endif

#define BINNUM_PACKED_TAG Lazy_tag
#define BINNUM_PACKED_LIMIT ((uint64_t)1 << 62)

static inline int binnum_is_packed(value v)
{
  return ROCQ_BINNUM_PACKING && Is_block(v) && Tag_val(v) == BINNUM_PACKED_TAG;
}

/* The number of the packed block v. The checks below hold for every block
   that a routine makes; if one fails, the block was not made by a routine,
   or was changed, and the process stops rather than compute with it. */
static inline uint64_t binnum_packed_number(value v)
{
  value f;
  uint64_t n;
  if (Wosize_val(v) != 1) abort();
  f = Field(v, 0);
  if (!Is_long(f)) abort();
  n = (uint64_t) Long_val(f);
  if (n < 2 || n >= BINNUM_PACKED_LIMIT) abort();
  return n;
}

/* The number of bits of n > 0. */
static inline unsigned binnum_bitlen(uint64_t n)
{
  return 64 - (unsigned) __builtin_clzll(n);
}

/* Field 0 of v, on the walk from an argument to the shared base of a
   result: v is a block that the routine read as a node of a Z or as a node
   of a positive's chain. A routine never puts a base below a packed block,
   so meeting one is a bug, and the process stops. */
static inline value binnum_base_step(value v)
{
  if (binnum_is_packed(v)) abort();
  return Field(v, 0);
}

/* Nonzero when ROCQ_VM_BINNUM_STATS is set: the routines, SWITCH and
   rocq_binnum_expand count only then. */
extern int rocq_binnum_stats;

/* Counts an expansion of a packed block into [nodes] chain nodes, by SWITCH
   ([where] = 0) or by rocq_binnum_expand ([where] = 1). */
void rocq_binnum_count_expansion(int where, uint64_t nodes);

/** Results.

    A value of the result, which the BINNUM and BINNUMCALL handlers
    (rocq_interp.c) allocate. A part is either an immediate, or a chain of
    [nnodes] fresh positive nodes (node i, from the outermost, is xI, a block
    of tag 1, if bit i is set, and xO, a block of tag 2, otherwise) over a
    base, possibly wrapped in one more block of one field and tag [wrap]
    (Zpos or Zneg). The bits are in [word] when [nnodes] is at most 64, and
    in the 32-bit limbs [bits] otherwise. The base is xH (BINNUM_BASE_XH), a
    fresh packed block of the number [base_num] (BINNUM_BASE_PACKED), or a
    subterm of an argument: argument [base_arg] after [base_depth] steps
    through field 0, every one of them through a block that the routine read
    as a node of a Z or of a chain. The routine keeps no pointer into the
    OCaml heap: the handler reads the base from the VM stack. */
enum { BINNUM_IMM, BINNUM_CHAIN };
enum { BINNUM_BASE_XH = -1, BINNUM_BASE_PACKED = -2 };

struct binnum_part {
  int kind;
  value imm;
  int wrap;
  uint64_t nnodes;
  uint64_t word;
  const uint32_t *bits;
  int base_arg;
  uint64_t base_depth;
  uint64_t base_num;
};

/* One part, or a pair (a block of tag 1 with the fields part[0], part[1]).
   With the statistics on, [words] is the number of nodes the routine read,
   [args] the positive arguments it started to read, and [args_packed] and
   [args_tail] those that were a packed block, and a chain over a packed
   tail. */
struct binnum_result {
  int nparts;
  uint64_t words;
  uint64_t args, args_packed, args_tail;
  struct binnum_part part[2];
};

/* Runs routine [k] on the [n] arguments [args[0..n-1]], at function entry
   ([site] = 0, BINNUM) or at a call site ([site] = 1, BINNUMCALL). If it
   accepts them, it returns the description of its result, valid until the
   next call; otherwise NULL. It allocates nothing in the OCaml heap. */
const struct binnum_result *rocq_binnum_run(int k, int n, const value *args, int site);

#endif /* _ROCQ_BINNUM_ */
