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
    BINNUM_PACKED_TAG (OCaml's Lazy_tag, 246, which the VM never uses),
    whose field 0 is Val_long(n). The block stands for the chain of n: xI
    (a block of tag 1) if n is odd and xO (tag 2) if it is even, over the
    chain of n >> 1, which is xH (Val_int(0)) when n >> 1 = 1.

    A block of size 1 is a result that a routine computed whole. A block of
    size 2 is a literal: a chain in the VM value of a structured constant
    [Const_val] (Vmvalues.val_of_str_const, through
    rocq_binnum_pack_literal; the other kinds of structured constant, such
    as universe instances, hold OCaml data and are never packed). Its field
    1 is the chain itself, which the structured constant keeps alive, so a
    reader of the chain takes it rather than building it.

    The same block stands for a Z, an N or a nat as well, because their
    constructors have the same tags: Zpos, Npos and S are the blocks of tag
    1 with one field, Zneg the block of tag 2, and Z0, N0 and O are
    Val_int(0). A reader of an N or of a nat refuses tag 2 (cur_node_nat,
    rocq_binnum.c).

    The routines, the packing of literals and the peel in PROJ (a size-1
    block of the rest of a number, rocq_interp.c) make packed blocks.
    SWITCH and PROJ (rocq_interp.c) and whd_val (vmvalues.ml, through
    rocq_binnum_expand) replace a packed block by its chain before they read
    it: field 1 when the block has one, a fresh chain otherwise. The
    routines read it as its number. No other code reads the structure of
    such a value: PUSHFIELDS and GETFIELD follow their own SWITCH, Kfield
    and SETFIELD act on cofix accumulators and on nested blocks of size 2,
    and the OCaml side reads a value only through whd_val. The tests
    test-suite/misc/rocqchk_binnum_packed.sh and rocqchk_binnum_literal.sh
    check the readers on packed results and on packed literals.

    Packing exists only on 64-bit builds, where Val_long has 63 bits, with
    OCaml before 5.0, whose runtime copies and scans a block of tag 246 as
    an ordinary block of its size: in OCaml 4.14, minor_gc.c oldify_one and
    major_gc.c mark_slice treat Closure_tag, Infix_tag, Forward_tag and the
    no-scan tags apart, and name Lazy_tag only as the target of a
    Forward_tag block, which the VM never makes. The OCaml 5 runtime was not
    read. Elsewhere ROCQ_BINNUM_PACKING is 0, no packed block is ever made,
    and binnum_is_packed is always false. */
#if defined(ARCH_SIXTYFOUR) && OCAML_VERSION < 50000
#define ROCQ_BINNUM_PACKING 1
#else
#define ROCQ_BINNUM_PACKING 0
#endif

#define BINNUM_PACKED_TAG Lazy_tag
#define BINNUM_PACKED_LIMIT ((uint64_t)1 << 62)

/* The tag of the node of bit [i] of [n]: xI (tag 1) where the bit is set,
   xO (tag 2) where it is clear. Every expansion of a packed number, and the
   check of a literal at packing time, use this one expression. */
#define BINNUM_NODE_TAG(n, i) ((((n) >> (i)) & 1) ? 1 : 2)

static inline int binnum_is_packed(value v)
{
  return ROCQ_BINNUM_PACKING && Is_block(v) && Tag_val(v) == BINNUM_PACKED_TAG;
}

/* The number of the packed block v. The checks below hold for every block
   that a routine or the packing of a literal makes; if one fails, the block
   was not made by them, or was changed, and the process stops rather than
   compute with it. */
static inline uint64_t binnum_packed_number(value v)
{
  value f;
  uint64_t n;
  mlsize_t size = Wosize_val(v);
  if (size != 1 && size != 2) abort();
  f = Field(v, 0);
  if (!Is_long(f)) abort();
  n = (uint64_t) Long_val(f);
  if (n < 2 || n >= BINNUM_PACKED_LIMIT) abort();
  if (size == 2) {
    value c = Field(v, 1);
    if (!Is_block(c) || Wosize_val(c) != 1 || Tag_val(c) != BINNUM_NODE_TAG(n, 0))
      abort();
  }
  return n;
}

/* The chain of the packed block v, or 0 when it keeps none (a result of a
   routine, of size 1). The caller has checked the block with
   binnum_packed_number. */
static inline value binnum_packed_chain(value v)
{
  return Wosize_val(v) == 2 ? Field(v, 1) : (value) 0;
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
   ([where] = 0), by rocq_binnum_expand ([where] = 1) or by PROJ ([where] =
   2). Any other [where] stops the process. */
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
