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
#include <caml/mlvalues.h>

/* A value of the result, which the BINNUM and BINNUMCALL handlers
   (rocq_interp.c) allocate. A part is either an immediate, or a chain of
   [nnodes] fresh positive nodes (node i, from the outermost, is xI, a block
   of tag 1, if bit i is set, and xO, a block of tag 2, otherwise) over a
   base, possibly wrapped in one more block of one field and tag [wrap] (Zpos
   or Zneg). The bits are in [word] when [nnodes] is at most 64, and in the
   32-bit limbs [bits] otherwise. The base is xH, or a subterm of an
   argument: argument [base_arg] after [base_depth] steps through field 0,
   every one of them through a block that the routine read. The routine
   keeps no pointer into the OCaml heap: the handler reads the base from the
   VM stack. */
enum { BINNUM_IMM, BINNUM_CHAIN };

struct binnum_part {
  int kind;
  value imm;
  int wrap;
  uint64_t nnodes;
  uint64_t word;
  const uint32_t *bits;
  int base_arg;
  uint64_t base_depth;
};

/* One part, or a pair (a block of tag 1 with the fields part[0], part[1]).
   [words] is the number of nodes the routine read. */
struct binnum_result {
  int nparts;
  uint64_t words;
  struct binnum_part part[2];
};

/* Runs routine [k] on the [n] arguments [args[0..n-1]], at function entry
   ([site] = 0, BINNUM) or at a call site ([site] = 1, BINNUMCALL). If it
   accepts them, it returns the description of its result, valid until the
   next call; otherwise NULL. It allocates nothing in the OCaml heap. */
const struct binnum_result *rocq_binnum_run(int k, int n, const value *args, int site);

#endif /* _ROCQ_BINNUM_ */
