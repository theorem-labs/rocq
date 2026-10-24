/************************************************************************/
/*         *      The Rocq Prover / The Rocq Development Team           */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

/* The routines of the BINNUM instruction: C versions of functions on binary
   numbers, which kernel/vmbinnum.ml binds to the constants whose bodies are
   equal to its reference terms. */

#ifndef _ROCQ_BINNUM_
#define _ROCQ_BINNUM_

#include <caml/mlvalues.h>

/* Runs routine [k] on the [n] arguments [args[0..n-1]]. If it accepts them,
   it stores the result in [*res] and returns 1. Otherwise it returns 0 and
   changes nothing. It allocates nothing and never calls the GC. */
int rocq_binnum_run(int k, int n, const value *args, value *res);

#endif /* _ROCQ_BINNUM_ */
