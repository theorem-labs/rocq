/***********************************************************************/
/*                                                                     */
/*                          Rocq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/


#ifndef _ROCQ_FIX_CODE_
#define _ROCQ_FIX_CODE_

#include <caml/mlvalues.h>

/* Scratch instrumentation (bytecode-VM lane profile, never shipped): -DROCQ_OPCOUNT builds the
   interpreter switch-based, and it counts every dispatch by (previous opcode, opcode). */
#ifdef ROCQ_OPCOUNT
#undef THREADED_CODE
#endif
void * rocq_stat_alloc (asize_t sz);

#ifdef THREADED_CODE
void rocq_init_thread_code(void ** instr_table, void * instr_base);
#endif /*  THREADED_CODE */

extern code_t accumulate;

int rocq_is_instruction(opcode_t, opcode_t);
value rocq_tcode_of_code(value code);
value rocq_accumulate(value);
value rocq_makeaccu (value i);
value rocq_pushpop (value i);
value rocq_accucond (value i);

#endif /* _ROCQ_FIX_CODE_ */
