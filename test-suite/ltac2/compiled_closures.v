Require Import Ltac2.Ltac2.

(** The body of an Ltac2 function that is the value of a global, and of every function written
    inside it, is turned once into OCaml code ([Tac2interp], "Compiled bodies"), which runs when
    the function is applied to all its arguments at run time. Each test below gives the value the
    interpreter gives, for every construct in such a body: constructors, records, projections and
    open constructors built from calls; writes to mutable fields; matches on closed types, full
    matches with nested, alias and or-patterns, matches on open types; local recursive functions;
    closures made in the body, which capture the variables of each run; string literals, which are
    new strings at each evaluation; globals redefined between two runs; and partial applications
    of functions and primitives, passed to and applied by other functions. Effects keep their
    order, failures and backtracking their behaviour. *)

Ltac2 check (b : bool) := if b then () else Control.throw (Invalid_argument None).
Ltac2 check_int (n : int) (m : int) := check (Int.equal n m).
Ltac2 Type rr := { mutable c : int }.
Ltac2 log (r : rr) (d : int) := r.(c) := Int.add (Int.mul (r.(c)) 10) d.
Ltac2 logv (r : rr) (d : int) (v : int) := log r d; v.

(** Constructors, records and projections whose fields are computed, in order. *)
Ltac2 Type rec3 := { fa : int; fb : int; fc : int }.
Ltac2 mk3 (r : rr) := { fa := logv r 1 10; fb := logv r 2 20; fc := logv r 3 30 }.
Ltac2 sum3 (x : rec3) := Int.add (x.(fa)) (Int.add (x.(fb)) (x.(fc))).
Ltac2 build_and_sum (r : rr) := Int.add (sum3 (mk3 r)) ((mk3 r).(fc)).
Ltac2 Eval let r := { c := 0 } in check_int (build_and_sum r) 90; check_int (r.(c)) 123123.
Ltac2 tuple_of (r : rr) := (logv r 4 4, Some (logv r 5 5), [logv r 6 6; logv r 7 7]).
Ltac2 tuple_sum (r : rr) :=
  match tuple_of r with
  | (a, Some b, [c; d]) => Int.add a (Int.add b (Int.add c d))
  | _ => -1
  end.
Ltac2 Eval let r := { c := 0 } in check_int (tuple_sum r) 22; check_int (r.(c)) 4567.

(** Writes to mutable fields, from values that are computed, in order. *)
Ltac2 set_twice (r : rr) := r.(c) := logv r 1 5; r.(c) := Int.add (logv r 2 0) (r.(c)); r.(c).
Ltac2 Eval let r := { c := 3 } in check_int (set_twice r) 52.

(** Full matches: nested patterns, aliases, or-patterns, atoms, in a function body. *)
Ltac2 classify (x : int option * int list) :=
  match x with
  | (Some 0, _) => 0
  | (Some n, ([] | [_])) => Int.add 100 n
  | ((Some _ | None) as o, (a :: b :: _) as l) =>
    Int.add (match o with Some n => n | None => 7 end) (Int.add (Int.mul a 1000) (Int.add (Int.mul b 10) (List.length l)))
  | (None, _) => -1
  end.
Ltac2 classify_all () :=
  [classify (Some 0, [1]); classify (Some 4, []); classify (Some 5, [9]);
   classify (Some 3, [1; 2; 3]); classify (None, [4; 5]); classify (None, [])].
Ltac2 Eval
  match classify_all () with
  | [a; b; c; d; e; f] =>
    check_int a 0; check_int b 104; check_int c 105; check_int d 1026; check_int e 4059; check_int f -1
  | _ => check false
  end.
Ltac2 strmatch (s : string) := match s with "ab" => 1 | "c" => 2 | _ => 3 end.
Ltac2 Eval check_int (Int.add (strmatch "ab") (Int.add (Int.mul 10 (strmatch "c")) (Int.mul 100 (strmatch "x")))) 321.
Ltac2 or_outer (k : int) (x : int option * int) :=
  let base := Int.mul k 10 in
  match x with
  | ((Some _ | None) as o, m) =>
    let extra := Int.add m 1 in
    Int.add base (Int.add extra (match o with Some n => n | None => 0 end))
  end.
Ltac2 Eval check_int (Int.add (or_outer 2 (Some 5, 3)) (or_outer 1 (None, 0))) 40.

(** Matches on open types, with the default branch, in a function body. *)
Ltac2 Type exn ::= [ E1 | E2 (int) | E3 (int, int) ].
Ltac2 of_exn (e : exn) := match e with E2 n => n | E3 a b => Int.sub a b | E1 => 1000 | _ => -1 end.
Ltac2 exn_sum () := Int.add (of_exn (E2 5)) (Int.add (of_exn (E3 10 3)) (Int.add (of_exn E1) (of_exn Not_found))).
Ltac2 Eval check_int (exn_sum ()) 1011.
Ltac2 Type open_t := [ .. ].
Ltac2 Type open_t ::= [ K1 (int) ].
Ltac2 mk_k1 (r : rr) := K1 (logv r 8 8).
Ltac2 un_k1 (x : open_t) := match x with K1 n => n | _ => 0 end.
Ltac2 Eval let r := { c := 0 } in check_int (Int.add (un_k1 (mk_k1 r)) (un_k1 (mk_k1 r))) 16; check_int (r.(c)) 88.

(** Local recursive functions, made at each run of the body over that run's variables. *)
Ltac2 count_to (base : int) (n : int) :=
  let rec go i acc := if Int.equal i 0 then acc else go (Int.sub i 1) (Int.add acc base) in
  go n 0.
Ltac2 Eval check_int (Int.add (count_to 3 4) (count_to 100 2)) 212.
Ltac2 rec_in_loop () :=
  List.fold_left (fun acc k =>
    let rec pow n := if Int.equal n 0 then 1 else Int.mul k (pow (Int.sub n 1)) in
    Int.add acc (pow 3)) 0 [1; 2; 3].
Ltac2 Eval check_int (rec_in_loop ()) 36.

(** Closures made in a body capture the variables of their own run. *)
Ltac2 adders () := List.map (fun k => fun x => Int.add (Int.mul k 10) x) [1; 2; 3].
Ltac2 Eval check_int (List.fold_left (fun acc f => Int.add acc (f 1)) 0 (adders ())) 63.
Ltac2 counter () := let r := { c := 0 } in (fun () => r.(c) := Int.add (r.(c)) 1; r.(c)).
Ltac2 Eval
  let a := counter () in let b := counter () in
  let _ := a () in let _ := a () in check_int (a ()) 3; check_int (b ()) 1.

(** A string literal is a new string each time it is evaluated. *)
Ltac2 fresh_str () := "abc".
Ltac2 mutate_str () := let s := fresh_str () in String.set s 0 (String.get "x" 0); s.
Ltac2 Eval
  let s1 := mutate_str () in
  let s2 := fresh_str () in
  check (String.equal s1 "xbc"); check (String.equal s2 "abc").
Ltac2 lit_twice () := let f := fun () => "q" in let a := f () in String.set a 0 (String.get "z" 0); f ().
Ltac2 Eval check (String.equal (lit_twice ()) "q").

(** A global read in a body, redefined between two runs ([Ltac2 Set]), read directly and through
    a mutable global whose value calls the reader. *)
Ltac2 mutable mval () := 1.
Ltac2 read_mval () := Int.add (mval ()) 10.
Ltac2 Eval check_int (read_mval ()) 11.
Ltac2 mutable saved : unit -> int := fun () => 0.
Ltac2 Set saved := fun () => read_mval ().
Ltac2 Set mval := fun () => 2.
Ltac2 Eval check_int (read_mval ()) 12.
Ltac2 Eval check_int (saved ()) 12.
Ltac2 Set mval as old := fun () => Int.mul (old ()) 5.
Ltac2 Eval check_int (read_mval ()) 20.

(** A global whose value holds a block is computed at each use, also in a body: a write into the
    block of one use (through array_set, as in global_value_cache.v) is not seen by the next use. *)
Ltac2 @ external raw_set : 'a -> int -> 'b -> unit := "rocq-runtime.plugins.ltac2" "array_set".
Ltac2 global_pair := (0, 0).
Ltac2 write_then_read () := raw_set global_pair 0 1; fst global_pair.
Ltac2 Eval check_int (write_then_read ()) 0.
Ltac2 Eval check_int (write_then_read ()) 0.
Ltac2 read_pair () := global_pair.
Ltac2 Eval raw_set (read_pair ()) 0 1; check_int (fst (read_pair ())) 0.

(** Partial applications: of a function, applied later to the rest of its arguments by another
    function, in order; of a primitive; of a function to some arguments and then the rest one by
    one; over-application. *)
Ltac2 sub3 (a : int) (b : int) (c : int) := Int.sub a (Int.sub b c).
Ltac2 Eval check_int (List.fold_left (fun acc x => Int.add acc x) 0 (List.map (sub3 100 10) [1; 2; 3])) 276.
Ltac2 Eval check (List.exist (Int.equal 3) [1; 2; 3]).
Ltac2 Eval check_int (List.fold_left Int.add 0 (List.map (Int.mul 3) [1; 2; 3])) 18.
Ltac2 Eval let f := sub3 50 in let g := f 20 in check_int (g 5) 35.
Ltac2 apply2 (f : int -> int -> int) := f 7 3.
Ltac2 Eval check_int (apply2 (sub3 20)) 16.
Ltac2 log_sub (r : rr) (a : int) (b : int) := log r a; log r b; Int.sub a b.
Ltac2 Eval let r := { c := 0 } in
  check_int (List.fold_left Int.add 0 (List.map (log_sub r 9) [1; 2])) 15; check_int (r.(c)) 9192.
Ltac2 has_three (l : int list array) := Array.exist (List.exist (Int.equal 3)) l.
Ltac2 Eval check (has_three (Array.of_list [[1]; [2; 3]])).
Ltac2 Eval check (Bool.neg (has_three (Array.of_list [[1]; [2]]))).

(** Failures and backtracking through the constructs above. *)
Ltac2 two () := Control.plus (fun () => 1) (fun _ => 2).
Ltac2 pair_two (r : rr) := (logv r 1 0, two (), logv r 3 0).
Ltac2 Eval
  let r := { c := 0 } in
  check_int (Control.plus
    (fun () => match pair_two r with (_, 1, _) => Control.zero E1 | (_, n, _) => n end)
    (fun _ => 0)) 2;
  check_int (r.(c)) 133.
Ltac2 fail_mid (r : rr) := { fa := logv r 1 1; fb := Control.zero (E2 (logv r 2 7)); fc := logv r 3 3 }.
Ltac2 Eval
  let r := { c := 0 } in
  check_int (Control.plus (fun () => (fail_mid r).(fa)) (fun e => match e with E2 n => n | _ => 0 end)) 7;
  check_int (r.(c)) 12.
Ltac2 two_parts (r : rr) := let k := K1 (two ()) in log r 4; un_k1 k.
Ltac2 Eval
  let r := { c := 0 } in
  check_int (Control.plus (fun () => match two_parts r with 1 => Control.zero E1 | n => n end) (fun _ => 0)) 2;
  check_int (r.(c)) 44.

(** Terms built in a body from its variables (an extension node). *)
Ltac2 succ_term (n : constr) := let m := '(S $n) in '(S $m).
Ltac2 Eval check (Constr.equal (succ_term '0) '2).

(** Names bound again inside a body: compiled code reads a variable at its position among the
    binders around it, so each test below rebinds a name that is in scope. A let with several
    bindings evaluates every right-hand side before any of its names is bound; a later binding
    of a name shadows the earlier one in a let, in a function's parameters, in a case branch,
    in a pattern (with an alias, or with alternatives that bind in different orders), in a
    mutual recursive let, in a match on an open type whose pattern has an alias (a full match),
    and in the default branch of a match on an open type. *)
Ltac2 simul (a : int) := let a := 10 with b := a in Int.add (Int.mul 100 a) b.
Ltac2 Eval check_int (simul 1) 1001.
Ltac2 shadow (x : int) :=
  let y := x with x := Int.add x 1 in
  let f := fun x => Int.add x y in
  match (x, y) with (y, x) => Int.add (Int.mul 100 (f y)) x end.
Ltac2 Eval check_int (shadow 1) 301.
Ltac2 case_shadow (x : int option) := let v := 100 in match x with Some v => Int.add v 1 | None => v end.
Ltac2 Eval check_int (Int.add (case_shadow (Some 5)) (case_shadow None)) 106.
Ltac2 orswap (p : int option * int option) :=
  match p with
  | (Some a, b) | (b, Some a) => (fun () => Int.add a (match b with Some n => Int.mul 10 n | None => 0 end)) ()
  | _ => -1
  end.
Ltac2 Eval check_int (Int.add (Int.mul 100 (orswap (Some 1, Some 2))) (orswap (None, Some 3))) 2103.
Ltac2 alias3 (x : (int * int) * int) :=
  let a := 7 in
  match x with ((a, b) as p, c) => Int.add (Int.mul 100 (fst p)) (Int.add (Int.mul 10 b) (Int.add a c)) end.
Ltac2 Eval check_int (alias3 ((1, 2), 3)) 124.
Ltac2 mutual (n : int) :=
  let k := 3 in
  let rec ev m := if Int.equal m 0 then k else od (Int.sub m 1)
  with od k := if Int.equal k 0 then -1 else ev (Int.sub k 1) in
  Int.add (Int.mul 100 (ev n)) (od n).
Ltac2 Eval check_int (mutual 4) 299.
Ltac2 of_exn_self (e : exn) :=
  let n := 7 in
  match e with E2 n as e2 => Int.add n (of_exn e2) | e3 => Int.add n (of_exn e3) end.
Ltac2 Eval check_int (Int.add (of_exn_self (E2 5)) (of_exn_self E1)) 1017.
Ltac2 of_exn_def (e : exn) :=
  let n := 7 in
  match e with E2 n => Int.add n 100 | e3 => Int.add n (of_exn e3) end.
Ltac2 Eval check_int (Int.add (of_exn_def (E2 5)) (of_exn_def E1)) 1112.

(** A body deeper than the compiler's depth limit (256 nested compiles): past the limit the
    code runs through the interpreter's run-time path, reading the variables that compiled code
    bound, and the compiled code after it continues in its own environment. *)
Ltac2 deep (x : int) :=
  let v1 := Int.add x 1 in let v2 := Int.add v1 1 in let v3 := Int.add v2 1 in let v4 := Int.add v3 1 in
  let v5 := Int.add v4 1 in let v6 := Int.add v5 1 in let v7 := Int.add v6 1 in let v8 := Int.add v7 1 in
  let v9 := Int.add v8 1 in let v10 := Int.add v9 1 in let v11 := Int.add v10 1 in
  let v12 := Int.add v11 1 in let v13 := Int.add v12 1 in let v14 := Int.add v13 1 in
  let v15 := Int.add v14 1 in let v16 := Int.add v15 1 in let v17 := Int.add v16 1 in
  let v18 := Int.add v17 1 in let v19 := Int.add v18 1 in let v20 := Int.add v19 1 in
  let v21 := Int.add v20 1 in let v22 := Int.add v21 1 in let v23 := Int.add v22 1 in
  let v24 := Int.add v23 1 in let v25 := Int.add v24 1 in let v26 := Int.add v25 1 in
  let v27 := Int.add v26 1 in let v28 := Int.add v27 1 in let v29 := Int.add v28 1 in
  let v30 := Int.add v29 1 in let v31 := Int.add v30 1 in let v32 := Int.add v31 1 in
  let v33 := Int.add v32 1 in let v34 := Int.add v33 1 in let v35 := Int.add v34 1 in
  let v36 := Int.add v35 1 in let v37 := Int.add v36 1 in let v38 := Int.add v37 1 in
  let v39 := Int.add v38 1 in let v40 := Int.add v39 1 in let v41 := Int.add v40 1 in
  let v42 := Int.add v41 1 in let v43 := Int.add v42 1 in let v44 := Int.add v43 1 in
  let v45 := Int.add v44 1 in let v46 := Int.add v45 1 in let v47 := Int.add v46 1 in
  let v48 := Int.add v47 1 in let v49 := Int.add v48 1 in let v50 := Int.add v49 1 in
  let v51 := Int.add v50 1 in let v52 := Int.add v51 1 in let v53 := Int.add v52 1 in
  let v54 := Int.add v53 1 in let v55 := Int.add v54 1 in let v56 := Int.add v55 1 in
  let v57 := Int.add v56 1 in let v58 := Int.add v57 1 in let v59 := Int.add v58 1 in
  let v60 := Int.add v59 1 in let v61 := Int.add v60 1 in let v62 := Int.add v61 1 in
  let v63 := Int.add v62 1 in let v64 := Int.add v63 1 in let v65 := Int.add v64 1 in
  let v66 := Int.add v65 1 in let v67 := Int.add v66 1 in let v68 := Int.add v67 1 in
  let v69 := Int.add v68 1 in let v70 := Int.add v69 1 in let v71 := Int.add v70 1 in
  let v72 := Int.add v71 1 in let v73 := Int.add v72 1 in let v74 := Int.add v73 1 in
  let v75 := Int.add v74 1 in let v76 := Int.add v75 1 in let v77 := Int.add v76 1 in
  let v78 := Int.add v77 1 in let v79 := Int.add v78 1 in let v80 := Int.add v79 1 in
  let v81 := Int.add v80 1 in let v82 := Int.add v81 1 in let v83 := Int.add v82 1 in
  let v84 := Int.add v83 1 in let v85 := Int.add v84 1 in let v86 := Int.add v85 1 in
  let v87 := Int.add v86 1 in let v88 := Int.add v87 1 in let v89 := Int.add v88 1 in
  let v90 := Int.add v89 1 in let v91 := Int.add v90 1 in let v92 := Int.add v91 1 in
  let v93 := Int.add v92 1 in let v94 := Int.add v93 1 in let v95 := Int.add v94 1 in
  let v96 := Int.add v95 1 in let v97 := Int.add v96 1 in let v98 := Int.add v97 1 in
  let v99 := Int.add v98 1 in let v100 := Int.add v99 1 in let v101 := Int.add v100 1 in
  let v102 := Int.add v101 1 in let v103 := Int.add v102 1 in let v104 := Int.add v103 1 in
  let v105 := Int.add v104 1 in let v106 := Int.add v105 1 in let v107 := Int.add v106 1 in
  let v108 := Int.add v107 1 in let v109 := Int.add v108 1 in let v110 := Int.add v109 1 in
  let v111 := Int.add v110 1 in let v112 := Int.add v111 1 in let v113 := Int.add v112 1 in
  let v114 := Int.add v113 1 in let v115 := Int.add v114 1 in let v116 := Int.add v115 1 in
  let v117 := Int.add v116 1 in let v118 := Int.add v117 1 in let v119 := Int.add v118 1 in
  let v120 := Int.add v119 1 in let v121 := Int.add v120 1 in let v122 := Int.add v121 1 in
  let v123 := Int.add v122 1 in let v124 := Int.add v123 1 in let v125 := Int.add v124 1 in
  let v126 := Int.add v125 1 in let v127 := Int.add v126 1 in let v128 := Int.add v127 1 in
  let v129 := Int.add v128 1 in let v130 := Int.add v129 1 in let v131 := Int.add v130 1 in
  let v132 := Int.add v131 1 in let v133 := Int.add v132 1 in let v134 := Int.add v133 1 in
  let v135 := Int.add v134 1 in let v136 := Int.add v135 1 in let v137 := Int.add v136 1 in
  let v138 := Int.add v137 1 in let v139 := Int.add v138 1 in let v140 := Int.add v139 1 in
  let v141 := Int.add v140 1 in let v142 := Int.add v141 1 in let v143 := Int.add v142 1 in
  let v144 := Int.add v143 1 in let v145 := Int.add v144 1 in let v146 := Int.add v145 1 in
  let v147 := Int.add v146 1 in let v148 := Int.add v147 1 in let v149 := Int.add v148 1 in
  let v150 := Int.add v149 1 in let v151 := Int.add v150 1 in let v152 := Int.add v151 1 in
  let v153 := Int.add v152 1 in let v154 := Int.add v153 1 in let v155 := Int.add v154 1 in
  let v156 := Int.add v155 1 in let v157 := Int.add v156 1 in let v158 := Int.add v157 1 in
  let v159 := Int.add v158 1 in let v160 := Int.add v159 1 in let v161 := Int.add v160 1 in
  let v162 := Int.add v161 1 in let v163 := Int.add v162 1 in let v164 := Int.add v163 1 in
  let v165 := Int.add v164 1 in let v166 := Int.add v165 1 in let v167 := Int.add v166 1 in
  let v168 := Int.add v167 1 in let v169 := Int.add v168 1 in let v170 := Int.add v169 1 in
  let v171 := Int.add v170 1 in let v172 := Int.add v171 1 in let v173 := Int.add v172 1 in
  let v174 := Int.add v173 1 in let v175 := Int.add v174 1 in let v176 := Int.add v175 1 in
  let v177 := Int.add v176 1 in let v178 := Int.add v177 1 in let v179 := Int.add v178 1 in
  let v180 := Int.add v179 1 in let v181 := Int.add v180 1 in let v182 := Int.add v181 1 in
  let v183 := Int.add v182 1 in let v184 := Int.add v183 1 in let v185 := Int.add v184 1 in
  let v186 := Int.add v185 1 in let v187 := Int.add v186 1 in let v188 := Int.add v187 1 in
  let v189 := Int.add v188 1 in let v190 := Int.add v189 1 in let v191 := Int.add v190 1 in
  let v192 := Int.add v191 1 in let v193 := Int.add v192 1 in let v194 := Int.add v193 1 in
  let v195 := Int.add v194 1 in let v196 := Int.add v195 1 in let v197 := Int.add v196 1 in
  let v198 := Int.add v197 1 in let v199 := Int.add v198 1 in let v200 := Int.add v199 1 in
  let v201 := Int.add v200 1 in let v202 := Int.add v201 1 in let v203 := Int.add v202 1 in
  let v204 := Int.add v203 1 in let v205 := Int.add v204 1 in let v206 := Int.add v205 1 in
  let v207 := Int.add v206 1 in let v208 := Int.add v207 1 in let v209 := Int.add v208 1 in
  let v210 := Int.add v209 1 in let v211 := Int.add v210 1 in let v212 := Int.add v211 1 in
  let v213 := Int.add v212 1 in let v214 := Int.add v213 1 in let v215 := Int.add v214 1 in
  let v216 := Int.add v215 1 in let v217 := Int.add v216 1 in let v218 := Int.add v217 1 in
  let v219 := Int.add v218 1 in let v220 := Int.add v219 1 in let v221 := Int.add v220 1 in
  let v222 := Int.add v221 1 in let v223 := Int.add v222 1 in let v224 := Int.add v223 1 in
  let v225 := Int.add v224 1 in let v226 := Int.add v225 1 in let v227 := Int.add v226 1 in
  let v228 := Int.add v227 1 in let v229 := Int.add v228 1 in let v230 := Int.add v229 1 in
  let v231 := Int.add v230 1 in let v232 := Int.add v231 1 in let v233 := Int.add v232 1 in
  let v234 := Int.add v233 1 in let v235 := Int.add v234 1 in let v236 := Int.add v235 1 in
  let v237 := Int.add v236 1 in let v238 := Int.add v237 1 in let v239 := Int.add v238 1 in
  let v240 := Int.add v239 1 in let v241 := Int.add v240 1 in let v242 := Int.add v241 1 in
  let v243 := Int.add v242 1 in let v244 := Int.add v243 1 in let v245 := Int.add v244 1 in
  let v246 := Int.add v245 1 in let v247 := Int.add v246 1 in let v248 := Int.add v247 1 in
  let v249 := Int.add v248 1 in let v250 := Int.add v249 1 in let v251 := Int.add v250 1 in
  let v252 := Int.add v251 1 in let v253 := Int.add v252 1 in let v254 := Int.add v253 1 in
  let v255 := Int.add v254 1 in let v256 := Int.add v255 1 in let v257 := Int.add v256 1 in
  let v258 := Int.add v257 1 in let v259 := Int.add v258 1 in let v260 := Int.add v259 1 in
  let v261 := Int.add v260 1 in let v262 := Int.add v261 1 in let v263 := Int.add v262 1 in
  let v264 := Int.add v263 1 in let v265 := Int.add v264 1 in let v266 := Int.add v265 1 in
  let v267 := Int.add v266 1 in let v268 := Int.add v267 1 in let v269 := Int.add v268 1 in
  let v270 := Int.add v269 1 in let v271 := Int.add v270 1 in let v272 := Int.add v271 1 in
  let v273 := Int.add v272 1 in let v274 := Int.add v273 1 in let v275 := Int.add v274 1 in
  let v276 := Int.add v275 1 in let v277 := Int.add v276 1 in let v278 := Int.add v277 1 in
  let v279 := Int.add v278 1 in let v280 := Int.add v279 1 in let v281 := Int.add v280 1 in
  let v282 := Int.add v281 1 in let v283 := Int.add v282 1 in let v284 := Int.add v283 1 in
  let v285 := Int.add v284 1 in let v286 := Int.add v285 1 in let v287 := Int.add v286 1 in
  let v288 := Int.add v287 1 in let v289 := Int.add v288 1 in let v290 := Int.add v289 1 in
  let v291 := Int.add v290 1 in let v292 := Int.add v291 1 in let v293 := Int.add v292 1 in
  let v294 := Int.add v293 1 in let v295 := Int.add v294 1 in let v296 := Int.add v295 1 in
  let v297 := Int.add v296 1 in let v298 := Int.add v297 1 in let v299 := Int.add v298 1 in
  let v300 := Int.add v299 1 in
  let f := fun y => Int.add y x in f v300.
Ltac2 Eval check_int (deep 1) 302.

(** An application whose head is not simple (a match that gives a partial application of a
    primitive). *)
Ltac2 pick (b : bool) (x : int) := (if b then Int.add x else Int.sub x) 3.
Ltac2 Eval check_int (Int.add (Int.mul 100 (pick true 10)) (pick false 10)) 1307.

(** More bindings in scope than the interpreter's environment keeps in its chain (16), read by
    compiled code and by a term built from them (an extension node), with and without backtraces. *)
Ltac2 many (n : constr) :=
  let a1 := n in let a2 := 2 in let a3 := 3 in let a4 := 4 in let a5 := 5 in let a6 := 6 in
  let a7 := 7 in let a8 := 8 in let a9 := 9 in let a10 := 10 in let a11 := 11 in let a12 := 12 in
  let a13 := 13 in let a14 := 14 in let a15 := 15 in let a16 := 16 in let a17 := 17 in let a18 := 18 in
  let t := '(S $a1) in
  Int.add (Int.add a18 a2) (match Constr.Unsafe.kind t with Constr.Unsafe.App _ _ => 1 | _ => 0 end).
Ltac2 Eval check_int (many '0) 21.
Set Ltac2 Backtrace.
Ltac2 Eval check_int (many '0) 21.
Unset Ltac2 Backtrace.

(** A partial application of a primitive that reads the proof state, applied by another
    function. *)
Ltac2 Eval check (List.for_all (Constr.Relevance.equal Constr.Relevance.relevant)
                   [Constr.Relevance.relevant; Constr.Relevance.relevant]).
Ltac2 Eval check (Bool.neg (List.exist (Constr.Relevance.equal Constr.Relevance.relevant)
                   [Constr.Relevance.irrelevant])).

(** One tactic built once and run in each goal ([Control.enter]): a compiled body that reads
    the goal runs once per goal, in goal order. *)
Ltac2 goal_args () := match Constr.Unsafe.kind (Control.goal ()) with
                      | Constr.Unsafe.App _ args => Array.length args
                      | _ => 0
                      end.
Ltac2 note (r : rr) := log r (Int.add (goal_args ()) 1).
Goal True /\ 2 = 2.
Proof.
  split.
  all: let r := { c := 0 } in Control.enter (fun () => note r); check_int (r.(c)) 14.
  - exact I.
  - reflexivity.
Qed.

(** With backtraces or Ltac2-in-Ltac1 profiling on, the general path runs; the values are the
    same. *)
Set Ltac2 Backtrace.
Ltac2 Eval let r := { c := 0 } in check_int (build_and_sum r) 90; check_int (r.(c)) 123123.
Ltac2 Eval check_int (rec_in_loop ()) 36.
Ltac2 Eval check_int (apply2 (sub3 20)) 16.
Unset Ltac2 Backtrace.
Set Ltac2 In Ltac1 Profiling.
Ltac2 Eval check_int (exn_sum ()) 1011.
Ltac2 Eval check_int (List.fold_left Int.add 0 (List.map (Int.mul 3) [1; 2; 3])) 18.
Unset Ltac2 In Ltac1 Profiling.
