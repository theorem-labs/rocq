(* -proof-record-no-graph: a proof whose universe state has more levels than
   the pairwise check takes (130 named levels), so the registration records
   the digest of the whole global graph the state was made from, and keeps
   the graph. The edited tree adds a constraint between two universes the
   proof never queries, which its footprint allows: the rebuilt state's
   global graph differs from the recorded one, so the proof misses on
   universe_rebuild and runs its tactics, as stock does. *)
Universe a b.

Polymorphic Lemma wide@{u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19
  u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 u38 u39
  u40 u41 u42 u43 u44 u45 u46 u47 u48 u49 u50 u51 u52 u53 u54 u55 u56 u57 u58 u59
  u60 u61 u62 u63 u64 u65 u66 u67 u68 u69 u70 u71 u72 u73 u74 u75 u76 u77 u78 u79
  u80 u81 u82 u83 u84 u85 u86 u87 u88 u89 u90 u91 u92 u93 u94 u95 u96 u97 u98 u99
  u100 u101 u102 u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115
  u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127 u128 u129} :
  Type@{u0} -> Type@{u0}.
Proof. exact (fun x => x). Qed.
