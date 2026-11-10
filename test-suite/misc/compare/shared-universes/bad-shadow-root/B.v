(* The forgery one step further: the answer's own directory is bound to a
   root the IMAGE already serves (vendor-root), so a name the challenge
   reads from the image is looked up in the answer's directory first.
   Whatever a config said, the two sides could then read different files
   under one library name.

   This answer Requires nothing from that directory, and still the run is
   refused: the binding itself is what no config can make safe, and a check
   that waited for a library to be loaded from it would be checking the
   answer's restraint rather than the run's shape. *)

Require Img.Third.

Definition unused := Img.Third.Yet.
