(* Test improved error messages for module type errors *)

(* Test 1: NotConvertibleInductiveField - types given to inductive differ *)
Module Type IndType1.
  Inductive I : Type := c : nat -> I.
End IndType1.
Module IndMod1.
  Inductive I : Type := c : bool -> I.
End IndMod1.
Fail Module IndTest1 : IndType1 := IndMod1.

(* Test 2: NotConvertibleConstructorField - constructor types differ *)
Module Type ConsType1.
  Inductive I : Type := c1 : nat -> I | c2 : I.
End ConsType1.
Module ConsMod1.
  Inductive I : Type := c1 : bool -> I | c2 : I.
End ConsMod1.
Fail Module ConsTest1 : ConsType1 := ConsMod1.

(* Test 3: NotSameConstructorNamesField - constructor names differ *)
Module Type ConsNameType.
  Inductive I : Type := foo : I | bar : I.
End ConsNameType.
Module ConsNameMod.
  Inductive I : Type := baz : I | qux : I.
End ConsNameMod.
Fail Module ConsNameTest : ConsNameType := ConsNameMod.

(* Test 4: NotSameInductiveNameInBlockField - mutual inductive type names differ *)
Module Type IndNameType.
  Inductive Foo : Type := mkFoo : Bar -> Foo
  with Bar : Type := mkBar : Foo -> Bar.
End IndNameType.
Module IndNameMod.
  Inductive Foo : Type := mkFoo : Baz -> Foo
  with Baz : Type := mkBar : Foo -> Baz.
End IndNameMod.
Fail Module IndNameTest : IndNameType := IndNameMod.

(* Test 5: InductiveNumbersFieldExpected - number of inductives differs *)
Module Type NumIndType.
  Inductive I1 : Type := c1 : I1
  with I2 : Type := c2 : I2.
End NumIndType.
Module NumIndMod.
  Inductive I1 : Type := c1 : I1.
End NumIndMod.
Fail Module NumIndTest : NumIndType := NumIndMod.

(* Test 6: InductiveParams - parameter contexts differ *)
Module Type ParamsType.
  Inductive I (A B : Type) : Type := c : A -> B -> I A B.
End ParamsType.
Module ParamsMod.
  Inductive I (A : Type) : Type := c : A -> A -> I A.
End ParamsMod.
Fail Module ParamsTest : ParamsType := ParamsMod.

(* Test 7: NotConvertibleBodyField - body of definitions differs *)
Module Type BodyType.
  Definition x := 42.
End BodyType.
Module BodyMod.
  Definition x := 0.
End BodyMod.
Fail Module BodyTest : BodyType := BodyMod.

(* Test 8: NotConvertibleTypeField - type of definitions differs *)
Module Type TypeFieldType.
  Definition x : nat := 0.
End TypeFieldType.
Module TypeFieldMod.
  Definition x : bool := true.
End TypeFieldMod.
Fail Module TypeFieldTest : TypeFieldType := TypeFieldMod.

(* Test 9: With Definition type mismatch with complex types from module *)
Module Type WithParamType.
  Parameter a : Type.
  Parameter b : a.
End WithParamType.
Fail Module Type WithParamTest := WithParamType with Definition a := nat with Definition b := true.

(* Test 10: Nested with definition error - type mismatch in submodule *)
Module Type InnerType.
  Parameter x : nat.
End InnerType.
Module Type NestedWithType.
  Declare Module Inner : InnerType.
End NestedWithType.
Fail Module Type NestedWithTest := NestedWithType with Definition Inner.x := true.

(* Test 11: RecordFieldExpected - expected record but got non-record *)
Module Type RecType.
  Record R := { field : nat }.
End RecType.
Module RecMod.
  Inductive R := mkR : nat -> R.
End RecMod.
Fail Module RecTest : RecType := RecMod.

(* Test 12: RecordProjectionsExpected - projection names differ *)
Module Type RecProjType.
  Record R := { foo : nat; bar : bool }.
End RecProjType.
Module RecProjMod.
  Record R := { baz : nat; qux : bool }.
End RecProjMod.
Fail Module RecProjTest : RecProjType := RecProjMod.

(* Test 13: FiniteInductiveFieldExpected - inductive vs coinductive *)
Module Type FiniteType.
  Inductive I := c : I.
End FiniteType.
Module FiniteMod.
  CoInductive I := c : I.
End FiniteMod.
Fail Module FiniteTest : FiniteType := FiniteMod.

(* Test 14: With Definition body mismatch *)
Module Type WithBodyType.
  Definition x := 5.
End WithBodyType.
Fail Module Type WithBodyTest := WithBodyType with Definition x := 10.
