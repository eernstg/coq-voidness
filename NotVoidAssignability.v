Require Import Utf8.
Require Import Types.
Require Import Subtypes.
Require Import List.
Require Export Types.
Require Export Subtypes.

Inductive isNotVariableNamed : Name -> DartType -> Prop :=
| invn_void : ∀ name,
  isNotVariableNamed name dt_void
| invn_dynamic : ∀ name,
  isNotVariableNamed name dt_dynamic
| invn_class : ∀ name ctypes,
  isNotVariableNamed name (dt_class ctypes)
| insn_variable : ∀ name1 name2,
  name1 <> name2 ->
  isNotVariableNamed name1 (dt_variable name2).

Hint Constructors isNotVariableNamed.

Inductive ClassTypeNamed : Name -> ClassTypes -> ClassType -> Prop :=
| ctn_first : ∀ name args ctypes,
  ClassTypeNamed name ((name, args) :: ctypes) (name, args)
| ctn_rest : ∀ name1 ctype ctypes name2 args2,
  name1 <> name2 ->
  ClassTypeNamed name1 ctypes ctype ->
  ClassTypeNamed name1 ((name2, args2) :: ctypes) ctype.

Hint Constructors ClassTypeNamed.

(* NotVoidAssignable typeOfSource typeAnnotationOfTarget: `Target x = source;` will cause a loss of voidness *)
Inductive NotVoidAssignable : DartType -> DartType -> Prop :=
| nva_base : ∀ T,
  T <> dt_void ->
  T <> dt_dynamic ->
  NotVoidAssignable dt_void T
| nva_class : ∀ ctypes1 ctypes2,
  NotVoidAssignableClassTypes ctypes1 ctypes2 ->
  NotVoidAssignable (dt_class ctypes1) (dt_class ctypes2)
| nva_function_ret : ∀ ret1 args1 ret2 args2,
  DartAssignable (dt_function ret1 args1) (dt_function ret2 args2) ->
  NotVoidAssignable ret1 ret2 ->
  NotVoidAssignable (dt_function ret1 args1) (dt_function ret2 args2)
| nva_function_arg : ∀ ret1 args1 ret2 args2,
  DartAssignable (dt_function ret1 args1) (dt_function ret2 args2) ->
  NotVoidAssignablePairwise args2 args1 ->
  NotVoidAssignable (dt_function ret1 args1) (dt_function ret2 args2)
| nva_variable : ∀ name dt,
  isNotVariableNamed name dt ->
  NotVoidAssignable (dt_variable name) dt

(* NotVoidAssignablePairwise types1 types2: At least one pair (type1, type2) causes a loss of voidness *)
with NotVoidAssignablePairwise : list DartType -> list DartType -> Prop :=
| nvap_cons_first : ∀ dt1 dts1 dt2 dts2,
  NotVoidAssignable dt1 dt2 ->
  NotVoidAssignablePairwise (dt1 :: dts1) (dt2 :: dts2)
| nvap_cons_rest : ∀ dt1 dts1 dt2 dts2,
  NotVoidAssignablePairwise dts1 dts2 ->
  NotVoidAssignablePairwise (dt1 :: dts1) (dt2 :: dts2)

(* NotVoidAssignableClassTypes classTypes1 classTypes2: `"dt_class classTypes2" x = "dt_class classTypes1"-expression` causes loss of voidness *)
with NotVoidAssignableClassTypes : ClassTypes -> ClassTypes -> Prop :=
| nvact_upcast : ∀ name args1 ctypes1 args2 ctypes2,
  DartSubtypesClassTypes ctypes1 ((name, args2) :: ctypes2) -> (* This is an upcast, to (name, args2) :: ctypes2 *)
  ClassTypeNamed name ctypes1 (name, args1) -> (* In ctypes1, the type named name is (name, args1) *)
  NotVoidAssignablePairwise args1 args2 -> (* At least one type argument is not-void-assignable *)
  NotVoidAssignableClassTypes ctypes1 ((name, args2) :: ctypes2)
| nvact_downcast : ∀ name args1 ctypes1 args2 ctypes2,
  DartSubtypesClassTypes ctypes2 ((name, args1) :: ctypes1) -> (* This is a downcast, to ctypes2 *)
  ClassTypeNamed name ctypes2 (name, args2) -> (* In ctypes2, the type named name is (name, args2) *)
  NotVoidAssignablePairwise args1 args2 -> (* At least one type argument is not-void-assignable *)
  NotVoidAssignableClassTypes ((name, args1) :: ctypes1) ctypes2.

Hint Constructors
  NotVoidAssignable NotVoidAssignablePairwise NotVoidAssignableClassTypes.
