(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import Types.
Require Import List.
Require Export Types.

Inductive DartSubtype : DartType -> DartType -> Prop :=
| ds_void : ∀ dt, DartSubtype dt dt_void
| ds_dynamic : ∀ dt, DartSubtype dt dt_dynamic
| ds_Object : ∀ dt, DartSubtype dt (dt_class (ndts_cons (Object, dts_nil) ndts_nil))
| ds_class : ∀ ctypes1 ctypes2,
  DartSubtypesClassTypes ctypes1 ctypes2 ->
  DartSubtype (dt_class ctypes1) (dt_class ctypes2)
| ds_function : ∀ ret1 args1 ret2 args2,
  DartSubtype ret1 ret2 ->
  DartSubtypePairwise args2 args1 ->
  DartSubtype (dt_function ret1 args1) (dt_function ret2 args2)
| ds_variable : ∀ name,
  DartSubtype (dt_variable name) (dt_variable name)
| ds_bottom_any : ∀ dt, DartSubtype dt_bottom dt

with DartSubtypePairwise : DartTypes -> DartTypes -> Prop :=
| dsp_nil : DartSubtypePairwise dts_nil dts_nil
| dsp_cons : ∀ dt1 dts1 dt2 dts2,
  DartSubtype dt1 dt2 ->
  DartSubtypePairwise dts1 dts2 ->
  DartSubtypePairwise (dts_cons dt1 dts1) (dts_cons dt2 dts2)

with DartSubtypesClassTypes : NameDartTypes -> NameDartTypes -> Prop :=
| dsscts_nil : ∀ ctypes,
  DartSubtypesClassTypes ctypes ndts_nil
| dsscts_cons : ∀ ctypes1 ctype2 ctypes2,
  DartSubtypeClassTypes ctypes1 ctype2 ->
  DartSubtypesClassTypes ctypes1 ctypes2 ->
  DartSubtypesClassTypes ctypes1 (ndts_cons ctype2 ctypes2)

with DartSubtypeClassTypes : NameDartTypes -> (Name * DartTypes) -> Prop :=
| dscts_first : ∀ ctype1 ctypes1 ctype2,
  DartSubtypeClassType ctype1 ctype2 ->
  DartSubtypeClassTypes (ndts_cons ctype1 ctypes1) ctype2
| dscts_rest : ∀ ctype1 ctypes1 ctype2,
  DartSubtypeClassTypes ctypes1 ctype2 ->
  DartSubtypeClassTypes (ndts_cons ctype1 ctypes1) ctype2

with DartSubtypeClassType : (Name * DartTypes) -> (Name * DartTypes) -> Prop :=
| dsct_args: ∀ name args1 args2,
  DartSubtypePairwise args1 args2 ->
  DartSubtypeClassType (name, args1) (name, args2).

Hint Constructors
  DartSubtype DartSubtypePairwise
  DartSubtypesClassTypes DartSubtypeClassTypes DartSubtypeClassType.

Definition DartAssignable (dt1: DartType) (dt2: DartType) : Prop :=
  or (DartSubtype dt1 dt2) (DartSubtype dt2 dt1).

Hint Unfold DartAssignable.
