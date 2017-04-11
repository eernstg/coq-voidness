(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import List.
Require Import Types.
Require Import Dynamics.

Require Export Types.
Require Export Dynamics.

Module VoidnessPreservationBase (MyDynamics : DynamicsSig).

  Inductive VoidnessPreserves : DartType -> DartType -> Prop :=
  | vp_dynamic_any : ∀ dt,
    VoidnessPreserves dt_dynamic dt
  | vp_any_void : ∀ dt,
    VoidnessPreserves dt dt_void
  | vp_any_variable : ∀ dt n,
    VoidnessPreserves dt (dt_variable n)
  | vp_any_dynamic : ∀ dt,
    MyDynamics.dynamic_is_magic ->
    VoidnessPreserves dt dt_dynamic
  | vp_class : ∀ dtypes1 dtypes2,
    VoidnessClassTypesPreserve dtypes1 dtypes2 ->
    VoidnessPreserves (dt_class dtypes1) (dt_class dtypes2)
  | vp_class_dynamic : ∀ dtypes,
    VoidnessPreserves (dt_class dtypes) dt_dynamic
  | vp_function : ∀ ret1 ret2 args1 args2,
    VoidnessPreserves ret1 ret2 ->
    VoidnessPreservesPairwise args2 args1 ->
    VoidnessPreserves (dt_function ret1 args1) (dt_function ret2 args2)
  | vp_function_dynamic : ∀ ret args,
    VoidnessPreserves (dt_function ret args) dt_dynamic

  with VoidnessPreservesPairwise : DartTypes -> DartTypes -> Prop :=
  | vpp_nil : VoidnessPreservesPairwise dts_nil dts_nil
  | vpp_cons : ∀ dt1 dt2 dts1 dts2,
    VoidnessPreserves dt1 dt2 ->
    VoidnessPreservesPairwise dts1 dts2 ->
    VoidnessPreservesPairwise (dts_cons dt1 dts1) (dts_cons dt2 dts2)

  with VoidnessClassTypesPreserve : NameDartTypes -> NameDartTypes -> Prop :=
  | vctsp_nil : ∀ ctypes,
    VoidnessClassTypesPreserve ndts_nil ctypes
  | vctsp_cons : ∀ ctype1 ctypes1 ctypes2,
    VoidnessClassTypePreserves ctype1 ctypes2 ->
    VoidnessClassTypesPreserve ctypes1 ctypes2 ->
    VoidnessClassTypesPreserve (ndts_cons ctype1 ctypes1) ctypes2

  with VoidnessClassTypePreserves : (Name * DartTypes) -> NameDartTypes -> Prop :=
  | vctp_gone : ∀ ctype ctypes,
    VoidnessClassTypeGone ctype ctypes ->
    VoidnessClassTypePreserves ctype ctypes
  | vctp_some : ∀ ctype ctypes,
    VoidnessClassTypePreservesSome ctype ctypes ->
    VoidnessClassTypePreserves ctype ctypes

  with VoidnessClassTypeGone : (Name * DartTypes) -> NameDartTypes -> Prop :=
  | vctg_nil : ∀ ctype,
    VoidnessClassTypeGone ctype ndts_nil
  | vctg_cons : ∀ name1 args1 name2 args2 ctypes,
    name1 <> name2 ->
    VoidnessClassTypeGone (name1, args1) ctypes ->
    VoidnessClassTypeGone (name1, args1) (ndts_cons (name2, args2) ctypes)

  with VoidnessClassTypePreservesSome : (Name * DartTypes) -> NameDartTypes -> Prop :=
  | vctps_first : ∀ name args1 args2 ctypes,
    VoidnessPreservesPairwise args1 args2 ->
    VoidnessPreservesPairwise args2 args1 ->
    VoidnessClassTypePreservesSome (name, args1) (ndts_cons (name, args2) ctypes)
  | vctps_rest : ∀ ctype1 ctype2 ctypes2,
    VoidnessClassTypePreservesSome ctype1 ctypes2 ->
    VoidnessClassTypePreservesSome ctype1 (ndts_cons ctype2 ctypes2).

  Hint Constructors
    VoidnessPreserves VoidnessPreservesPairwise
    VoidnessClassTypesPreserve VoidnessClassTypePreserves
    VoidnessClassTypeGone VoidnessClassTypePreservesSome.

End VoidnessPreservationBase.
