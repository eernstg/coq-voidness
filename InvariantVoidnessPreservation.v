(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import Types.
Require Import Voidness.
Require Import List.
Require Export Types.
Require Export Voidness.

Module VoidnessPreservationBase (Import MyVoidness : VoidnessSig).

  Inductive VoidnessPreserves : DartType -> DartType -> Prop :=
  | vp_0_any : ∀ dt1 dt2,
    voidness dt1 = vt_0 ->
    VoidnessPreserves dt1 dt2
  | vp_any_1 : ∀ dt1 dt2,
    annotationVoidness dt2 = vt_1 ->
    VoidnessPreserves dt1 dt2
  | vp_class : ∀ dtypes1 dtypes2,
    VoidnessClassTypesPreserve dtypes1 dtypes2 ->
    VoidnessPreserves (dt_class dtypes1) (dt_class dtypes2)
  | vp_class_0 : ∀ dtypes dt,
    annotationVoidness dt = vt_0 ->
    VoidnessPreserves (dt_class dtypes) dt
  | vp_function : ∀ ret1 ret2 args1 args2,
    VoidnessPreserves ret1 ret2 ->
    VoidnessPreservesPairwise args2 args1 ->
    VoidnessPreserves (dt_function ret1 args1) (dt_function ret2 args2)
  | vp_function_0 : ∀ ret args dt,
    annotationVoidness dt = vt_0 ->
    VoidnessPreserves (dt_function ret args) dt

  with VoidnessPreservesPairwise : list DartType -> list DartType -> Prop :=
  | vpp_nil : VoidnessPreservesPairwise nil nil
  | vpp_cons : ∀ dt1 dt2 dts1 dts2,
    VoidnessPreserves dt1 dt2 ->
    VoidnessPreservesPairwise dts1 dts2 ->
    VoidnessPreservesPairwise (dt1 :: dts1) (dt2 :: dts2)

  with VoidnessClassTypesPreserve : ClassTypes -> ClassTypes -> Prop :=
  | vctsp_nil : ∀ ctypes,
    VoidnessClassTypesPreserve nil ctypes
  | vctsp_cons : ∀ ctype1 ctypes1 ctypes2,
    VoidnessClassTypePreserves ctype1 ctypes2 ->
    VoidnessClassTypesPreserve ctypes1 ctypes2 ->
    VoidnessClassTypesPreserve (ctype1 :: ctypes1) ctypes2

  with VoidnessClassTypePreserves : ClassType -> ClassTypes -> Prop :=
  | vctp_gone : ∀ ctype ctypes,
    VoidnessClassTypeGone ctype ctypes ->
    VoidnessClassTypePreserves ctype ctypes
  | vctp_some : ∀ ctype ctypes,
    VoidnessClassTypePreservesSome ctype ctypes ->
    VoidnessClassTypePreserves ctype ctypes

  with VoidnessClassTypeGone : ClassType -> ClassTypes -> Prop :=
  | vctg_nil : ∀ ctype,
    VoidnessClassTypeGone ctype nil
  | vctg_cons : ∀ name1 args1 name2 args2 ctypes,
    name1 <> name2 ->
    VoidnessClassTypeGone (name1, args1) ctypes ->
    VoidnessClassTypeGone (name1, args1) ((name2, args2) :: ctypes)

  with VoidnessClassTypePreservesSome : ClassType -> ClassTypes -> Prop :=
  | vctps_first : ∀ name args1 args2 ctypes,
    VoidnessPreservesPairwise args1 args2 ->
    VoidnessPreservesPairwise args2 args1 ->
    VoidnessClassTypePreservesSome (name, args1) ((name, args2) :: ctypes)
  | vctps_rest : ∀ ctype1 ctype2 ctypes2,
    VoidnessClassTypePreservesSome ctype1 ctypes2 ->
    VoidnessClassTypePreservesSome ctype1 (ctype2 :: ctypes2).

  Hint Constructors
    VoidnessPreserves VoidnessPreservesPairwise
    VoidnessClassTypesPreserve VoidnessClassTypePreserves
    VoidnessClassTypeGone VoidnessClassTypePreservesSome.

  Definition TypeVoidnessPreserves := VoidnessPreserves.

  Hint Unfold TypeVoidnessPreserves.

End VoidnessPreservationBase.
