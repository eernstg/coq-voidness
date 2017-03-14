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

  Inductive VoidnessPreserves : VoidnessType -> VoidnessType -> Prop :=
  | vp_0_any : ∀ vt, VoidnessPreserves vt_0 vt
  | vp_any_1 : ∀ vt, VoidnessPreserves vt vt_1
  | vp_class : ∀ ctypes1 ctypes2,
    VoidnessClassTypesPreserve ctypes1 ctypes2 ->
    VoidnessPreserves (vt_class ctypes1) (vt_class ctypes2)
  | vp_class_0 : ∀ ctypes,
    VoidnessPreserves (vt_class ctypes) vt_0
  | vp_function : ∀ ret1 ret2 args1 args2,
    VoidnessPreserves ret1 ret2 ->
    VoidnessPreservesPairwise args2 args1 ->
    VoidnessPreserves (vt_function ret1 args1) (vt_function ret2 args2)
  | vp_function_0 : ∀ ret args,
    VoidnessPreserves (vt_function ret args) vt_0

  with VoidnessPreservesPairwise : list VoidnessType -> list VoidnessType -> Prop :=
  | vpp_nil : VoidnessPreservesPairwise nil nil
  | vpp_cons : ∀ vt1 vt2 vts1 vts2,
    VoidnessPreserves vt1 vt2 ->
    VoidnessPreservesPairwise vts1 vts2 ->
    VoidnessPreservesPairwise (vt1 :: vts1) (vt2 :: vts2)

  with VoidnessClassTypesPreserve : VoidnessClassTypes -> VoidnessClassTypes -> Prop :=
  | vctsp_nil : ∀ ctypes,
    VoidnessClassTypesPreserve nil ctypes
  | vctsp_cons : ∀ ctype1 ctypes1 ctypes2,
    VoidnessClassTypePreserves ctype1 ctypes2 ->
    VoidnessClassTypesPreserve ctypes1 ctypes2 ->
    VoidnessClassTypesPreserve (ctype1 :: ctypes1) ctypes2

  with VoidnessClassTypePreserves : VoidnessClassType -> VoidnessClassTypes -> Prop :=
  | vctp_gone : ∀ ctype ctypes,
    VoidnessClassTypeGone ctype ctypes ->
    VoidnessClassTypePreserves ctype ctypes
  | vctp_some : ∀ ctype ctypes,
    VoidnessClassTypePreservesSome ctype ctypes ->
    VoidnessClassTypePreserves ctype ctypes

  with VoidnessClassTypeGone : VoidnessClassType -> VoidnessClassTypes -> Prop :=
  | vctg_nil : ∀ ctype,
    VoidnessClassTypeGone ctype nil
  | vctg_cons : ∀ name1 args1 name2 args2 ctypes,
    name1 <> name2 ->
    VoidnessClassTypeGone (name1, args1) ctypes ->
    VoidnessClassTypeGone (name1, args1) ((name2, args2) :: ctypes)

  with VoidnessClassTypePreservesSome : VoidnessClassType -> VoidnessClassTypes -> Prop :=
  | vctps_first : ∀ name args1 args2 ctypes,
    VoidnessPreservesPairwise args1 args2 ->
    VoidnessClassTypePreservesSome (name, args1) ((name, args2) :: ctypes)
  | vctps_rest : ∀ ctype1 ctype2 ctypes2,
    VoidnessClassTypePreservesSome ctype1 ctypes2 ->
    VoidnessClassTypePreservesSome ctype1 (ctype2 :: ctypes2).

  Hint Constructors
    VoidnessPreserves VoidnessPreservesPairwise
    VoidnessClassTypesPreserve VoidnessClassTypePreserves
    VoidnessClassTypeGone VoidnessClassTypePreservesSome.

  Definition TypeVoidnessPreserves (dt1: DartType) (dt2: DartType) : Prop :=
    VoidnessPreserves (voidness dt1) (annotationVoidness dt2).

  Hint Unfold TypeVoidnessPreserves.

End VoidnessPreservationBase.
