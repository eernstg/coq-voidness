
(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import List.
Require Import InvariantVoidnessPreservation.
Require Import FunctionTestTypes.

Module MyVoidnessPreservation :=
  InvariantVoidnessPreservation.VoidnessPreservationBase Voidness.NormalVoidness.
Import MyVoidnessPreservation.

(* void Function(void) f = func<dynamic, dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_dynamic_dynamic dt_fun_void_void.
  apply vp_function; auto.
Qed.

(* void Function(void) f = func<dynamic, void>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_dynamic_void dt_fun_void_void.
  apply vp_function; auto.
Qed.

(* void Function(void) f = func<void, dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_dynamic dt_fun_void_void.
  apply vp_function; auto.
Qed.

(* void Function(void) f = func<Object, Object>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_Object_Object dt_fun_void_void).
  intro H. inversion H.
  - inversion H0.
  - inversion H5. inversion H9. inversion H12.
Qed.

(* void Function(void) f = func<Object, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_Object_void dt_fun_void_void).
  intro H. inversion H.
  - inversion H0.
  - inversion H5. inversion H9. inversion H12.
Qed.

(* void Function(void) f = func<void, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_Object dt_fun_void_void.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic) g = func<void, void>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_void dt_fun_dynamic_dynamic.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic) g = func<dynamic, void>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_dynamic_void dt_fun_dynamic_dynamic.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic) g = func<void, dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_dynamic dt_fun_dynamic_dynamic.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic) g = func<Object, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_Object_Object dt_fun_dynamic_dynamic.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic) g = func<Object, void>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_Object_void dt_fun_dynamic_dynamic.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic) g = func<void, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_Object dt_fun_dynamic_dynamic.
  apply vp_function; auto.
Qed.

(* Object Function(Object) h = func<void, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_void_void dt_fun_Object_Object).
  intro H. inversion H.
  - inversion H0.
  - inversion H3. inversion H6.
Qed.

(* Object Function(Object) h = func<dynamic, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_dynamic_void dt_fun_Object_Object).
  intro H. inversion H.
  - inversion H0.
  - inversion H3. inversion H6.
Qed.

(* Object Function(Object) h = func<void, dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_dynamic dt_fun_Object_Object.
  apply vp_function; auto.
Qed.

(* Object Function(Object) h = func<Object, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_Object_Object dt_fun_Object_Object.
  apply vp_function.
  - apply vp_class. apply vctsp_cons; auto.
    apply vctp_some. apply vctps_first; auto.
  - apply vpp_cons; auto. apply vp_class. apply vctsp_cons; auto.
    apply vctp_some. apply vctps_first; auto.
Qed.

(* Object Function(Object) h = func<Object, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_Object_void dt_fun_Object_Object).
  intro H. inversion H.
  - inversion H0.
  - inversion H3. inversion H6.
Qed.

(* Object Function(Object) h = func<void, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_Object dt_fun_Object_Object.
  apply vp_function; auto.
  apply vp_class. apply vctsp_cons; auto.
  apply vctp_some. apply vctps_first; auto.
Qed.

(* Object Function(void) h = func<Object, Object>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_Object_Object dt_fun_void_Object).
  intro H. inversion H.
  - inversion H0.
  - inversion H5. inversion H9. inversion H12.
Qed.

(* dynamic Function(void Function(void)) f = func<dynamic Function(dynamic), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_dynamic_dynamic dt_fun2_void_void.
  apply vp_function; auto.
  apply vpp_cons; auto.
  apply vp_function; auto.
Qed.

(* dynamic Function(void Function(void)) f = func<Object Function(dynamic), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_dynamic_Object dt_fun2_void_void).
  intro H. inversion H.
  - inversion H0.
  - inversion H5. inversion H9. inversion H12.
    inversion H15. inversion H18.
Qed.

(* dynamic Function(void Function(void)) f = func<dynamic Function(Object), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_Object_dynamic dt_fun2_void_void.
  apply vp_function; auto.
  apply vpp_cons; auto.
  apply vp_function; auto.
Qed.

(* dynamic Function(void Function(void)) f = func<Object Function(Object), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_Object_Object dt_fun2_void_void).
  intro H. inversion H.
  - inversion H0.
  - inversion H5. inversion H9. inversion H12.
    inversion H15. inversion H18.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<void Function(void), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_void_void dt_fun2_dynamic_dynamic.
  apply vp_function; auto.
  apply vpp_cons; auto.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<Object Function(void), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_void_Object dt_fun2_dynamic_dynamic.
  apply vp_function; auto.
  apply vpp_cons; auto.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<void Function(Object), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_Object_void dt_fun2_dynamic_dynamic.
  apply vp_function; auto.
  apply vpp_cons; auto.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<Object Function(Object), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_Object_Object dt_fun2_dynamic_dynamic.
  apply vp_function; auto.
  apply vpp_cons; auto.
  apply vp_function; auto.
Qed.

(* dynamic Function(Object Function(Object)) f = func<void Function(void), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_void_void dt_fun2_Object_Object).
  intro H. inversion H.
  - inversion H0.
  - inversion H5. inversion H9. inversion H12.
    inversion H17. inversion H21. inversion H24. 
Qed.

(* dynamic Function(Object Function(Object)) f = func<dynamic Function(void), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_void_dynamic dt_fun2_Object_Object).
  intro H. inversion H.
  - inversion H0.
  - inversion H5. inversion H9. inversion H12.
    inversion H17. inversion H21. inversion H24.
Qed.

(* dynamic Function(Object Function(Object)) f = func<void Function(dynamic), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_dynamic_void dt_fun2_Object_Object.
  apply vp_function; auto.
  apply vpp_cons; auto.
  apply vp_function; auto.
Qed.

(* dynamic Function(Object Function(Object)) f = func<dynamic Function(dynamic), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_dynamic_dynamic dt_fun2_Object_Object.
  apply vp_function; auto.
  apply vpp_cons; auto.
  apply vp_function; auto.
Qed.
