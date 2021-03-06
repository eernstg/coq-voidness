(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import VoidnessPreservation.
Require Import FunctionTestTypes.

Module MyVoidnessPreservation :=
  VoidnessPreservation.VoidnessPreservationBase Dynamics.StrictDynamics.
Import MyVoidnessPreservation.

(* void Function(void) f = func<dynamic, dynamic>; // No *)
Goal ~(VoidnessPreserves dt_fun_dynamic_dynamic dt_fun_void_void).
  intro H. inversion H. inversion H5. inversion H9. exact H12.
Qed.

(* void Function(void) f = func<dynamic, void>; // No *)
Goal ~(VoidnessPreserves dt_fun_dynamic_void dt_fun_void_void).
  intro H. inversion H. inversion H5. inversion H9. exact H12.
Qed.

(* void Function(void) f = func<void, dynamic>; // Yes *)
Goal VoidnessPreserves dt_fun_void_dynamic dt_fun_void_void.
  apply vp_function; auto.
Qed.

(* void Function(void) f = func<Object, Object>; // No *)
Goal ~(VoidnessPreserves dt_fun_Object_Object dt_fun_void_void).
  intro H. inversion H. inversion H5. inversion H9.
Qed.

(* void Function(void) f = func<Object, void>; // No *)
Goal ~(VoidnessPreserves dt_fun_Object_void dt_fun_void_void).
  intro H. inversion H. inversion H5. inversion H9.
Qed.

(* void Function(void) f = func<void, Object>; // Yes *)
Goal VoidnessPreserves dt_fun_void_Object dt_fun_void_void.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic) g = func<void, void>; // No *)
Goal ~(VoidnessPreserves dt_fun_void_void dt_fun_dynamic_dynamic).
  intro H. inversion H. inversion H3. exact H6.
Qed.

(* dynamic Function(dynamic) g = func<dynamic, void>; // No *)
Goal ~(VoidnessPreserves dt_fun_dynamic_void dt_fun_dynamic_dynamic).
  intro H. inversion H. inversion H3. exact H6.
Qed.

(* dynamic Function(dynamic) g = func<void, dynamic>; // Yes *)
Goal VoidnessPreserves dt_fun_void_dynamic dt_fun_dynamic_dynamic.
  apply vp_function; auto.
Qed.

(* dynamic Function(dynamic) g = func<Object, Object>; // Yes *)
Goal VoidnessPreserves dt_fun_Object_Object dt_fun_dynamic_dynamic.
  apply vp_function; auto.
  apply vp_class_dynamic.
Qed.

(* dynamic Function(dynamic) g = func<Object, void>; // No *)
Goal ~(VoidnessPreserves dt_fun_Object_void dt_fun_dynamic_dynamic).
  intro H. inversion H. inversion H3. exact H6.
Qed.

(* dynamic Function(dynamic) g = func<void, Object>; // Yes *)
Goal VoidnessPreserves dt_fun_void_Object dt_fun_dynamic_dynamic.
  apply vp_function; auto.
  apply vp_class_dynamic.
Qed.

(* Object Function(Object) h = func<void, void>; // No *)
Goal ~(VoidnessPreserves dt_fun_void_void dt_fun_Object_Object).
  intro H. inversion H. inversion H3.
Qed.

(* Object Function(Object) h = func<dynamic, void>; // No *)
Goal ~(VoidnessPreserves dt_fun_dynamic_void dt_fun_Object_Object).
  intro H. inversion H. inversion H3.
Qed.

(* Object Function(Object) h = func<void, dynamic>; // Yes *)
Goal VoidnessPreserves dt_fun_void_dynamic dt_fun_Object_Object.
  apply vp_function; auto.
Qed.

(* Object Function(Object) h = func<Object, Object>; // Yes *)
Goal VoidnessPreserves dt_fun_Object_Object dt_fun_Object_Object.
  apply vp_function; auto.
  - apply vp_class. apply vctsp_cons.
    + apply vctp_some. apply vctps_first. auto.
    + auto.
  - apply vpp_cons. 
    + apply vp_class. apply vctsp_cons.
      * apply vctp_some. apply vctps_first. auto.
      * auto.
    + auto.
Qed.

(* Object Function(Object) h = func<Object, void>; // No *)
Goal ~(VoidnessPreserves dt_fun_Object_void dt_fun_Object_Object).
  intro H. inversion H. inversion H3.
Qed.

(* Object Function(Object) h = func<void, Object>; // Yes *)
Goal VoidnessPreserves dt_fun_void_Object dt_fun_Object_Object.
  apply vp_function; auto.
  apply vp_class. apply vctsp_cons. 
  - apply vctp_some. apply vctps_first. auto.
  - auto.
Qed.

(* Object Function(void) h = func<Object, Object>; // No *)
Goal ~(VoidnessPreserves dt_fun_Object_Object dt_fun_void_Object).
  intro H. inversion H. inversion H5. inversion H9.
Qed.

(* dynamic Function(void Function(void)) f = func<dynamic Function(dynamic), dynamic>; // No *)
Goal ~(VoidnessPreserves dt_fun2_dynamic_dynamic dt_fun2_void_void).
  intro H. inversion H. inversion H5. inversion H9. inversion H15. exact H18.
Qed.

(* dynamic Function(void Function(void)) f = func<Object Function(dynamic), dynamic>; // No *)
Goal ~(VoidnessPreserves dt_fun2_dynamic_Object dt_fun2_void_void).
  intro H. inversion H. inversion H5. inversion H9. inversion H15.
Qed.

(* dynamic Function(void Function(void)) f = func<dynamic Function(Object), dynamic>; // No *)
Goal ~(VoidnessPreserves dt_fun2_Object_dynamic dt_fun2_void_void).
  intro H. inversion H. inversion H5. inversion H9. inversion H15. exact H18.
Qed.

(* dynamic Function(void Function(void)) f = func<Object Function(Object), dynamic>; // No *)
Goal ~(VoidnessPreserves dt_fun2_Object_Object dt_fun2_void_void).
  intro H. inversion H. inversion H5. inversion H9. inversion H15.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<void Function(void), dynamic>; // No *)
Goal ~(VoidnessPreserves dt_fun2_void_void dt_fun2_dynamic_dynamic).
  intro H. inversion H. inversion H5. inversion H9. 
  inversion H17. inversion H21. exact H24.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<Object Function(void), dynamic>; // No *)
Goal ~(VoidnessPreserves dt_fun2_void_Object dt_fun2_dynamic_dynamic).
  intro H. inversion H. inversion H5. inversion H9. 
  inversion H17. inversion H21. exact H24.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<void Function(Object), dynamic>; // Yes *)
Goal VoidnessPreserves dt_fun2_Object_void dt_fun2_dynamic_dynamic.
  apply vp_function; auto. apply vpp_cons.
  - apply vp_function; auto. apply vpp_cons.
    + apply vp_class_dynamic. 
    + auto.
  - auto.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<Object Function(Object), dynamic>; // Yes *)
Goal VoidnessPreserves dt_fun2_Object_Object dt_fun2_dynamic_dynamic.
  apply vp_function; auto. 
  apply vpp_cons.
  - apply vp_function; auto. apply vpp_cons. 
    + apply vp_class_dynamic.
    + auto.
  - auto.
Qed.

(* dynamic Function(Object Function(Object)) f = func<void Function(void), dynamic>; // No *)
Goal ~(VoidnessPreserves dt_fun2_void_void dt_fun2_Object_Object).
  unfold not. intros. inversion H. inversion H5. 
  inversion H9. inversion H17. inversion H21.
Qed.

(* dynamic Function(Object Function(Object)) f = func<dynamic Function(void), dynamic>; // No *)
Goal ~(VoidnessPreserves dt_fun2_void_dynamic dt_fun2_Object_Object).
  unfold not. intros. inversion H. inversion H5. 
  inversion H9. inversion H17. inversion H21.
Qed.

(* dynamic Function(Object Function(Object)) f = func<void Function(dynamic), dynamic>; // Yes *)
Goal VoidnessPreserves dt_fun2_dynamic_void dt_fun2_Object_Object.
  apply vp_function; auto. 
  apply vpp_cons; auto. 
  apply vp_function; auto.     
Qed.

(* dynamic Function(Object Function(Object)) f = func<dynamic Function(dynamic), dynamic>; // Yes *)
Goal VoidnessPreserves dt_fun2_dynamic_dynamic dt_fun2_Object_Object.
  apply vp_function; auto. 
  apply vpp_cons; auto. 
  apply vp_function; auto.
  apply vp_class_dynamic.
Qed.
