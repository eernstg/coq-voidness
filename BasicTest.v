(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import ClassTestTypes.
Require Import VoidnessPreservation.

(* Works with multiple parameters, with no changes: Uncomment one of them. *)
Module MyDynamics :=
  Dynamics.NormalDynamics.

Module MyVoidnessPreservation :=
  VoidnessPreservation.VoidnessPreservationBase MyDynamics.
Import MyVoidnessPreservation.

(* ---------- Voidness Types ---------- *)

(* B<A<1>, Object> *)
Definition ct_B_A1_Object :=
  ndts_cons (B, dts_cons dt_A_void (dts_cons dt_Object dts_nil)) ct_Object.
Definition dt_B_A1_Object := dt_class ct_B_A1_Object.

(* B<Object, Object> *)
Definition ct_B_ObjectObject :=
  ndts_cons (B, dts_cons dt_Object (dts_cons dt_Object dts_nil)) ct_Object.
Definition dt_B_ObjectObject := dt_class ct_B_ObjectObject.

(* A<A<void>> *)
Definition ct_A_A_void := 
  ndts_cons (A, dts_cons dt_A_void dts_nil) ct_Object.
Definition dt_A_A_void := dt_class ct_A_A_void.

Hint Unfold
  ct_Object dt_Object ct_A_Object dt_A_Object ct_A_void dt_A_void
  ct_A_dynamic dt_A_dynamic ct_Iterable_Object dt_Iterable_Object
  ct_Iterable_void dt_Iterable_void ct_List_Object dt_List_Object
  ct_List_void dt_List_void ct_A_A_void dt_A_A_void
  ct_B_A1_Object dt_B_A1_Object ct_B_ObjectObject dt_B_ObjectObject.

(* ---------- Trying out existing examples ---------- *)

(* dynamic <:: dynamic *)
Goal VoidnessPreserves dt_dynamic dt_dynamic.
 auto.
Qed.

(* dynamic <:: void *)
Goal VoidnessPreserves dt_dynamic dt_void.
  auto.
Qed.

(* dynamic <:: variable n *)
Goal forall n, VoidnessPreserves dt_dynamic (dt_variable n).
  auto.
Qed.

(* A<Object> <:: A<void> *)
Goal VoidnessPreserves dt_A_Object dt_A_void.
  apply vp_class; apply vctsp_cons.
    apply vctp_some; apply vctps_first; auto.
  apply vctsp_cons; auto.
  apply vctp_some. apply vctps_rest. apply vctps_first. auto.
Qed.

(* A<A<void>> <:: A<void> *)
Goal VoidnessPreserves dt_A_A_void dt_A_void.
  apply vp_class; apply vctsp_cons; auto.
    apply vctp_some. apply vctps_first. apply vpp_cons; auto.
  apply vctsp_cons; auto. apply vctp_some. apply vctps_rest. apply vctps_first. auto.
Qed.

(* Not A<void> <:: A<Object> *)
Goal ~(VoidnessPreserves dt_A_void dt_A_Object).
  unfold not. intro H. inversion H. inversion H2. inversion H5.
    inversion H8. apply H14. reflexivity.
  inversion H8.
    inversion H12. inversion H19.
  inversion H13. inversion H17.
Qed.
