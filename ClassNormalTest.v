(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import ClassTestTypes.
Require Import VoidnessPreservation.

Module MyVoidnessPreservation :=
  VoidnessPreservation.VoidnessPreservationBase Dynamics.NormalDynamics.
Import MyVoidnessPreservation.

(* -------------------- Examples from email threads -------------------- *)

(* A<Object> x = new A<void>(); // No *)
Goal ~(VoidnessPreserves dt_A_void dt_A_Object).
  intro H. inversion H. inversion H2. inversion H5.
  - inversion H8. intuition H14.
  - inversion H8. 
    + inversion H12. inversion H19.
    + inversion H13. inversion H17.
Qed.

(* A<dynamic> x = new A<void>(); // Yes *)
Goal VoidnessPreserves dt_A_void dt_A_dynamic.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some. apply vctps_first. auto. 
  - apply vctsp_cons.
    + apply vctp_some. apply vctps_rest. apply vctps_first. auto.
    + auto.
Qed.

(* A<Object> x = new A<dynamic>(); // Yes *)
Goal VoidnessPreserves dt_A_dynamic dt_A_Object.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some. apply vctps_first. auto. 
  - apply vctsp_cons.
    + apply vctp_some. apply vctps_rest. apply vctps_first. auto.
    + auto.
Qed.

(* A<void> x = new A<dynamic>(); // voidV = dynamicV, Yes *)
Goal VoidnessPreserves dt_A_dynamic dt_A_void.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some. apply vctps_first. auto. 
  - apply vctsp_cons.
    + apply vctp_some. apply vctps_rest. apply vctps_first. auto.
    + auto.
Qed.

(* A<void> x = new A<Object>(); // voidV = objectV, Yes *)
Goal VoidnessPreserves dt_A_Object dt_A_void.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some. apply vctps_first. auto. 
  - apply vctsp_cons.
    + apply vctp_some. apply vctps_rest. apply vctps_first. auto.
    + auto.
Qed.

(* dynamic x = new A<void>(); // Yes *)
Goal VoidnessPreserves dt_A_void dt_dynamic.
  simpl. auto 7.
Qed.

(* Object x = new A<void>(); // Yes *)
Goal VoidnessPreserves dt_A_void dt_Object.
  apply vp_class. apply vctsp_cons.
  - apply vctp_gone. apply vctg_cons.
    + discriminate.
    + apply vctg_nil. 
  - apply vctsp_cons.
    + apply vctp_some. apply vctps_first. auto.
    + auto.
Qed.

(* Iterable<void> x = new List<void>(); // Yes *)
Goal VoidnessPreserves dt_List_void dt_Iterable_void.
  apply vp_class. apply vctsp_cons.
  - apply vctp_gone; apply vctg_cons.
    + discriminate.
    + apply vctg_cons.
      * discriminate.
      * auto.
  - apply vctsp_cons.
    + apply vctp_some. apply vctps_first. auto.
    + apply vctsp_cons.
      * apply vctp_some. apply vctps_rest. apply vctps_first. auto.
      * auto.
Qed.

(* List<void> x = new Iterable<void>(); // Yes *)
Goal VoidnessPreserves dt_Iterable_void dt_List_void.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some. apply vctps_rest. apply vctps_first. auto. 
  - apply vctsp_cons.
    + apply vctp_some. apply vctps_rest. apply vctps_rest.
      apply vctps_first. auto.
    + auto.
Qed.

(* Iterable<Object> x = new List<void>(); // No *)
Goal ~(VoidnessPreserves dt_List_void dt_Iterable_Object).
  intro H. inversion H.
  inversion H2. inversion H7. inversion H10.
  - inversion H13. intuition H19.
  - inversion H13. inversion H17. inversion H24. inversion H18. inversion H22.
Qed.

(* List<Object> x = new Iterable<void>(); // No *)
Goal ~(VoidnessPreserves dt_Iterable_void dt_List_Object).
  intro H. inversion H.
  inversion H2. inversion H5.
  - inversion H8. inversion H17. intuition H21.
  - inversion H8. inversion H13. 
    + inversion H16. inversion H23.
    + inversion H17. inversion H21.
Qed.
