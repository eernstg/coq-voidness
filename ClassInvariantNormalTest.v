(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import ClassTestTypes.
Require Import InvariantVoidnessPreservation.

Module MyVoidnessPreservation :=
  InvariantVoidnessPreservation.VoidnessPreservationBase
    Dynamics.NormalDynamics.
Import MyVoidnessPreservation.

(* -------------------- Examples from email threads -------------------- *)

(* A<Object> x = new A<void>(); // No *)
Goal ~(VoidnessPreserves dt_A_void dt_A_Object).
  unfold not. intro H. inversion H. 
  - inversion H2. inversion H5. 
    + inversion H8. intuition H14.
    + inversion H8. 
      * inversion H14. inversion H20.
      * inversion H13. inversion H17.
Qed.

(* A<dynamic> x = new A<void>(); // Yes *)
Goal VoidnessPreserves dt_A_void dt_A_dynamic.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some; apply vctps_first; auto.
  - apply vctsp_cons; auto.
    apply vctp_some; apply vctps_rest; apply vctps_first; auto.
Qed.

(* A<Object> x = new A<dynamic>(); // Yes *)
Goal VoidnessPreserves dt_A_dynamic dt_A_Object.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some; apply vctps_first; auto.
  - apply vctsp_cons; auto.
    apply vctp_some. apply vctps_rest. apply vctps_first; auto. 
Qed.

(* A<void> x = new A<dynamic>(); // voidV = dynamicV, Yes *)
Goal VoidnessPreserves dt_A_dynamic dt_A_void.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some. apply vctps_first; auto.
  - apply vctsp_cons; auto.
    apply vctp_some. apply vctps_rest. apply vctps_first; auto.
Qed.

(* A<void> x = new A<Object>(); // voidV = objectV, No *)
Goal ~(VoidnessPreserves dt_A_Object dt_A_void).
  intro H. inversion H. 
  - inversion H2. inversion H5. 
    + inversion H8. intuition H14.
    + inversion H8. 
      * inversion H16. inversion H20.
      * inversion H13. inversion H17.
Qed.

(* dynamic x = new A<void>(); // Yes *)
Goal VoidnessPreserves dt_A_void dt_dynamic.
  auto.
Qed.

(* Object x = new A<void>(); // Yes *)
Goal VoidnessPreserves dt_A_void dt_Object.
  apply vp_class. apply vctsp_cons.
  - apply vctp_gone. apply vctg_cons. discriminate. apply vctg_nil.
  - apply vctsp_cons; auto.
    apply vctp_some. apply vctps_first; auto.
Qed.

(* Iterable<void> x = new List<void>(); // Yes *)
Goal VoidnessPreserves dt_List_void dt_Iterable_void.
  apply vp_class. apply vctsp_cons.
  - apply vctp_gone; apply vctg_cons. discriminate.
    apply vctg_cons. discriminate.
    auto.
  - apply vctsp_cons.
    + apply vctp_some. apply vctps_first. auto. auto.
    + apply vctsp_cons; auto. apply vctp_some. apply vctps_rest. 
      apply vctps_first; auto.
Qed.

(* List<void> x = new Iterable<void>(); // Yes *)
Goal VoidnessPreserves dt_Iterable_void dt_List_void.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some. apply vctps_rest. apply vctps_first; auto.
  - apply vctsp_cons; auto.
    apply vctp_some. apply vctps_rest. apply vctps_rest.
    apply vctps_first; auto.
Qed.

(* Iterable<Object> x = new List<void>(); // No *)
Goal ~(VoidnessPreserves dt_List_void dt_Iterable_Object).
  intro H. inversion H. 
  - inversion H2. inversion H7. inversion H10.
    + inversion H13. intuition H19.
    + inversion H13. 
      * inversion H19. inversion H25.
      * inversion H18. inversion H22.
Qed.

(* List<Object> x = new Iterable<void>(); // No *)
Goal ~(VoidnessPreserves dt_Iterable_void dt_List_Object).
  intro H. inversion H.
  - inversion H2. inversion H5.
    + inversion H8. inversion H17. intuition H21.
    + inversion H8. inversion H13.
      * inversion H18. inversion H24.
      * inversion H17. inversion H21.
Qed.
