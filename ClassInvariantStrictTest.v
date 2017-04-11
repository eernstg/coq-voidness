(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import List.
Require Import ClassTestTypes.
Require Import InvariantVoidnessPreservation.

Module MyVoidnessPreservation :=
  InvariantVoidnessPreservation.VoidnessPreservationBase
    Dynamics.StrictDynamics.
Import MyVoidnessPreservation.

(* -------------------- Examples from email threads -------------------- *)

(* A<Object> x = new A<void>(); // No *)
Goal ~(TypeVoidnessPreserves dt_A_void dt_A_Object).
  intro H. inversion H; simpl in *.
  - inversion H2. inversion H5.
    + inversion H8. intuition H14.
    + inversion H8; subst.
      * inversion H14. inversion H4.
      * inversion H8. inversion H4. inversion H14. inversion H3. inversion H10.
Qed.

(* A<dynamic> x = new A<void>(); // No *)
Goal ~(TypeVoidnessPreserves dt_A_void dt_A_dynamic).
  intro H. inversion H; simpl in *.
  - inversion H2. inversion H5. 
    + inversion H8. intuition H14.
    + inversion H8. 
      * inversion H14. inversion H20. exact H23.
      * inversion H13. inversion H17.      
Qed.

(* A<Object> x = new A<dynamic>(); // Yes *)
Goal TypeVoidnessPreserves dt_A_dynamic dt_A_Object.
  unfold TypeVoidnessPreserves, dt_A_dynamic, dt_A_Object, ct_A_dynamic, ct_A_Object.
  apply vp_class. apply vctsp_cons.
  - apply vctp_some. apply vctps_first. 
    + apply vpp_cons; auto.
    + apply vpp_cons; auto. apply vp_class_0.
  - apply vctsp_cons; auto.
    apply vctp_some. apply vctps_rest. apply vctps_first; auto.
Qed.

(* A<void> x = new A<dynamic>(); // voidV = dynamicV, No *)
Goal ~(TypeVoidnessPreserves dt_A_dynamic dt_A_void).
  intro H. inversion H; simpl in *.
  - inversion H2. inversion H5.
    + inversion H8. intuition H14.
    + inversion H8.
      * inversion H16. inversion H20. exact H23. 
      * inversion H13. inversion H17.
Qed.

(* A<void> x = new A<Object>(); // voidV = objectV, No *)
Goal ~(TypeVoidnessPreserves dt_A_Object dt_A_void).
  intro H. inversion H; simpl in *.
  - inversion H2. inversion H5.
    + inversion H8. intuition H14. 
    + inversion H8. 
      * inversion H16. inversion H20.
      * inversion H13. inversion H17.
Qed.

(* dynamic x = new A<void>(); // Yes *)
Goal TypeVoidnessPreserves dt_A_void dt_dynamic.
  unfold TypeVoidnessPreserves,dt_A_void, ct_A_void. auto.
Qed.

(* Object x = new A<void>(); // Yes *)
Goal TypeVoidnessPreserves dt_A_void dt_Object.
  unfold TypeVoidnessPreserves, dt_A_void, dt_Object, ct_A_void, ct_Object.
  apply vp_class. apply vctsp_cons; auto.
  apply vctp_gone. apply vctg_cons; auto. discriminate.
Qed.

(* Iterable<void> x = new List<void>(); // Yes *)
Goal TypeVoidnessPreserves dt_List_void dt_Iterable_void.
  unfold TypeVoidnessPreserves. simpl.
  - apply vp_class. apply vctsp_cons.
    + apply vctp_gone; apply vctg_cons. discriminate.
      apply vctg_cons; auto. discriminate.
    + apply vctsp_cons.
      * apply vctp_some; auto. apply vctps_first; auto. 
      * apply vctsp_cons; auto. 
        apply vctp_some. apply vctps_rest. apply vctps_first; auto.
Qed.

(* List<void> x = new Iterable<void>(); // Yes *)
Goal TypeVoidnessPreserves dt_Iterable_void dt_List_void.
  unfold TypeVoidnessPreserves. simpl.
  - apply vp_class. apply vctsp_cons.
    + apply vctp_some. apply vctps_rest. apply vctps_first.
      * apply vpp_cons. apply vp_any_void. auto.
      * apply vpp_cons. apply vp_any_void. auto.
    + apply vctsp_cons.
      * apply vctp_some. apply vctps_rest. apply vctps_rest.
        apply vctps_first. auto. auto.
      * apply vctsp_nil.
Qed.

(* Iterable<Object> x = new List<void>(); // No *)
Goal ~(TypeVoidnessPreserves dt_List_void dt_Iterable_Object).
  unfold TypeVoidnessPreserves.
  intro H. inversion H. 
  - inversion H2. inversion H7. inversion H10. 
    + inversion H13. intuition H19.
    + inversion H13. 
      * inversion H19. inversion H25. 
      * inversion H18. inversion H22.
Qed.

(* List<Object> x = new Iterable<void>(); // No *)
Goal ~(TypeVoidnessPreserves dt_Iterable_void dt_List_Object).
  unfold TypeVoidnessPreserves.
  intro H. inversion H. 
  - inversion H2. inversion H5. 
    + inversion H8. inversion H17. intuition H21.
    + inversion H8. inversion H13. 
      * inversion H18. inversion H24.
      * inversion H17. inversion H21.
Qed.
